import V185TrunkScan23Chunk0722

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4275544 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 2, 4, 2]
def baseStart_4275544 : Nat := 118140960795 + 4275544 * 2 ^ 59
def prefixEnd_4275544 : Nat := 4983230072969 + 3 ^ 40 * 4275544 * 2
def baseEnd_4275544 : Nat := 2195409131446925148137137

theorem tailTrace_4275544 : CollatzResearch.WordTrace tailWord_4275544 prefixEnd_4275544 2195409131446925148137137 := by
  unfold tailWord_4275544
  simp only [CollatzResearch.WordTrace]
  refine ⟨77970950411220883812868843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103961267214961178417158457 77970950411220883812868843)
  ·
    refine ⟨116956425616831325719303265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77970950411220883812868843 116956425616831325719303265)
    ·
      refine ⟨87717319212623494289477449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116956425616831325719303265 87717319212623494289477449)
      ·
        refine ⟨65787989409467620717108087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87717319212623494289477449 65787989409467620717108087)
        ·
          refine ⟨98681984114201431075662131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65787989409467620717108087 98681984114201431075662131)
          ·
            refine ⟨148022976171302146613493197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98681984114201431075662131 148022976171302146613493197)
            ·
              refine ⟨55508616064238304980059949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148022976171302146613493197 55508616064238304980059949)
              ·
                refine ⟨20815731024089364367522481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55508616064238304980059949 20815731024089364367522481)
                ·
                  refine ⟨15611798268067023275641861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20815731024089364367522481 15611798268067023275641861)
                  ·
                    refine ⟨2927212175262566864182849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15611798268067023275641861 2927212175262566864182849)
                    ·
                      refine ⟨2195409131446925148137137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2927212175262566864182849 2195409131446925148137137)
                      ·
                        rfl

theorem cell23_4275544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_4275544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275544 prefixEnd_4275544 := by exact prefixLift 4275544
  have htrace : WordTrace (prefixWord ++ tailWord_4275544) baseStart_4275544 baseEnd_4275544 := by
    simpa [prefixWord, tailWord_4275544, baseEnd_4275544] using wordTrace_append hprefix tailTrace_4275544
  have hstable : (prefixWord ++ tailWord_4275544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275544).length < 2 ^ (prefixWord ++ tailWord_4275544).sum := by decide
  have hdescent : baseEnd_4275544 < baseStart_4275544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275557 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 2, 4, 4]
def baseStart_4275557 : Nat := 118140960795 + 4275557 * 2 ^ 59
def prefixEnd_4275557 : Nat := 4983230072969 + 3 ^ 40 * 4275557 * 2
def baseEnd_4275557 : Nat := 2195415806695433597274577

theorem tailTrace_4275557 : CollatzResearch.WordTrace tailWord_4275557 prefixEnd_4275557 2195415806695433597274577 := by
  unfold tailWord_4275557
  simp only [CollatzResearch.WordTrace]
  refine ⟨155942374971394670845960925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103961583314263113897307283 155942374971394670845960925)
  ·
    refine ⟨58478390614273001567235347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155942374971394670845960925 58478390614273001567235347)
    ·
      refine ⟨87717585921409502350853021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58478390614273001567235347 87717585921409502350853021)
      ·
        refine ⟨32894094720528563381569883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87717585921409502350853021 32894094720528563381569883)
        ·
          refine ⟨49341142080792845072354825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32894094720528563381569883 49341142080792845072354825)
          ·
            refine ⟨37005856560594633804266119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49341142080792845072354825 37005856560594633804266119)
            ·
              refine ⟨55508784840891950706399179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37005856560594633804266119 55508784840891950706399179)
              ·
                refine ⟨83263177261337926059598769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55508784840891950706399179 83263177261337926059598769)
                ·
                  refine ⟨62447382946003444544699077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83263177261337926059598769 62447382946003444544699077)
                  ·
                    refine ⟨11708884302375645852131077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62447382946003444544699077 11708884302375645852131077)
                    ·
                      refine ⟨2195415806695433597274577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11708884302375645852131077 2195415806695433597274577)
                      ·
                        rfl

theorem cell23_4275557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_4275557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275557 prefixEnd_4275557 := by exact prefixLift 4275557
  have htrace : WordTrace (prefixWord ++ tailWord_4275557) baseStart_4275557 baseEnd_4275557 := by
    simpa [prefixWord, tailWord_4275557, baseEnd_4275557] using wordTrace_append hprefix tailTrace_4275557
  have hstable : (prefixWord ++ tailWord_4275557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275557).length < 2 ^ (prefixWord ++ tailWord_4275557).sum := by decide
  have hdescent : baseEnd_4275557 < baseStart_4275557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275564 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 3]
def baseStart_4275564 : Nat := 118140960795 + 4275564 * 2 ^ 59
def prefixEnd_4275564 : Nat := 4983230072969 + 3 ^ 40 * 4275564 * 2
def baseEnd_4275564 : Nat := 2195419401060015069887045

theorem tailTrace_4275564 : CollatzResearch.WordTrace tailWord_4275564 prefixEnd_4275564 2195419401060015069887045 := by
  unfold tailWord_4275564
  simp only [CollatzResearch.WordTrace]
  refine ⟨77971315141184655520732873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103961753521579540694310497 77971315141184655520732873)
  ·
    refine ⟨58478486355888491640549655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77971315141184655520732873 58478486355888491640549655)
    ·
      refine ⟨87717729533832737460824483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58478486355888491640549655 87717729533832737460824483)
      ·
        refine ⟨131576594300749106191236725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87717729533832737460824483 131576594300749106191236725)
        ·
          refine ⟨12335305715695228705428443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131576594300749106191236725 12335305715695228705428443)
          ·
            refine ⟨18502958573542843058142665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12335305715695228705428443 18502958573542843058142665)
            ·
              refine ⟨13877218930157132293606999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18502958573542843058142665 13877218930157132293606999)
              ·
                refine ⟨20815828395235698440410499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13877218930157132293606999 20815828395235698440410499)
                ·
                  refine ⟨31223742592853547660615749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20815828395235698440410499 31223742592853547660615749)
                  ·
                    refine ⟨5854451736160040186365453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31223742592853547660615749 5854451736160040186365453)
                    ·
                      refine ⟨2195419401060015069887045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5854451736160040186365453 2195419401060015069887045)
                      ·
                        rfl

theorem cell23_4275564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_4275564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275564 prefixEnd_4275564 := by exact prefixLift 4275564
  have htrace : WordTrace (prefixWord ++ tailWord_4275564) baseStart_4275564 baseEnd_4275564 := by
    simpa [prefixWord, tailWord_4275564, baseEnd_4275564] using wordTrace_append hprefix tailTrace_4275564
  have hstable : (prefixWord ++ tailWord_4275564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275564).length < 2 ^ (prefixWord ++ tailWord_4275564).sum := by decide
  have hdescent : baseEnd_4275564 < baseStart_4275564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275647 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 6]
def baseStart_4275647 : Nat := 118140960795 + 4275647 * 2 ^ 59
def prefixEnd_4275647 : Nat := 4983230072969 + 3 ^ 40 * 4275647 * 2
def baseEnd_4275647 : Nat := 2195462019954338245149163

theorem tailTrace_4275647 : CollatzResearch.WordTrace tailWord_4275647 prefixEnd_4275647 2195462019954338245149163 := by
  unfold tailWord_4275647
  simp only [CollatzResearch.WordTrace]
  refine ⟨155945657541068616216737195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103963771694045744144491463 155945657541068616216737195)
  ·
    refine ⟨233918486311602924325105793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155945657541068616216737195 233918486311602924325105793)
    ·
      refine ⟨175438864733702193243829345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233918486311602924325105793 175438864733702193243829345)
      ·
        refine ⟨131579148550276644932872009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175438864733702193243829345 131579148550276644932872009)
        ·
          refine ⟨98684361412707483699654007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131579148550276644932872009 98684361412707483699654007)
          ·
            refine ⟨148026542119061225549481011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98684361412707483699654007 148026542119061225549481011)
            ·
              refine ⟨222039813178591838324221517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148026542119061225549481011 222039813178591838324221517)
              ·
                refine ⟨83264929941971939371583069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222039813178591838324221517 83264929941971939371583069)
                ·
                  refine ⟨31224348728239477264343651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83264929941971939371583069 31224348728239477264343651)
                  ·
                    refine ⟨46836523092359215896515477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31224348728239477264343651 46836523092359215896515477)
                    ·
                      refine ⟨2195462019954338245149163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46836523092359215896515477 2195462019954338245149163)
                      ·
                        rfl

theorem cell23_4275647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_4275647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275647 prefixEnd_4275647 := by exact prefixLift 4275647
  have htrace : WordTrace (prefixWord ++ tailWord_4275647) baseStart_4275647 baseEnd_4275647 := by
    simpa [prefixWord, tailWord_4275647, baseEnd_4275647] using wordTrace_append hprefix tailTrace_4275647
  have hstable : (prefixWord ++ tailWord_4275647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275647).length < 2 ^ (prefixWord ++ tailWord_4275647).sum := by decide
  have hdescent : baseEnd_4275647 < baseStart_4275647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275685 : List Nat := [1, 3, 1, 5, 1, 3, 2, 1, 1, 1, 4]
def baseStart_4275685 : Nat := 118140960795 + 4275685 * 2 ^ 59
def prefixEnd_4275685 : Nat := 4983230072969 + 3 ^ 40 * 4275685 * 2
def baseEnd_4275685 : Nat := 2195481532219209096473989

theorem tailTrace_4275685 : CollatzResearch.WordTrace tailWord_4275685 prefixEnd_4275685 2195481532219209096473989 := by
  unfold tailWord_4275685
  simp only [CollatzResearch.WordTrace]
  refine ⟨155947043514930948706620509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103964695676620632471080339 155947043514930948706620509)
  ·
    refine ⟨58480141318099105764982691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155947043514930948706620509 58480141318099105764982691)
    ·
      refine ⟨87720211977148658647474037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58480141318099105764982691 87720211977148658647474037)
      ·
        refine ⟨8223769872857686748200691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87720211977148658647474037 8223769872857686748200691)
        ·
          refine ⟨12335654809286530122301037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8223769872857686748200691 12335654809286530122301037)
          ·
            refine ⟨4625870553482448795862889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12335654809286530122301037 4625870553482448795862889)
            ·
              refine ⟨3469402915111836596897167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4625870553482448795862889 3469402915111836596897167)
              ·
                refine ⟨5204104372667754895345751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3469402915111836596897167 5204104372667754895345751)
                ·
                  refine ⟨7806156559001632343018627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5204104372667754895345751 7806156559001632343018627)
                  ·
                    refine ⟨11709234838502448514527941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7806156559001632343018627 11709234838502448514527941)
                    ·
                      refine ⟨2195481532219209096473989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11709234838502448514527941 2195481532219209096473989)
                      ·
                        rfl

theorem cell23_4275685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_4275685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275685 prefixEnd_4275685 := by exact prefixLift 4275685
  have htrace : WordTrace (prefixWord ++ tailWord_4275685) baseStart_4275685 baseEnd_4275685 := by
    simpa [prefixWord, tailWord_4275685, baseEnd_4275685] using wordTrace_append hprefix tailTrace_4275685
  have hstable : (prefixWord ++ tailWord_4275685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275685).length < 2 ^ (prefixWord ++ tailWord_4275685).sum := by decide
  have hdescent : baseEnd_4275685 < baseStart_4275685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275702 : List Nat := [5, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2]
def baseStart_4275702 : Nat := 118140960795 + 4275702 * 2 ^ 59
def prefixEnd_4275702 : Nat := 4983230072969 + 3 ^ 40 * 4275702 * 2
def baseEnd_4275702 : Nat := 2195490261390335529961411

theorem tailTrace_4275702 : CollatzResearch.WordTrace tailWord_4275702 prefixEnd_4275702 2195490261390335529961411 := by
  unfold tailWord_4275702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9746728972241835038124335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103965109037246240406659573 9746728972241835038124335)
  ·
    refine ⟨14620093458362752557186503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9746728972241835038124335 14620093458362752557186503)
    ·
      refine ⟨21930140187544128835779755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14620093458362752557186503 21930140187544128835779755)
      ·
        refine ⟨32895210281316193253669633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21930140187544128835779755 32895210281316193253669633)
        ·
          refine ⟨24671407710987144940252225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32895210281316193253669633 24671407710987144940252225)
          ·
            refine ⟨18503555783240358705189169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24671407710987144940252225 18503555783240358705189169)
            ·
              refine ⟨13877666837430269028891877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18503555783240358705189169 13877666837430269028891877)
              ·
                refine ⟨2602062532018175442917227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13877666837430269028891877 2602062532018175442917227)
                ·
                  refine ⟨3903093798027263164375841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2602062532018175442917227 3903093798027263164375841)
                  ·
                    refine ⟨2927320348520447373281881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3903093798027263164375841 2927320348520447373281881)
                    ·
                      refine ⟨2195490261390335529961411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2927320348520447373281881 2195490261390335529961411)
                      ·
                        rfl

theorem cell23_4275702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_4275702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275702 prefixEnd_4275702 := by exact prefixLift 4275702
  have htrace : WordTrace (prefixWord ++ tailWord_4275702) baseStart_4275702 baseEnd_4275702 := by
    simpa [prefixWord, tailWord_4275702, baseEnd_4275702] using wordTrace_append hprefix tailTrace_4275702
  have hstable : (prefixWord ++ tailWord_4275702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275702).length < 2 ^ (prefixWord ++ tailWord_4275702).sum := by decide
  have hdescent : baseEnd_4275702 < baseStart_4275702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275711 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 3, 3, 2]
def baseStart_4275711 : Nat := 118140960795 + 4275711 * 2 ^ 59
def prefixEnd_4275711 : Nat := 4983230072969 + 3 ^ 40 * 4275711 * 2
def baseEnd_4275711 : Nat := 2195494882716225994748869

theorem tailTrace_4275711 : CollatzResearch.WordTrace tailWord_4275711 prefixEnd_4275711 2195494882716225994748869 := by
  unfold tailWord_4275711
  simp only [CollatzResearch.WordTrace]
  refine ⟨155947991812836755147066987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103965327875224503431377991 155947991812836755147066987)
  ·
    refine ⟨233921987719255132720600481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155947991812836755147066987 233921987719255132720600481)
    ·
      refine ⟨175441490789441349540450361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233921987719255132720600481 175441490789441349540450361)
      ·
        refine ⟨131581118092081012155337771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175441490789441349540450361 131581118092081012155337771)
        ·
          refine ⟨197371677138121518233006657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131581118092081012155337771 197371677138121518233006657)
          ·
            refine ⟨148028757853591138674754993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197371677138121518233006657 148028757853591138674754993)
            ·
              refine ⟨111021568390193354006066245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148028757853591138674754993 111021568390193354006066245)
              ·
                refine ⟨20816544073161253876137421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111021568390193354006066245 20816544073161253876137421)
                ·
                  refine ⟨7806204027435470203551533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20816544073161253876137421 7806204027435470203551533)
                  ·
                    refine ⟨2927326510288301326331825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7806204027435470203551533 2927326510288301326331825)
                    ·
                      refine ⟨2195494882716225994748869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2927326510288301326331825 2195494882716225994748869)
                      ·
                        rfl

theorem cell23_4275711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 3, 2].length) (baseStart_4275711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275711 prefixEnd_4275711 := by exact prefixLift 4275711
  have htrace : WordTrace (prefixWord ++ tailWord_4275711) baseStart_4275711 baseEnd_4275711 := by
    simpa [prefixWord, tailWord_4275711, baseEnd_4275711] using wordTrace_append hprefix tailTrace_4275711
  have hstable : (prefixWord ++ tailWord_4275711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275711).length < 2 ^ (prefixWord ++ tailWord_4275711).sum := by decide
  have hdescent : baseEnd_4275711 < baseStart_4275711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275742 : List Nat := [4, 3, 3, 1, 2, 1, 9]
def baseStart_4275742 : Nat := 118140960795 + 4275742 * 2 ^ 59
def prefixEnd_4275742 : Nat := 4983230072969 + 3 ^ 40 * 4275742 * 2
def baseEnd_4275742 : Nat := 27105071612549572511867

theorem tailTrace_4275742 : CollatzResearch.WordTrace tailWord_4275742 prefixEnd_4275742 27105071612549572511867 := by
  unfold tailWord_4275742
  simp only [CollatzResearch.WordTrace]
  refine ⟨19493640309465555930180685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103966081650482964960963653 19493640309465555930180685)
  ·
    refine ⟨7310115116049583473817757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19493640309465555930180685 7310115116049583473817757)
    ·
      refine ⟨2741293168518593802681659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7310115116049583473817757 2741293168518593802681659)
      ·
        refine ⟨4111939752777890704022489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2741293168518593802681659 4111939752777890704022489)
        ·
          refine ⟨3083954814583418028016867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4111939752777890704022489 3083954814583418028016867)
          ·
            refine ⟨4625932221875127042025301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3083954814583418028016867 4625932221875127042025301)
            ·
              refine ⟨27105071612549572511867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4625932221875127042025301 27105071612549572511867)
              ·
                rfl

theorem cell23_4275742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 9].length) (baseStart_4275742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275742 prefixEnd_4275742 := by exact prefixLift 4275742
  have htrace : WordTrace (prefixWord ++ tailWord_4275742) baseStart_4275742 baseEnd_4275742 := by
    simpa [prefixWord, tailWord_4275742, baseEnd_4275742] using wordTrace_append hprefix tailTrace_4275742
  have hstable : (prefixWord ++ tailWord_4275742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275742).length < 2 ^ (prefixWord ++ tailWord_4275742).sum := by decide
  have hdescent : baseEnd_4275742 < baseStart_4275742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275775 : List Nat := [1, 1, 2, 2, 3, 4, 1, 3, 2, 2, 2]
def baseStart_4275775 : Nat := 118140960795 + 4275775 * 2 ^ 59
def prefixEnd_4275775 : Nat := 4983230072969 + 3 ^ 40 * 4275775 * 2
def baseEnd_4275775 : Nat := 2195527745478113744348575

theorem tailTrace_4275775 : CollatzResearch.WordTrace tailWord_4275775 prefixEnd_4275775 2195527745478113744348575 := by
  unfold tailWord_4275775
  simp only [CollatzResearch.WordTrace]
  refine ⟨155950326084604894077396779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103966884056403262718264519 155950326084604894077396779)
  ·
    refine ⟨233925489126907341116095169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155950326084604894077396779 233925489126907341116095169)
    ·
      refine ⟨175444116845180505837071377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233925489126907341116095169 175444116845180505837071377)
      ·
        refine ⟨131583087633885379377803533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175444116845180505837071377 131583087633885379377803533)
        ·
          refine ⟨49343657862707017266676325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131583087633885379377803533 49343657862707017266676325)
          ·
            refine ⟨9251935849257565737501811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49343657862707017266676325 9251935849257565737501811)
            ·
              refine ⟨13877903773886348606252717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9251935849257565737501811 13877903773886348606252717)
              ·
                refine ⟨5204213915207380727344769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13877903773886348606252717 5204213915207380727344769)
                ·
                  refine ⟨3903160436405535545508577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5204213915207380727344769 3903160436405535545508577)
                  ·
                    refine ⟨2927370327304151659131433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3903160436405535545508577 2927370327304151659131433)
                    ·
                      refine ⟨2195527745478113744348575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2927370327304151659131433 2195527745478113744348575)
                      ·
                        rfl

theorem cell23_4275775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 2, 2].length) (baseStart_4275775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275775 prefixEnd_4275775 := by exact prefixLift 4275775
  have htrace : WordTrace (prefixWord ++ tailWord_4275775) baseStart_4275775 baseEnd_4275775 := by
    simpa [prefixWord, tailWord_4275775, baseEnd_4275775] using wordTrace_append hprefix tailTrace_4275775
  have hstable : (prefixWord ++ tailWord_4275775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275775).length < 2 ^ (prefixWord ++ tailWord_4275775).sum := by decide
  have hdescent : baseEnd_4275775 < baseStart_4275775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275801 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 4, 5, 2]
def baseStart_4275801 : Nat := 118140960795 + 4275801 * 2 ^ 59
def prefixEnd_4275801 : Nat := 4983230072969 + 3 ^ 40 * 4275801 * 2
def baseEnd_4275801 : Nat := 2195541095975130642623455

theorem tailTrace_4275801 : CollatzResearch.WordTrace tailWord_4275801 prefixEnd_4275801 2195541095975130642623455 := by
  unfold tailWord_4275801
  simp only [CollatzResearch.WordTrace]
  refine ⟨155951274382510700517843257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103967516255007133678562171 155951274382510700517843257)
  ·
    refine ⟨116963455786883025388382443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155951274382510700517843257 116963455786883025388382443)
    ·
      refine ⟨175445183680324538082573665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116963455786883025388382443 175445183680324538082573665)
      ·
        refine ⟨131583887760243403561930249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175445183680324538082573665 131583887760243403561930249)
        ·
          refine ⟨98687915820182552671447687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131583887760243403561930249 98687915820182552671447687)
          ·
            refine ⟨148031873730273829007171531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98687915820182552671447687 148031873730273829007171531)
            ·
              refine ⟨222047810595410743510757297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148031873730273829007171531 222047810595410743510757297)
              ·
                refine ⟨166535857946558057633067973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222047810595410743510757297 166535857946558057633067973)
                ·
                  refine ⟨31225473364979635806200245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 166535857946558057633067973 31225473364979635806200245)
                  ·
                    refine ⟨2927388127966840856831273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31225473364979635806200245 2927388127966840856831273)
                    ·
                      refine ⟨2195541095975130642623455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2927388127966840856831273 2195541095975130642623455)
                      ·
                        rfl

theorem cell23_4275801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 5, 2].length) (baseStart_4275801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275801 prefixEnd_4275801 := by exact prefixLift 4275801
  have htrace : WordTrace (prefixWord ++ tailWord_4275801) baseStart_4275801 baseEnd_4275801 := by
    simpa [prefixWord, tailWord_4275801, baseEnd_4275801] using wordTrace_append hprefix tailTrace_4275801
  have hstable : (prefixWord ++ tailWord_4275801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275801).length < 2 ^ (prefixWord ++ tailWord_4275801).sum := by decide
  have hdescent : baseEnd_4275801 < baseStart_4275801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275811 : List Nat := [1, 1, 1, 5, 1, 3, 2, 2, 2, 5]
def baseStart_4275811 : Nat := 118140960795 + 4275811 * 2 ^ 59
def prefixEnd_4275811 : Nat := 4983230072969 + 3 ^ 40 * 4275811 * 2
def baseEnd_4275811 : Nat := 731848743593891867832803

theorem tailTrace_4275811 : CollatzResearch.WordTrace tailWord_4275811 prefixEnd_4275811 731848743593891867832803 := by
  unfold tailWord_4275811
  simp only [CollatzResearch.WordTrace]
  refine ⟨155951639112474472225707287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103967759408316314817138191 155951639112474472225707287)
  ·
    refine ⟨233927458668711708338560931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155951639112474472225707287 233927458668711708338560931)
    ·
      refine ⟨350891188003067562507841397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233927458668711708338560931 350891188003067562507841397)
      ·
        refine ⟨32896048875287583985110131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 350891188003067562507841397 32896048875287583985110131)
        ·
          refine ⟨49344073312931375977665197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32896048875287583985110131 49344073312931375977665197)
          ·
            refine ⟨18504027492349265991624449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49344073312931375977665197 18504027492349265991624449)
            ·
              refine ⟨13878020619261949493718337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18504027492349265991624449 13878020619261949493718337)
              ·
                refine ⟨10408515464446462120288753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13878020619261949493718337 10408515464446462120288753)
                ·
                  refine ⟨7806386598334846590216565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10408515464446462120288753 7806386598334846590216565)
                  ·
                    refine ⟨731848743593891867832803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7806386598334846590216565 731848743593891867832803)
                    ·
                      rfl

theorem cell23_4275811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 5].length) (baseStart_4275811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275811 prefixEnd_4275811 := by exact prefixLift 4275811
  have htrace : WordTrace (prefixWord ++ tailWord_4275811) baseStart_4275811 baseEnd_4275811 := by
    simpa [prefixWord, tailWord_4275811, baseEnd_4275811] using wordTrace_append hprefix tailTrace_4275811
  have hstable : (prefixWord ++ tailWord_4275811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275811).length < 2 ^ (prefixWord ++ tailWord_4275811).sum := by decide
  have hdescent : baseEnd_4275811 < baseStart_4275811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275818 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 2, 5, 2]
def baseStart_4275818 : Nat := 118140960795 + 4275818 * 2 ^ 59
def prefixEnd_4275818 : Nat := 4983230072969 + 3 ^ 40 * 4275818 * 2
def baseEnd_4275818 : Nat := 2195549825146257076110877

theorem tailTrace_4275818 : CollatzResearch.WordTrace tailWord_4275818 prefixEnd_4275818 2195549825146257076110877 := by
  unfold tailWord_4275818
  simp only [CollatzResearch.WordTrace]
  refine ⟨38987973605862278105303027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103967929615632741614141405 38987973605862278105303027)
  ·
    refine ⟨58481960408793417157954541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38987973605862278105303027 58481960408793417157954541)
    ·
      refine ⟨21930735153297531434232953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58481960408793417157954541 21930735153297531434232953)
      ·
        refine ⟨16448051364973148575674715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21930735153297531434232953 16448051364973148575674715)
        ·
          refine ⟨24672077047459722863512073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16448051364973148575674715 24672077047459722863512073)
          ·
            refine ⟨18504057785594792147634055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24672077047459722863512073 18504057785594792147634055)
            ·
              refine ⟨27756086678392188221451083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18504057785594792147634055 27756086678392188221451083)
              ·
                refine ⟨41634130017588282332176625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27756086678392188221451083 41634130017588282332176625)
                ·
                  refine ⟨31225597513191211749132469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41634130017588282332176625 31225597513191211749132469)
                  ·
                    refine ⟨2927399766861676101481169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31225597513191211749132469 2927399766861676101481169)
                    ·
                      refine ⟨2195549825146257076110877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2927399766861676101481169 2195549825146257076110877)
                      ·
                        rfl

theorem cell23_4275818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_4275818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275818 prefixEnd_4275818 := by exact prefixLift 4275818
  have htrace : WordTrace (prefixWord ++ tailWord_4275818) baseStart_4275818 baseEnd_4275818 := by
    simpa [prefixWord, tailWord_4275818, baseEnd_4275818] using wordTrace_append hprefix tailTrace_4275818
  have hstable : (prefixWord ++ tailWord_4275818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275818).length < 2 ^ (prefixWord ++ tailWord_4275818).sum := by decide
  have hdescent : baseEnd_4275818 < baseStart_4275818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275851 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 3]
def baseStart_4275851 : Nat := 118140960795 + 4275851 * 2 ^ 59
def prefixEnd_4275851 : Nat := 4983230072969 + 3 ^ 40 * 4275851 * 2
def baseEnd_4275851 : Nat := 2195566770007855446998225

theorem tailTrace_4275851 : CollatzResearch.WordTrace tailWord_4275851 prefixEnd_4275851 2195566770007855446998225 := by
  unfold tailWord_4275851
  simp only [CollatzResearch.WordTrace]
  refine ⟨155953098032329559057163407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103968732021553039371442271 155953098032329559057163407)
  ·
    refine ⟨233929647048494338585745111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155953098032329559057163407 233929647048494338585745111)
    ·
      refine ⟨350894470572741507878617667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233929647048494338585745111 350894470572741507878617667)
      ·
        refine ⟨526341705859112261817926501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350894470572741507878617667 526341705859112261817926501)
        ·
          refine ⟨98689069848583549090861219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 526341705859112261817926501 98689069848583549090861219)
          ·
            refine ⟨148033604772875323636291829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98689069848583549090861219 148033604772875323636291829)
            ·
              refine ⟨13878150447457061590902359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 148033604772875323636291829 13878150447457061590902359)
              ·
                refine ⟨20817225671185592386353539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13878150447457061590902359 20817225671185592386353539)
                ·
                  refine ⟨31225838506778388579530309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20817225671185592386353539 31225838506778388579530309)
                  ·
                    refine ⟨5854844720020947858661933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31225838506778388579530309 5854844720020947858661933)
                    ·
                      refine ⟨2195566770007855446998225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5854844720020947858661933 2195566770007855446998225)
                      ·
                        rfl

theorem cell23_4275851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 3].length) (baseStart_4275851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275851 prefixEnd_4275851 := by exact prefixLift 4275851
  have htrace : WordTrace (prefixWord ++ tailWord_4275851) baseStart_4275851 baseEnd_4275851 := by
    simpa [prefixWord, tailWord_4275851, baseEnd_4275851] using wordTrace_append hprefix tailTrace_4275851
  have hstable : (prefixWord ++ tailWord_4275851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275851).length < 2 ^ (prefixWord ++ tailWord_4275851).sum := by decide
  have hdescent : baseEnd_4275851 < baseStart_4275851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275918 : List Nat := [4, 1, 1, 1, 3, 1, 1, 5, 1, 5]
def baseStart_4275918 : Nat := 118140960795 + 4275918 * 2 ^ 59
def prefixEnd_4275918 : Nat := 4983230072969 + 3 ^ 40 * 4275918 * 2
def baseEnd_4275918 : Nat := 731867057737235561620139

theorem tailTrace_4275918 : CollatzResearch.WordTrace tailWord_4275918 prefixEnd_4275918 731867057737235561620139 := by
  unfold tailWord_4275918
  simp only [CollatzResearch.WordTrace]
  refine ⟨19494442715385853687481551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103970361148724552999901605 19494442715385853687481551)
  ·
    refine ⟨29241664073078780531222327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19494442715385853687481551 29241664073078780531222327)
    ·
      refine ⟨43862496109618170796833491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29241664073078780531222327 43862496109618170796833491)
      ·
        refine ⟨65793744164427256195250237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43862496109618170796833491 65793744164427256195250237)
        ·
          refine ⟨24672654061660221073218839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65793744164427256195250237 24672654061660221073218839)
          ·
            refine ⟨37008981092490331609828259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24672654061660221073218839 37008981092490331609828259)
            ·
              refine ⟨55513471638735497414742389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37008981092490331609828259 55513471638735497414742389)
              ·
                refine ⟨5204387966131452882632099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55513471638735497414742389 5204387966131452882632099)
                ·
                  refine ⟨7806581949197179323948149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5204387966131452882632099 7806581949197179323948149)
                  ·
                    refine ⟨731867057737235561620139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7806581949197179323948149 731867057737235561620139)
                    ·
                      rfl

theorem cell23_4275918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_4275918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275918 prefixEnd_4275918 := by exact prefixLift 4275918
  have htrace : WordTrace (prefixWord ++ tailWord_4275918) baseStart_4275918 baseEnd_4275918 := by
    simpa [prefixWord, tailWord_4275918, baseEnd_4275918] using wordTrace_append hprefix tailTrace_4275918
  have hstable : (prefixWord ++ tailWord_4275918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275918).length < 2 ^ (prefixWord ++ tailWord_4275918).sum := by decide
  have hdescent : baseEnd_4275918 < baseStart_4275918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275926 : List Nat := [5, 2, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_4275926 : Nat := 118140960795 + 4275926 * 2 ^ 59
def prefixEnd_4275926 : Nat := 4983230072969 + 3 ^ 40 * 4275926 * 2
def baseEnd_4275926 : Nat := 731868427018980884520127

theorem tailTrace_4275926 : CollatzResearch.WordTrace tailWord_4275926 prefixEnd_4275926 731868427018980884520127 := by
  unfold tailWord_4275926
  simp only [CollatzResearch.WordTrace]
  refine ⟨9747239594191115429133977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103970555671371897910762421 9747239594191115429133977)
  ·
    refine ⟨7310429695643336571850483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9747239594191115429133977 7310429695643336571850483)
    ·
      refine ⟨10965644543465004857775725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7310429695643336571850483 10965644543465004857775725)
      ·
        refine ⟨4112116703799376821665897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10965644543465004857775725 4112116703799376821665897)
        ·
          refine ⟨3084087527849532616249423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4112116703799376821665897 3084087527849532616249423)
          ·
            refine ⟨4626131291774298924374135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3084087527849532616249423 4626131291774298924374135)
            ·
              refine ⟨6939196937661448386561203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4626131291774298924374135 6939196937661448386561203)
              ·
                refine ⟨10408795406492172579841805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6939196937661448386561203 10408795406492172579841805)
                ·
                  refine ⟨3903298277434564717440677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10408795406492172579841805 3903298277434564717440677)
                  ·
                    refine ⟨731868427018980884520127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3903298277434564717440677 731868427018980884520127)
                    ·
                      rfl

theorem cell23_4275926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_4275926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275926 prefixEnd_4275926 := by exact prefixLift 4275926
  have htrace : WordTrace (prefixWord ++ tailWord_4275926) baseStart_4275926 baseEnd_4275926 := by
    simpa [prefixWord, tailWord_4275926, baseEnd_4275926] using wordTrace_append hprefix tailTrace_4275926
  have hstable : (prefixWord ++ tailWord_4275926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275926).length < 2 ^ (prefixWord ++ tailWord_4275926).sum := by decide
  have hdescent : baseEnd_4275926 < baseStart_4275926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275951 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 6]
def baseStart_4275951 : Nat := 118140960795 + 4275951 * 2 ^ 59
def prefixEnd_4275951 : Nat := 4983230072969 + 3 ^ 40 * 4275951 * 2
def baseEnd_4275951 : Nat := 2195618118073305055747765

theorem tailTrace_4275951 : CollatzResearch.WordTrace tailWord_4275951 prefixEnd_4275951 2195618118073305055747765 := by
  unfold tailWord_4275951
  simp only [CollatzResearch.WordTrace]
  refine ⟨155956745331967276135803707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103971163554644850757202471 155956745331967276135803707)
  ·
    refine ⟨233935117997950914203705561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155956745331967276135803707 233935117997950914203705561)
    ·
      refine ⟨175451338498463185652779171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233935117997950914203705561 175451338498463185652779171)
      ·
        refine ⟨263177007747694778479168757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175451338498463185652779171 263177007747694778479168757)
        ·
          refine ⟨24672844476346385482422071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 263177007747694778479168757 24672844476346385482422071)
          ·
            refine ⟨37009266714519578223633107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24672844476346385482422071 37009266714519578223633107)
            ·
              refine ⟨55513900071779367335449661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37009266714519578223633107 55513900071779367335449661)
              ·
                refine ⟨20817712526917262750793623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55513900071779367335449661 20817712526917262750793623)
                ·
                  refine ⟨31226568790375894126190435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20817712526917262750793623 31226568790375894126190435)
                  ·
                    refine ⟨46839853185563841189285653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31226568790375894126190435 46839853185563841189285653)
                    ·
                      refine ⟨2195618118073305055747765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46839853185563841189285653 2195618118073305055747765)
                      ·
                        rfl

theorem cell23_4275951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_4275951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275951 prefixEnd_4275951 := by exact prefixLift 4275951
  have htrace : WordTrace (prefixWord ++ tailWord_4275951) baseStart_4275951 baseEnd_4275951 := by
    simpa [prefixWord, tailWord_4275951, baseEnd_4275951] using wordTrace_append hprefix tailTrace_4275951
  have hstable : (prefixWord ++ tailWord_4275951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275951).length < 2 ^ (prefixWord ++ tailWord_4275951).sum := by decide
  have hdescent : baseEnd_4275951 < baseStart_4275951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275955 : List Nat := [1, 1, 1, 2, 2, 3, 2, 4, 3, 2, 2]
def baseStart_4275955 : Nat := 118140960795 + 4275955 * 2 ^ 59
def prefixEnd_4275955 : Nat := 4983230072969 + 3 ^ 40 * 4275955 * 2
def baseEnd_4275955 : Nat := 2195620171995923040097747

theorem tailTrace_4275955 : CollatzResearch.WordTrace tailWord_4275955 prefixEnd_4275955 2195620171995923040097747 := by
  unfold tailWord_4275955
  simp only [CollatzResearch.WordTrace]
  refine ⟨155956891223952784818949319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103971260815968523212632879 155956891223952784818949319)
  ·
    refine ⟨233935336835929177228423979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155956891223952784818949319 233935336835929177228423979)
    ·
      refine ⟨350903005253893765842635969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233935336835929177228423979 350903005253893765842635969)
      ·
        refine ⟨263177253940420324381976977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350903005253893765842635969 263177253940420324381976977)
        ·
          refine ⟨197382940455315243286482733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263177253940420324381976977 197382940455315243286482733)
          ·
            refine ⟨74018602670743216232431025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197382940455315243286482733 74018602670743216232431025)
            ·
              refine ⟨55513952003057412174323269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74018602670743216232431025 55513952003057412174323269)
              ·
                refine ⟨10408866000573264782685613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55513952003057412174323269 10408866000573264782685613)
                ·
                  refine ⟨3903324750214974293507105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10408866000573264782685613 3903324750214974293507105)
                  ·
                    refine ⟨2927493562661230720130329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3903324750214974293507105 2927493562661230720130329)
                    ·
                      refine ⟨2195620171995923040097747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2927493562661230720130329 2195620171995923040097747)
                      ·
                        rfl

theorem cell23_4275955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 2, 2].length) (baseStart_4275955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275955 prefixEnd_4275955 := by exact prefixLift 4275955
  have htrace : WordTrace (prefixWord ++ tailWord_4275955) baseStart_4275955 baseEnd_4275955 := by
    simpa [prefixWord, tailWord_4275955, baseEnd_4275955] using wordTrace_append hprefix tailTrace_4275955
  have hstable : (prefixWord ++ tailWord_4275955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275955).length < 2 ^ (prefixWord ++ tailWord_4275955).sum := by decide
  have hdescent : baseEnd_4275955 < baseStart_4275955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275972 : List Nat := [2, 3, 2, 2, 1, 3, 3, 1, 1, 1, 4]
def baseStart_4275972 : Nat := 118140960795 + 4275972 * 2 ^ 59
def prefixEnd_4275972 : Nat := 4983230072969 + 3 ^ 40 * 4275972 * 2
def baseEnd_4275972 : Nat := 2195628901167049473585169

theorem tailTrace_4275972 : CollatzResearch.WordTrace tailWord_4275972 prefixEnd_4275972 2195628901167049473585169 := by
  unfold tailWord_4275972
  simp only [CollatzResearch.WordTrace]
  refine ⟨77978755632445598361159085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103971674176594131148212113 77978755632445598361159085)
  ·
    refine ⟨29242033362167099385434657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77978755632445598361159085 29242033362167099385434657)
    ·
      refine ⟨21931525021625324539075993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29242033362167099385434657 21931525021625324539075993)
      ·
        refine ⟨16448643766218993404306995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21931525021625324539075993 16448643766218993404306995)
        ·
          refine ⟨24672965649328490106460493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16448643766218993404306995 24672965649328490106460493)
          ·
            refine ⟨9252362118498183789922685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24672965649328490106460493 9252362118498183789922685)
            ·
              refine ⟨3469635794436818921221007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9252362118498183789922685 3469635794436818921221007)
              ·
                refine ⟨5204453691655228381831511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3469635794436818921221007 5204453691655228381831511)
                ·
                  refine ⟨7806680537482842572747267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5204453691655228381831511 7806680537482842572747267)
                  ·
                    refine ⟨11710020806224263859120901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7806680537482842572747267 11710020806224263859120901)
                    ·
                      refine ⟨2195628901167049473585169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11710020806224263859120901 2195628901167049473585169)
                      ·
                        rfl

theorem cell23_4275972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_4275972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275972 prefixEnd_4275972 := by exact prefixLift 4275972
  have htrace : WordTrace (prefixWord ++ tailWord_4275972) baseStart_4275972 baseEnd_4275972 := by
    simpa [prefixWord, tailWord_4275972, baseEnd_4275972] using wordTrace_append hprefix tailTrace_4275972
  have hstable : (prefixWord ++ tailWord_4275972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275972).length < 2 ^ (prefixWord ++ tailWord_4275972).sum := by decide
  have hdescent : baseEnd_4275972 < baseStart_4275972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275989 : List Nat := [1, 3, 2, 1, 2, 4, 1, 4, 1, 2, 2]
def baseStart_4275989 : Nat := 118140960795 + 4275989 * 2 ^ 59
def prefixEnd_4275989 : Nat := 4983230072969 + 3 ^ 40 * 4275989 * 2
def baseEnd_4275989 : Nat := 2195637630338175907072591

theorem tailTrace_4275989 : CollatzResearch.WordTrace tailWord_4275989 prefixEnd_4275989 2195637630338175907072591 := by
  unfold tailWord_4275989
  simp only [CollatzResearch.WordTrace]
  refine ⟨155958131305829608625687021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103972087537219739083791347 155958131305829608625687021)
  ·
    refine ⟨58484299239686103234632633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155958131305829608625687021 58484299239686103234632633)
    ·
      refine ⟨43863224429764577425974475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58484299239686103234632633 43863224429764577425974475)
      ·
        refine ⟨65794836644646866138961713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43863224429764577425974475 65794836644646866138961713)
        ·
          refine ⟨49346127483485149604221285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65794836644646866138961713 49346127483485149604221285)
          ·
            refine ⟨9252398903153465550791491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49346127483485149604221285 9252398903153465550791491)
            ·
              refine ⟨13878598354730198326187237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9252398903153465550791491 13878598354730198326187237)
              ·
                refine ⟨2602237191511912186160107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13878598354730198326187237 2602237191511912186160107)
                ·
                  refine ⟨3903355787267868279240161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2602237191511912186160107 3903355787267868279240161)
                  ·
                    refine ⟨2927516840450901209430121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3903355787267868279240161 2927516840450901209430121)
                    ·
                      refine ⟨2195637630338175907072591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2927516840450901209430121 2195637630338175907072591)
                      ·
                        rfl

theorem cell23_4275989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 1, 2, 2].length) (baseStart_4275989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275989 prefixEnd_4275989 := by exact prefixLift 4275989
  have htrace : WordTrace (prefixWord ++ tailWord_4275989) baseStart_4275989 baseEnd_4275989 := by
    simpa [prefixWord, tailWord_4275989, baseEnd_4275989] using wordTrace_append hprefix tailTrace_4275989
  have hstable : (prefixWord ++ tailWord_4275989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275989).length < 2 ^ (prefixWord ++ tailWord_4275989).sum := by decide
  have hdescent : baseEnd_4275989 < baseStart_4275989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276005 : List Nat := [1, 3, 1, 2, 3, 3, 2, 1, 1, 3, 3]
def baseStart_4276005 : Nat := 118140960795 + 4276005 * 2 ^ 59
def prefixEnd_4276005 : Nat := 4983230072969 + 3 ^ 40 * 4276005 * 2
def baseEnd_4276005 : Nat := 2195645846028647844472517

theorem tailTrace_4276005 : CollatzResearch.WordTrace tailWord_4276005 prefixEnd_4276005 2195645846028647844472517 := by
  unfold tailWord_4276005
  simp only [CollatzResearch.WordTrace]
  refine ⟨155958714873771643358269469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103972476582514428905512979 155958714873771643358269469)
  ·
    refine ⟨58484518077664366259351051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155958714873771643358269469 58484518077664366259351051)
    ·
      refine ⟨87726777116496549389026577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58484518077664366259351051 87726777116496549389026577)
      ·
        refine ⟨65795082837372412041769933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87726777116496549389026577 65795082837372412041769933)
        ·
          refine ⟨24673156064014654515663725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65795082837372412041769933 24673156064014654515663725)
          ·
            refine ⟨9252433524005495443373897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24673156064014654515663725 9252433524005495443373897)
            ·
              refine ⟨6939325143004121582530423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9252433524005495443373897 6939325143004121582530423)
              ·
                refine ⟨10408987714506182373795635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6939325143004121582530423 10408987714506182373795635)
                ·
                  refine ⟨15613481571759273560693453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10408987714506182373795635 15613481571759273560693453)
                  ·
                    refine ⟨5855055589409727585260045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15613481571759273560693453 5855055589409727585260045)
                    ·
                      refine ⟨2195645846028647844472517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5855055589409727585260045 2195645846028647844472517)
                      ·
                        rfl

theorem cell23_4276005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_4276005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276005 prefixEnd_4276005 := by exact prefixLift 4276005
  have htrace : WordTrace (prefixWord ++ tailWord_4276005) baseStart_4276005 baseEnd_4276005 := by
    simpa [prefixWord, tailWord_4276005, baseEnd_4276005] using wordTrace_append hprefix tailTrace_4276005
  have hstable : (prefixWord ++ tailWord_4276005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276005).length < 2 ^ (prefixWord ++ tailWord_4276005).sum := by decide
  have hdescent : baseEnd_4276005 < baseStart_4276005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276011 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 4]
def baseStart_4276011 : Nat := 118140960795 + 4276011 * 2 ^ 59
def prefixEnd_4276011 : Nat := 4983230072969 + 3 ^ 40 * 4276011 * 2
def baseEnd_4276011 : Nat := 2195648926912574820997489

theorem tailTrace_4276011 : CollatzResearch.WordTrace tailWord_4276011 prefixEnd_4276011 2195648926912574820997489 := by
  unfold tailWord_4276011
  simp only [CollatzResearch.WordTrace]
  refine ⟨155958933711749906382987887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103972622474499937588658591 155958933711749906382987887)
  ·
    refine ⟨233938400567624859574481831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155958933711749906382987887 233938400567624859574481831)
    ·
      refine ⟨350907600851437289361722747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233938400567624859574481831 350907600851437289361722747)
      ·
        refine ⟨526361401277155934042584121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350907600851437289361722747 526361401277155934042584121)
        ·
          refine ⟨394771050957866950531938091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 526361401277155934042584121 394771050957866950531938091)
          ·
            refine ⟨592156576436800425797907137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394771050957866950531938091 592156576436800425797907137)
            ·
              refine ⟨444117432327600319348430353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 592156576436800425797907137 444117432327600319348430353)
              ·
                refine ⟨333088074245700239511322765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 444117432327600319348430353 333088074245700239511322765)
                ·
                  refine ⟨124908027842137589816746037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 333088074245700239511322765 124908027842137589816746037)
                  ·
                    refine ⟨11710127610200399045319941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 124908027842137589816746037 11710127610200399045319941)
                    ·
                      refine ⟨2195648926912574820997489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11710127610200399045319941 2195648926912574820997489)
                      ·
                        rfl

theorem cell23_4276011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 4].length) (baseStart_4276011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276011 prefixEnd_4276011 := by exact prefixLift 4276011
  have htrace : WordTrace (prefixWord ++ tailWord_4276011) baseStart_4276011 baseEnd_4276011 := by
    simpa [prefixWord, tailWord_4276011, baseEnd_4276011] using wordTrace_append hprefix tailTrace_4276011
  have hstable : (prefixWord ++ tailWord_4276011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276011).length < 2 ^ (prefixWord ++ tailWord_4276011).sum := by decide
  have hdescent : baseEnd_4276011 < baseStart_4276011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276022 : List Nat := [5, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_4276022 : Nat := 118140960795 + 4276022 * 2 ^ 59
def prefixEnd_4276022 : Nat := 4983230072969 + 3 ^ 40 * 4276022 * 2
def baseEnd_4276022 : Nat := 2195654575199774277959939

theorem tailTrace_4276022 : CollatzResearch.WordTrace tailWord_4276022 prefixEnd_4276022 2195654575199774277959939 := by
  unfold tailWord_4276022
  simp only [CollatzResearch.WordTrace]
  refine ⟨9747458432169378453852395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103972889943140036841092213 9747458432169378453852395)
  ·
    refine ⟨14621187648254067680778593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9747458432169378453852395 14621187648254067680778593)
    ·
      refine ⟨10965890736190550760583945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14621187648254067680778593 10965890736190550760583945)
      ·
        refine ⟨8224418052142913070437959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10965890736190550760583945 8224418052142913070437959)
        ·
          refine ⟨12336627078214369605656939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8224418052142913070437959 12336627078214369605656939)
          ·
            refine ⟨18504940617321554408485409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12336627078214369605656939 18504940617321554408485409)
            ·
              refine ⟨13878705462991165806364057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18504940617321554408485409 13878705462991165806364057)
              ·
                refine ⟨10409029097243374354773043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13878705462991165806364057 10409029097243374354773043)
                ·
                  refine ⟨15613543645865061532159565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10409029097243374354773043 15613543645865061532159565)
                  ·
                    refine ⟨5855078867199398074559837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15613543645865061532159565 5855078867199398074559837)
                    ·
                      refine ⟨2195654575199774277959939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5855078867199398074559837 2195654575199774277959939)
                      ·
                        rfl

theorem cell23_4276022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_4276022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276022 prefixEnd_4276022 := by exact prefixLift 4276022
  have htrace : WordTrace (prefixWord ++ tailWord_4276022) baseStart_4276022 baseEnd_4276022 := by
    simpa [prefixWord, tailWord_4276022, baseEnd_4276022] using wordTrace_append hprefix tailTrace_4276022
  have hstable : (prefixWord ++ tailWord_4276022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276022).length < 2 ^ (prefixWord ++ tailWord_4276022).sum := by decide
  have hdescent : baseEnd_4276022 < baseStart_4276022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276058 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4]
def baseStart_4276058 : Nat := 118140960795 + 4276058 * 2 ^ 59
def prefixEnd_4276058 : Nat := 4983230072969 + 3 ^ 40 * 4276058 * 2
def baseEnd_4276058 : Nat := 2195673060503336137109773

theorem tailTrace_4276058 : CollatzResearch.WordTrace tailWord_4276058 prefixEnd_4276058 2195673060503336137109773 := by
  unfold tailWord_4276058
  simp only [CollatzResearch.WordTrace]
  refine ⟨38990161985644908352487207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103973765295053088939965885 38990161985644908352487207)
  ·
    refine ⟨58485242978467362528730811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38990161985644908352487207 58485242978467362528730811)
    ·
      refine ⟨87727864467701043793096217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58485242978467362528730811 87727864467701043793096217)
      ·
        refine ⟨65795898350775782844822163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87727864467701043793096217 65795898350775782844822163)
        ·
          refine ⟨98693847526163674267233245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65795898350775782844822163 98693847526163674267233245)
          ·
            refine ⟨37010192822311377850212467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98693847526163674267233245 37010192822311377850212467)
            ·
              refine ⟨55515289233467066775318701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37010192822311377850212467 55515289233467066775318701)
              ·
                refine ⟨20818233462550150040744513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55515289233467066775318701 20818233462550150040744513)
                ·
                  refine ⟨15613675096912612530558385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20818233462550150040744513 15613675096912612530558385)
                  ·
                    refine ⟨11710256322684459397918789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15613675096912612530558385 11710256322684459397918789)
                    ·
                      refine ⟨2195673060503336137109773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11710256322684459397918789 2195673060503336137109773)
                      ·
                        rfl

theorem cell23_4276058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_4276058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276058 prefixEnd_4276058 := by exact prefixLift 4276058
  have htrace : WordTrace (prefixWord ++ tailWord_4276058) baseStart_4276058 baseEnd_4276058 := by
    simpa [prefixWord, tailWord_4276058, baseEnd_4276058] using wordTrace_append hprefix tailTrace_4276058
  have hstable : (prefixWord ++ tailWord_4276058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276058).length < 2 ^ (prefixWord ++ tailWord_4276058).sum := by decide
  have hdescent : baseEnd_4276058 < baseStart_4276058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276105 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 2, 5, 2]
def baseStart_4276105 : Nat := 118140960795 + 4276105 * 2 ^ 59
def prefixEnd_4276105 : Nat := 4983230072969 + 3 ^ 40 * 4276105 * 2
def baseEnd_4276105 : Nat := 2195697194094097453222057

theorem tailTrace_4276105 : CollatzResearch.WordTrace tailWord_4276105 prefixEnd_4276105 2195697194094097453222057 := by
  unfold tailWord_4276105
  simp only [CollatzResearch.WordTrace]
  refine ⟨155962362173409360436909769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103974908115606240291273179 155962362173409360436909769)
  ·
    refine ⟨116971771630057020327682327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155962362173409360436909769 116971771630057020327682327)
    ·
      refine ⟨175457657445085530491523491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116971771630057020327682327 175457657445085530491523491)
      ·
        refine ⟨263186486167628295737285237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175457657445085530491523491 263186486167628295737285237)
        ·
          refine ⟨24673733078215152725370491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 263186486167628295737285237 24673733078215152725370491)
          ·
            refine ⟨37010599617322729088055737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24673733078215152725370491 37010599617322729088055737)
            ·
              refine ⟨27757949712992046816041803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37010599617322729088055737 27757949712992046816041803)
              ·
                refine ⟨41636924569488070224062705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27757949712992046816041803 41636924569488070224062705)
                ·
                  refine ⟨31227693427116052668047029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41636924569488070224062705 31227693427116052668047029)
                  ·
                    refine ⟨2927596258792129937629409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31227693427116052668047029 2927596258792129937629409)
                    ·
                      refine ⟨2195697194094097453222057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2927596258792129937629409 2195697194094097453222057)
                      ·
                        rfl

theorem cell23_4276105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 5, 2].length) (baseStart_4276105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276105 prefixEnd_4276105 := by exact prefixLift 4276105
  have htrace : WordTrace (prefixWord ++ tailWord_4276105) baseStart_4276105 baseEnd_4276105 := by
    simpa [prefixWord, tailWord_4276105, baseEnd_4276105] using wordTrace_append hprefix tailTrace_4276105
  have hstable : (prefixWord ++ tailWord_4276105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276105).length < 2 ^ (prefixWord ++ tailWord_4276105).sum := by decide
  have hdescent : baseEnd_4276105 < baseStart_4276105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276202 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 5, 1, 3]
def baseStart_4276202 : Nat := 118140960795 + 4276202 * 2 ^ 59
def prefixEnd_4276202 : Nat := 4983230072969 + 3 ^ 40 * 4276202 * 2
def baseEnd_4276202 : Nat := 2195747001717583573709111

theorem tailTrace_4276202 : CollatzResearch.WordTrace tailWord_4276202 prefixEnd_4276202 2195747001717583573709111 := by
  unfold tailWord_4276202
  simp only [CollatzResearch.WordTrace]
  refine ⟨38991475013514486500797715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103977266702705297335460573 38991475013514486500797715)
  ·
    refine ⟨58487212520271729751196573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38991475013514486500797715 58487212520271729751196573)
    ·
      refine ⟨21932704695101898656698715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58487212520271729751196573 21932704695101898656698715)
      ·
        refine ⟨32899057042652847985048073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21932704695101898656698715 32899057042652847985048073)
        ·
          refine ⟨24674292781989635988786055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32899057042652847985048073 24674292781989635988786055)
          ·
            refine ⟨37011439172984453983179083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24674292781989635988786055 37011439172984453983179083)
            ·
              refine ⟨55517158759476680974768625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37011439172984453983179083 55517158759476680974768625)
              ·
                refine ⟨41637869069607510731076469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55517158759476680974768625 41637869069607510731076469)
                ·
                  refine ⟨3903550225275704131038419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41637869069607510731076469 3903550225275704131038419)
                  ·
                    refine ⟨5855325337913556196557629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3903550225275704131038419 5855325337913556196557629)
                    ·
                      refine ⟨2195747001717583573709111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5855325337913556196557629 2195747001717583573709111)
                      ·
                        rfl

theorem cell23_4276202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_4276202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276202 prefixEnd_4276202 := by exact prefixLift 4276202
  have htrace : WordTrace (prefixWord ++ tailWord_4276202) baseStart_4276202 baseEnd_4276202 := by
    simpa [prefixWord, tailWord_4276202, baseEnd_4276202] using wordTrace_append hprefix tailTrace_4276202
  have hstable : (prefixWord ++ tailWord_4276202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276202).length < 2 ^ (prefixWord ++ tailWord_4276202).sum := by decide
  have hdescent : baseEnd_4276202 < baseStart_4276202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276209 : List Nat := [1, 2, 2, 2, 6, 1, 1, 2, 6]
def baseStart_4276209 : Nat := 118140960795 + 4276209 * 2 ^ 59
def prefixEnd_4276209 : Nat := 4983230072969 + 3 ^ 40 * 4276209 * 2
def baseEnd_4276209 : Nat := 243972288453573894035731

theorem tailTrace_4276209 : CollatzResearch.WordTrace tailWord_4276209 prefixEnd_4276209 243972288453573894035731 := by
  unfold tailWord_4276209
  simp only [CollatzResearch.WordTrace]
  refine ⟨155966155365032586198695681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103977436910021724132463787 155966155365032586198695681)
  ·
    refine ⟨116974616523774439649021761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155966155365032586198695681 116974616523774439649021761)
    ·
      refine ⟨87730962392830829736766321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116974616523774439649021761 87730962392830829736766321)
      ·
        refine ⟨65798221794623122302574741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87730962392830829736766321 65798221794623122302574741)
        ·
          refine ⟨3084291646622958857933191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65798221794623122302574741 3084291646622958857933191)
          ·
            refine ⟨4626437469934438286899787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3084291646622958857933191 4626437469934438286899787)
            ·
              refine ⟨6939656204901657430349681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4626437469934438286899787 6939656204901657430349681)
              ·
                refine ⟨5204742153676243072762261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6939656204901657430349681 5204742153676243072762261)
                ·
                  refine ⟨243972288453573894035731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5204742153676243072762261 243972288453573894035731)
                  ·
                    rfl

theorem cell23_4276209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 6].length) (baseStart_4276209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276209 prefixEnd_4276209 := by exact prefixLift 4276209
  have htrace : WordTrace (prefixWord ++ tailWord_4276209) baseStart_4276209 baseEnd_4276209 := by
    simpa [prefixWord, tailWord_4276209, baseEnd_4276209] using wordTrace_append hprefix tailTrace_4276209
  have hstable : (prefixWord ++ tailWord_4276209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276209).length < 2 ^ (prefixWord ++ tailWord_4276209).sum := by decide
  have hdescent : baseEnd_4276209 < baseStart_4276209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276218 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 2, 10]
def baseStart_4276218 : Nat := 118140960795 + 4276218 * 2 ^ 59
def prefixEnd_4276218 : Nat := 4983230072969 + 3 ^ 40 * 4276218 * 2
def baseEnd_4276218 : Nat := 731918405802685170369679

theorem tailTrace_4276218 : CollatzResearch.WordTrace tailWord_4276218 prefixEnd_4276218 731918405802685170369679 := by
  unfold tailWord_4276218
  simp only [CollatzResearch.WordTrace]
  refine ⟨38991620905499995183943327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103977655747999987157182205 38991620905499995183943327)
  ·
    refine ⟨58487431358249992775914991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38991620905499995183943327 58487431358249992775914991)
    ·
      refine ⟨87731147037374989163872487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58487431358249992775914991 87731147037374989163872487)
      ·
        refine ⟨131596720556062483745808731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87731147037374989163872487 131596720556062483745808731)
        ·
          refine ⟨197395080834093725618713097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131596720556062483745808731 197395080834093725618713097)
          ·
            refine ⟨148046310625570294214034823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197395080834093725618713097 148046310625570294214034823)
            ·
              refine ⟨222069465938355441321052235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148046310625570294214034823 222069465938355441321052235)
              ·
                refine ⟨333104198907533161981578353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222069465938355441321052235 333104198907533161981578353)
                ·
                  refine ⟨249828149180649871486183765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 333104198907533161981578353 249828149180649871486183765)
                  ·
                    refine ⟨731918405802685170369679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 249828149180649871486183765 731918405802685170369679)
                    ·
                      rfl

theorem cell23_4276218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_4276218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276218 prefixEnd_4276218 := by exact prefixLift 4276218
  have htrace : WordTrace (prefixWord ++ tailWord_4276218) baseStart_4276218 baseEnd_4276218 := by
    simpa [prefixWord, tailWord_4276218, baseEnd_4276218] using wordTrace_append hprefix tailTrace_4276218
  have hstable : (prefixWord ++ tailWord_4276218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276218).length < 2 ^ (prefixWord ++ tailWord_4276218).sum := by decide
  have hdescent : baseEnd_4276218 < baseStart_4276218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276219 : List Nat := [1, 1, 1, 1, 1, 3, 6, 4, 1, 1, 3]
def baseStart_4276219 : Nat := 118140960795 + 4276219 * 2 ^ 59
def prefixEnd_4276219 : Nat := 4983230072969 + 3 ^ 40 * 4276219 * 2
def baseEnd_4276219 : Nat := 2195755730888710007196533

theorem tailTrace_4276219 : CollatzResearch.WordTrace tailWord_4276219 prefixEnd_4276219 2195755730888710007196533 := by
  unfold tailWord_4276219
  simp only [CollatzResearch.WordTrace]
  refine ⟨155966520094996357906559711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103977680063330905271039807 155966520094996357906559711)
  ·
    refine ⟨233949780142494536859839567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155966520094996357906559711 233949780142494536859839567)
    ·
      refine ⟨350924670213741805289759351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233949780142494536859839567 350924670213741805289759351)
      ·
        refine ⟨526387005320612707934639027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350924670213741805289759351 526387005320612707934639027)
        ·
          refine ⟨789580507980919061901958541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 526387005320612707934639027 789580507980919061901958541)
          ·
            refine ⟨296092690492844648213234453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 789580507980919061901958541 296092690492844648213234453)
            ·
              refine ⟨13879344866852092884995365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 296092690492844648213234453 13879344866852092884995365)
              ·
                refine ⟨2602377162534767415936631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13879344866852092884995365 2602377162534767415936631)
                ·
                  refine ⟨3903565743802151123904947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2602377162534767415936631 3903565743802151123904947)
                  ·
                    refine ⟨5855348615703226685857421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3903565743802151123904947 5855348615703226685857421)
                    ·
                      refine ⟨2195755730888710007196533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5855348615703226685857421 2195755730888710007196533)
                      ·
                        rfl

theorem cell23_4276219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 1, 1, 3].length) (baseStart_4276219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276219 prefixEnd_4276219 := by exact prefixLift 4276219
  have htrace : WordTrace (prefixWord ++ tailWord_4276219) baseStart_4276219 baseEnd_4276219 := by
    simpa [prefixWord, tailWord_4276219, baseEnd_4276219] using wordTrace_append hprefix tailTrace_4276219
  have hstable : (prefixWord ++ tailWord_4276219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276219).length < 2 ^ (prefixWord ++ tailWord_4276219).sum := by decide
  have hdescent : baseEnd_4276219 < baseStart_4276219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276252 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 4, 4]
def baseStart_4276252 : Nat := 118140960795 + 4276252 * 2 ^ 59
def prefixEnd_4276252 : Nat := 4983230072969 + 3 ^ 40 * 4276252 * 2
def baseEnd_4276252 : Nat := 731924225250102792694627

theorem tailTrace_4276252 : CollatzResearch.WordTrace tailWord_4276252 prefixEnd_4276252 731924225250102792694627 := by
  unfold tailWord_4276252
  simp only [CollatzResearch.WordTrace]
  refine ⟨77983861851938402271255505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103978482469251203028340673 77983861851938402271255505)
  ·
    refine ⟨58487896388953801703441629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77983861851938402271255505 58487896388953801703441629)
    ·
      refine ⟨21932961145857675638790611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58487896388953801703441629 21932961145857675638790611)
      ·
        refine ⟨32899441718786513458185917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21932961145857675638790611 32899441718786513458185917)
        ·
          refine ⟨12337290644544942546819719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32899441718786513458185917 12337290644544942546819719)
          ·
            refine ⟨18505935966817413820229579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12337290644544942546819719 18505935966817413820229579)
            ·
              refine ⟨27758903950226120730344369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18505935966817413820229579 27758903950226120730344369)
              ·
                refine ⟨20819177962669590547758277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27758903950226120730344369 20819177962669590547758277)
                ·
                  refine ⟨3903595868000548227704677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20819177962669590547758277 3903595868000548227704677)
                  ·
                    refine ⟨731924225250102792694627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3903595868000548227704677 731924225250102792694627)
                    ·
                      rfl

theorem cell23_4276252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_4276252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276252 prefixEnd_4276252 := by exact prefixLift 4276252
  have htrace : WordTrace (prefixWord ++ tailWord_4276252) baseStart_4276252 baseEnd_4276252 := by
    simpa [prefixWord, tailWord_4276252, baseEnd_4276252] using wordTrace_append hprefix tailTrace_4276252
  have hstable : (prefixWord ++ tailWord_4276252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276252).length < 2 ^ (prefixWord ++ tailWord_4276252).sum := by decide
  have hdescent : baseEnd_4276252 < baseStart_4276252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276253 : List Nat := [1, 4, 2, 2, 2, 3, 1, 3, 1, 1, 3]
def baseStart_4276253 : Nat := 118140960795 + 4276253 * 2 ^ 59
def prefixEnd_4276253 : Nat := 4983230072969 + 3 ^ 40 * 4276253 * 2
def baseEnd_4276253 : Nat := 2195773189230962874171377

theorem tailTrace_4276253 : CollatzResearch.WordTrace tailWord_4276253 prefixEnd_4276253 2195773189230962874171377 := by
  unfold tailWord_4276253
  simp only [CollatzResearch.WordTrace]
  refine ⟨155967760176873181713297413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103978506784582121142198275 155967760176873181713297413)
  ·
    refine ⟨29243955033163721571243265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155967760176873181713297413 29243955033163721571243265)
    ·
      refine ⟨21932966274872791178432449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29243955033163721571243265 21932966274872791178432449)
      ·
        refine ⟨16449724706154593383824337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21932966274872791178432449 16449724706154593383824337)
        ·
          refine ⟨12337293529615945037868253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16449724706154593383824337 12337293529615945037868253)
          ·
            refine ⟨4626485073605979389200595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12337293529615945037868253 4626485073605979389200595)
            ·
              refine ⟨6939727610408969083800893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4626485073605979389200595 6939727610408969083800893)
              ·
                refine ⟨2602397853903363406425335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6939727610408969083800893 2602397853903363406425335)
                ·
                  refine ⟨3903596780855045109638003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2602397853903363406425335 3903596780855045109638003)
                  ·
                    refine ⟨5855395171282567664457005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3903596780855045109638003 5855395171282567664457005)
                    ·
                      refine ⟨2195773189230962874171377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5855395171282567664457005 2195773189230962874171377)
                      ·
                        rfl

theorem cell23_4276253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_4276253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276253 prefixEnd_4276253 := by exact prefixLift 4276253
  have htrace : WordTrace (prefixWord ++ tailWord_4276253) baseStart_4276253 baseEnd_4276253 := by
    simpa [prefixWord, tailWord_4276253, baseEnd_4276253] using wordTrace_append hprefix tailTrace_4276253
  have hstable : (prefixWord ++ tailWord_4276253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276253).length < 2 ^ (prefixWord ++ tailWord_4276253).sum := by decide
  have hdescent : baseEnd_4276253 < baseStart_4276253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276255 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 4]
def baseStart_4276255 : Nat := 118140960795 + 4276255 * 2 ^ 59
def prefixEnd_4276255 : Nat := 4983230072969 + 3 ^ 40 * 4276255 * 2
def baseEnd_4276255 : Nat := 2195774216192271866346367

theorem tailTrace_4276255 : CollatzResearch.WordTrace tailWord_4276255 prefixEnd_4276255 2195774216192271866346367 := by
  unfold tailWord_4276255
  simp only [CollatzResearch.WordTrace]
  refine ⟨155967833122865936054870219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103978555415243957369913479 155967833122865936054870219)
  ·
    refine ⟨233951749684298904082305329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155967833122865936054870219 233951749684298904082305329)
    ·
      refine ⟨175463812263224178061728997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233951749684298904082305329 175463812263224178061728997)
      ·
        refine ⟨32899464799354533386574187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 175463812263224178061728997 32899464799354533386574187)
        ·
          refine ⟨49349197199031800079861281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32899464799354533386574187 49349197199031800079861281)
          ·
            refine ⟨37011897899273850059895961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49349197199031800079861281 37011897899273850059895961)
            ·
              refine ⟨27758923424455387544921971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37011897899273850059895961 27758923424455387544921971)
              ·
                refine ⟨41638385136683081317382957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27758923424455387544921971 41638385136683081317382957)
                ·
                  refine ⟨15614394426256155494018609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41638385136683081317382957 15614394426256155494018609)
                  ·
                    refine ⟨11710795819692116620513957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15614394426256155494018609 11710795819692116620513957)
                    ·
                      refine ⟨2195774216192271866346367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11710795819692116620513957 2195774216192271866346367)
                      ·
                        rfl

theorem cell23_4276255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_4276255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276255 prefixEnd_4276255 := by exact prefixLift 4276255
  have htrace : WordTrace (prefixWord ++ tailWord_4276255) baseStart_4276255 baseEnd_4276255 := by
    simpa [prefixWord, tailWord_4276255, baseEnd_4276255] using wordTrace_append hprefix tailTrace_4276255
  have hstable : (prefixWord ++ tailWord_4276255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276255).length < 2 ^ (prefixWord ++ tailWord_4276255).sum := by decide
  have hdescent : baseEnd_4276255 < baseStart_4276255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276285 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_4276285 : Nat := 118140960795 + 4276285 * 2 ^ 59
def prefixEnd_4276285 : Nat := 4983230072969 + 3 ^ 40 * 4276285 * 2
def baseEnd_4276285 : Nat := 2195789620611906748971229

theorem tailTrace_4276285 : CollatzResearch.WordTrace tailWord_4276285 prefixEnd_4276285 2195789620611906748971229 := by
  unfold tailWord_4276285
  simp only [CollatzResearch.WordTrace]
  refine ⟨155968927312757251178462309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103979284875171500785641539 155968927312757251178462309)
  ·
    refine ⟨29244173871141984595961683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155968927312757251178462309 29244173871141984595961683)
    ·
      refine ⟨43866260806712976893942525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29244173871141984595961683 43866260806712976893942525)
      ·
        refine ⟨16449847802517366335228447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43866260806712976893942525 16449847802517366335228447)
        ·
          refine ⟨24674771703776049502842671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16449847802517366335228447 24674771703776049502842671)
          ·
            refine ⟨37012157555664074254264007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24674771703776049502842671 37012157555664074254264007)
            ·
              refine ⟨55518236333496111381396011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37012157555664074254264007 55518236333496111381396011)
              ·
                refine ⟨83277354500244167072094017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55518236333496111381396011 83277354500244167072094017)
                ·
                  refine ⟨62458015875183125304070513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83277354500244167072094017 62458015875183125304070513)
                  ·
                    refine ⟨46843511906387343978052885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62458015875183125304070513 46843511906387343978052885)
                    ·
                      refine ⟨2195789620611906748971229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46843511906387343978052885 2195789620611906748971229)
                      ·
                        rfl

theorem cell23_4276285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_4276285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276285 prefixEnd_4276285 := by exact prefixLift 4276285
  have htrace : WordTrace (prefixWord ++ tailWord_4276285) baseStart_4276285 baseEnd_4276285 := by
    simpa [prefixWord, tailWord_4276285, baseEnd_4276285] using wordTrace_append hprefix tailTrace_4276285
  have hstable : (prefixWord ++ tailWord_4276285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276285).length < 2 ^ (prefixWord ++ tailWord_4276285).sum := by decide
  have hdescent : baseEnd_4276285 < baseStart_4276285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276286 : List Nat := [4, 2, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_4276286 : Nat := 118140960795 + 4276286 * 2 ^ 59
def prefixEnd_4276286 : Nat := 4983230072969 + 3 ^ 40 * 4276286 * 2
def baseEnd_4276286 : Nat := 731930044697520415019575

theorem tailTrace_4276286 : CollatzResearch.WordTrace tailWord_4276286 prefixEnd_4276286 731930044697520415019575 := by
  unfold tailWord_4276286
  simp only [CollatzResearch.WordTrace]
  refine ⟨19496120473219203543656089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103979309190502418899499141 19496120473219203543656089)
  ·
    refine ⟨14622090354914402657742067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19496120473219203543656089 14622090354914402657742067)
    ·
      refine ⟨21933135532371603986613101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14622090354914402657742067 21933135532371603986613101)
      ·
        refine ⟨8224925824639351494979913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21933135532371603986613101 8224925824639351494979913)
        ·
          refine ⟨6168694368479513621234935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8224925824639351494979913 6168694368479513621234935)
          ·
            refine ⟨9253041552719270431852403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6168694368479513621234935 9253041552719270431852403)
            ·
              refine ⟨13879562329078905647778605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9253041552719270431852403 13879562329078905647778605)
              ·
                refine ⟨5204835873404589617916977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13879562329078905647778605 5204835873404589617916977)
                ·
                  refine ⟨3903626905053442213437733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5204835873404589617916977 3903626905053442213437733)
                  ·
                    refine ⟨731930044697520415019575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3903626905053442213437733 731930044697520415019575)
                    ·
                      rfl

theorem cell23_4276286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_4276286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276286 prefixEnd_4276286 := by exact prefixLift 4276286
  have htrace : WordTrace (prefixWord ++ tailWord_4276286) baseStart_4276286 baseEnd_4276286 := by
    simpa [prefixWord, tailWord_4276286, baseEnd_4276286] using wordTrace_append hprefix tailTrace_4276286
  have hstable : (prefixWord ++ tailWord_4276286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276286).length < 2 ^ (prefixWord ++ tailWord_4276286).sum := by decide
  have hdescent : baseEnd_4276286 < baseStart_4276286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276342 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_4276342 : Nat := 118140960795 + 4276342 * 2 ^ 59
def prefixEnd_4276342 : Nat := 4983230072969 + 3 ^ 40 * 4276342 * 2
def baseEnd_4276342 : Nat := 731939629669737675319489

theorem tailTrace_4276342 : CollatzResearch.WordTrace tailWord_4276342 prefixEnd_4276342 731939629669737675319489 := by
  unfold tailWord_4276342
  simp only [CollatzResearch.WordTrace]
  refine ⟨9748187892096921869580455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103980670849033833275524853 9748187892096921869580455)
  ·
    refine ⟨14622281838145382804370683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9748187892096921869580455 14622281838145382804370683)
    ·
      refine ⟨21933422757218074206556025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14622281838145382804370683 21933422757218074206556025)
      ·
        refine ⟨16450067067913555654917019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21933422757218074206556025 16450067067913555654917019)
        ·
          refine ⟨24675100601870333482375529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16450067067913555654917019 24675100601870333482375529)
          ·
            refine ⟨18506325451402750111781647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24675100601870333482375529 18506325451402750111781647)
            ·
              refine ⟨27759488177104125167672471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18506325451402750111781647 27759488177104125167672471)
              ·
                refine ⟨41639232265656187751508707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27759488177104125167672471 41639232265656187751508707)
                ·
                  refine ⟨62458848398484281627263061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41639232265656187751508707 62458848398484281627263061)
                  ·
                    refine ⟨731939629669737675319489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62458848398484281627263061 731939629669737675319489)
                    ·
                      rfl

theorem cell23_4276342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_4276342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276342 prefixEnd_4276342 := by exact prefixLift 4276342
  have htrace : WordTrace (prefixWord ++ tailWord_4276342) baseStart_4276342 baseEnd_4276342 := by
    simpa [prefixWord, tailWord_4276342, baseEnd_4276342] using wordTrace_append hprefix tailTrace_4276342
  have hstable : (prefixWord ++ tailWord_4276342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276342).length < 2 ^ (prefixWord ++ tailWord_4276342).sum := by decide
  have hdescent : baseEnd_4276342 < baseStart_4276342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276349 : List Nat := [1, 4, 1, 1, 3, 2, 1, 3, 1, 4, 2]
def baseStart_4276349 : Nat := 118140960795 + 4276349 * 2 ^ 59
def prefixEnd_4276349 : Nat := 4983230072969 + 3 ^ 40 * 4276349 * 2
def baseEnd_4276349 : Nat := 2195822483373794498570935

theorem tailTrace_4276349 : CollatzResearch.WordTrace tailWord_4276349 prefixEnd_4276349 2195822483373794498570935 := by
  unfold tailWord_4276349
  simp only [CollatzResearch.WordTrace]
  refine ⟨155971261584525390108792101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103980841056350260072528067 155971261584525390108792101)
  ·
    refine ⟨29244611547098510645398519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155971261584525390108792101 29244611547098510645398519)
    ·
      refine ⟨43866917320647765968097779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29244611547098510645398519 43866917320647765968097779)
      ·
        refine ⟨65800375980971648952146669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43866917320647765968097779 65800375980971648952146669)
        ·
          refine ⟨24675140992864368357055001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65800375980971648952146669 24675140992864368357055001)
          ·
            refine ⟨18506355744648276267791251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24675140992864368357055001 18506355744648276267791251)
            ·
              refine ⟨27759533616972414401686877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18506355744648276267791251 27759533616972414401686877)
              ·
                refine ⟨10409825106364655400632579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27759533616972414401686877 10409825106364655400632579)
                ·
                  refine ⟨15614737659546983100948869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10409825106364655400632579 15614737659546983100948869)
                  ·
                    refine ⟨2927763311165059331427913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15614737659546983100948869 2927763311165059331427913)
                    ·
                      refine ⟨2195822483373794498570935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2927763311165059331427913 2195822483373794498570935)
                      ·
                        rfl

theorem cell23_4276349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_4276349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276349 prefixEnd_4276349 := by exact prefixLift 4276349
  have htrace : WordTrace (prefixWord ++ tailWord_4276349) baseStart_4276349 baseEnd_4276349 := by
    simpa [prefixWord, tailWord_4276349, baseEnd_4276349] using wordTrace_append hprefix tailTrace_4276349
  have hstable : (prefixWord ++ tailWord_4276349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276349).length < 2 ^ (prefixWord ++ tailWord_4276349).sum := by decide
  have hdescent : baseEnd_4276349 < baseStart_4276349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276355 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 9]
def baseStart_4276355 : Nat := 118140960795 + 4276355 * 2 ^ 59
def prefixEnd_4276355 : Nat := 4983230072969 + 3 ^ 40 * 4276355 * 2
def baseEnd_4276355 : Nat := 243980618250857941677323

theorem tailTrace_4276355 : CollatzResearch.WordTrace tailWord_4276355 prefixEnd_4276355 243980618250857941677323 := by
  unfold tailWord_4276355
  simp only [CollatzResearch.WordTrace]
  refine ⟨155971480422503653133510519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103980986948335768755673679 155971480422503653133510519)
  ·
    refine ⟨233957220633755479700265779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155971480422503653133510519 233957220633755479700265779)
    ·
      refine ⟨350935830950633219550398669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233957220633755479700265779 350935830950633219550398669)
      ·
        refine ⟨131600936606487457331399501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 350935830950633219550398669 131600936606487457331399501)
        ·
          refine ⟨49350351227432796499274813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131600936606487457331399501 49350351227432796499274813)
          ·
            refine ⟨18506381710287298687228055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49350351227432796499274813 18506381710287298687228055)
            ·
              refine ⟨27759572565430948030842083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18506381710287298687228055 27759572565430948030842083)
              ·
                refine ⟨41639358848146422046263125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27759572565430948030842083 41639358848146422046263125)
                ·
                  refine ⟨243980618250857941677323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41639358848146422046263125 243980618250857941677323)
                  ·
                    rfl

theorem cell23_4276355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 9].length) (baseStart_4276355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276355 prefixEnd_4276355 := by exact prefixLift 4276355
  have htrace : WordTrace (prefixWord ++ tailWord_4276355) baseStart_4276355 baseEnd_4276355 := by
    simpa [prefixWord, tailWord_4276355, baseEnd_4276355] using wordTrace_append hprefix tailTrace_4276355
  have hstable : (prefixWord ++ tailWord_4276355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276355).length < 2 ^ (prefixWord ++ tailWord_4276355).sum := by decide
  have hdescent : baseEnd_4276355 < baseStart_4276355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276383 : List Nat := [1, 1, 2, 6, 1, 1, 3, 2, 2, 2, 2]
def baseStart_4276383 : Nat := 118140960795 + 4276383 * 2 ^ 59
def prefixEnd_4276383 : Nat := 4983230072969 + 3 ^ 40 * 4276383 * 2
def baseEnd_4276383 : Nat := 2195839941716047365545779

theorem tailTrace_4276383 : CollatzResearch.WordTrace tailWord_4276383 prefixEnd_4276383 2195839941716047365545779 := by
  unfold tailWord_4276383
  simp only [CollatzResearch.WordTrace]
  refine ⟨155972501666402213915529803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103981667777601475943686535 155972501666402213915529803)
  ·
    refine ⟨233958752499603320873294705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155972501666402213915529803 233958752499603320873294705)
    ·
      refine ⟨175469064374702490654971029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233958752499603320873294705 175469064374702490654971029)
      ·
        refine ⟨8225112392564179249451767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 175469064374702490654971029 8225112392564179249451767)
        ·
          refine ⟨12337668588846268874177651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8225112392564179249451767 12337668588846268874177651)
          ·
            refine ⟨18506502883269403311266477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12337668588846268874177651 18506502883269403311266477)
            ·
              refine ⟨6939938581226026241724929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18506502883269403311266477 6939938581226026241724929)
              ·
                refine ⟨5204953935919519681293697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6939938581226026241724929 5204953935919519681293697)
                ·
                  refine ⟨3903715451939639760970273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5204953935919519681293697 3903715451939639760970273)
                  ·
                    refine ⟨2927786588954729820727705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3903715451939639760970273 2927786588954729820727705)
                    ·
                      refine ⟨2195839941716047365545779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2927786588954729820727705 2195839941716047365545779)
                      ·
                        rfl

theorem cell23_4276383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_4276383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276383 prefixEnd_4276383 := by exact prefixLift 4276383
  have htrace : WordTrace (prefixWord ++ tailWord_4276383) baseStart_4276383 baseEnd_4276383 := by
    simpa [prefixWord, tailWord_4276383, baseEnd_4276383] using wordTrace_append hprefix tailTrace_4276383
  have hstable : (prefixWord ++ tailWord_4276383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276383).length < 2 ^ (prefixWord ++ tailWord_4276383).sum := by decide
  have hdescent : baseEnd_4276383 < baseStart_4276383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276395 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 5]
def baseStart_4276395 : Nat := 118140960795 + 4276395 * 2 ^ 59
def prefixEnd_4276395 : Nat := 4983230072969 + 3 ^ 40 * 4276395 * 2
def baseEnd_4276395 : Nat := 2195846103483901318595723

theorem tailTrace_4276395 : CollatzResearch.WordTrace tailWord_4276395 prefixEnd_4276395 2195846103483901318595723 := by
  unfold tailWord_4276395
  simp only [CollatzResearch.WordTrace]
  refine ⟨155972939342358739964966639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103981959561572493309977759 155972939342358739964966639)
  ·
    refine ⟨233959409013538109947449959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155972939342358739964966639 233959409013538109947449959)
    ·
      refine ⟨350939113520307164921174939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233959409013538109947449959 350939113520307164921174939)
      ·
        refine ⟨526408670280460747381762409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350939113520307164921174939 526408670280460747381762409)
        ·
          refine ⟨394806502710345560536321807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 526408670280460747381762409 394806502710345560536321807)
          ·
            refine ⟨592209754065518340804482711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394806502710345560536321807 592209754065518340804482711)
            ·
              refine ⟨888314631098277511206724067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592209754065518340804482711 888314631098277511206724067)
              ·
                refine ⟨1332471946647416266810086101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 888314631098277511206724067 1332471946647416266810086101)
                ·
                  refine ⟨31229811249548818753361393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1332471946647416266810086101 31229811249548818753361393)
                  ·
                    refine ⟨23422358437161614065021045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31229811249548818753361393 23422358437161614065021045)
                    ·
                      refine ⟨2195846103483901318595723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23422358437161614065021045 2195846103483901318595723)
                      ·
                        rfl

theorem cell23_4276395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 5].length) (baseStart_4276395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276395 prefixEnd_4276395 := by exact prefixLift 4276395
  have htrace : WordTrace (prefixWord ++ tailWord_4276395) baseStart_4276395 baseEnd_4276395 := by
    simpa [prefixWord, tailWord_4276395, baseEnd_4276395] using wordTrace_append hprefix tailTrace_4276395
  have hstable : (prefixWord ++ tailWord_4276395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276395).length < 2 ^ (prefixWord ++ tailWord_4276395).sum := by decide
  have hdescent : baseEnd_4276395 < baseStart_4276395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276415 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 1, 10]
def baseStart_4276415 : Nat := 118140960795 + 4276415 * 2 ^ 59
def prefixEnd_4276415 : Nat := 4983230072969 + 3 ^ 40 * 4276415 * 2
def baseEnd_4276415 : Nat := 731952124365663746781877

theorem tailTrace_4276415 : CollatzResearch.WordTrace tailWord_4276415 prefixEnd_4276415 731952124365663746781877 := by
  unfold tailWord_4276415
  simp only [CollatzResearch.WordTrace]
  refine ⟨155973668802286283380694699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103982445868190855587129799 155973668802286283380694699)
  ·
    refine ⟨233960503203429425071042049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155973668802286283380694699 233960503203429425071042049)
    ·
      refine ⟨175470377402572068803281537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233960503203429425071042049 175470377402572068803281537)
      ·
        refine ⟨131602783051929051602461153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175470377402572068803281537 131602783051929051602461153)
        ·
          refine ⟨98702087288946788701845865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131602783051929051602461153 98702087288946788701845865)
          ·
            refine ⟨74026565466710091526384399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98702087288946788701845865 74026565466710091526384399)
            ·
              refine ⟨111039848200065137289576599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74026565466710091526384399 111039848200065137289576599)
              ·
                refine ⟨166559772300097705934364899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111039848200065137289576599 166559772300097705934364899)
                ·
                  refine ⟨249839658450146558901547349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166559772300097705934364899 249839658450146558901547349)
                  ·
                    refine ⟨731952124365663746781877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 249839658450146558901547349 731952124365663746781877)
                    ·
                      rfl

theorem cell23_4276415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 10].length) (baseStart_4276415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276415 prefixEnd_4276415 := by exact prefixLift 4276415
  have htrace : WordTrace (prefixWord ++ tailWord_4276415) baseStart_4276415 baseEnd_4276415 := by
    simpa [prefixWord, tailWord_4276415, baseEnd_4276415] using wordTrace_append hprefix tailTrace_4276415
  have hstable : (prefixWord ++ tailWord_4276415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276415).length < 2 ^ (prefixWord ++ tailWord_4276415).sum := by decide
  have hdescent : baseEnd_4276415 < baseStart_4276415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276472 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 2, 5, 3]
def baseStart_4276472 : Nat := 118140960795 + 4276472 * 2 ^ 59
def prefixEnd_4276472 : Nat := 4983230072969 + 3 ^ 40 * 4276472 * 2
def baseEnd_4276472 : Nat := 2195885641494297517332869

theorem tailTrace_4276472 : CollatzResearch.WordTrace tailWord_4276472 prefixEnd_4276472 2195885641494297517332869 := by
  unfold tailWord_4276472
  simp only [CollatzResearch.WordTrace]
  refine ⟨77987873881539891057759835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103983831842053188077013113 77987873881539891057759835)
  ·
    refine ⟨116981810822309836586639753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77987873881539891057759835 116981810822309836586639753)
    ·
      refine ⟨87736358116732377439979815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116981810822309836586639753 87736358116732377439979815)
      ·
        refine ⟨131604537175098566159969723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87736358116732377439979815 131604537175098566159969723)
        ·
          refine ⟨197406805762647849239954585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131604537175098566159969723 197406805762647849239954585)
          ·
            refine ⟨148055104321985886929965939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197406805762647849239954585 148055104321985886929965939)
            ·
              refine ⟨222082656482978830394948909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148055104321985886929965939 222082656482978830394948909)
              ·
                refine ⟨83280996181117061398105841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222082656482978830394948909 83280996181117061398105841)
                ·
                  refine ⟨62460747135837796048579381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83280996181117061398105841 62460747135837796048579381)
                  ·
                    refine ⟨5855695043984793379554317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62460747135837796048579381 5855695043984793379554317)
                    ·
                      refine ⟨2195885641494297517332869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5855695043984793379554317 2195885641494297517332869)
                      ·
                        rfl

theorem cell23_4276472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_4276472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276472 prefixEnd_4276472 := by exact prefixLift 4276472
  have htrace : WordTrace (prefixWord ++ tailWord_4276472) baseStart_4276472 baseEnd_4276472 := by
    simpa [prefixWord, tailWord_4276472, baseEnd_4276472] using wordTrace_append hprefix tailTrace_4276472
  have hstable : (prefixWord ++ tailWord_4276472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276472).length < 2 ^ (prefixWord ++ tailWord_4276472).sum := by decide
  have hdescent : baseEnd_4276472 < baseStart_4276472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276476 : List Nat := [2, 2, 2, 1, 4, 2, 2, 1, 2, 2, 3]
def baseStart_4276476 : Nat := 118140960795 + 4276476 * 2 ^ 59
def prefixEnd_4276476 : Nat := 4983230072969 + 3 ^ 40 * 4276476 * 2
def baseEnd_4276476 : Nat := 2195887695416915501682851

theorem tailTrace_4276476 : CollatzResearch.WordTrace tailWord_4276476 prefixEnd_4276476 2195887695416915501682851 := by
  unfold tailWord_4276476
  simp only [CollatzResearch.WordTrace]
  refine ⟨77987946827532645399332641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103983929103376860532443521 77987946827532645399332641)
  ·
    refine ⟨58490960120649484049499481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77987946827532645399332641 58490960120649484049499481)
    ·
      refine ⟨43868220090487113037124611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58490960120649484049499481 43868220090487113037124611)
      ·
        refine ⟨65802330135730669555686917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43868220090487113037124611 65802330135730669555686917)
        ·
          refine ⟨12337936900449500541691297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65802330135730669555686917 12337936900449500541691297)
          ·
            refine ⟨9253452675337125406268473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12337936900449500541691297 9253452675337125406268473)
            ·
              refine ⟨6940089506502844054701355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9253452675337125406268473 6940089506502844054701355)
              ·
                refine ⟨10410134259754266082052033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6940089506502844054701355 10410134259754266082052033)
                ·
                  refine ⟨7807600694815699561539025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10410134259754266082052033 7807600694815699561539025)
                  ·
                    refine ⟨5855700521111774671154269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7807600694815699561539025 5855700521111774671154269)
                    ·
                      refine ⟨2195887695416915501682851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5855700521111774671154269 2195887695416915501682851)
                      ·
                        rfl

theorem cell23_4276476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_4276476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276476 prefixEnd_4276476 := by exact prefixLift 4276476
  have htrace : WordTrace (prefixWord ++ tailWord_4276476) baseStart_4276476 baseEnd_4276476 := by
    simpa [prefixWord, tailWord_4276476, baseEnd_4276476] using wordTrace_append hprefix tailTrace_4276476
  have hstable : (prefixWord ++ tailWord_4276476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276476).length < 2 ^ (prefixWord ++ tailWord_4276476).sum := by decide
  have hdescent : baseEnd_4276476 < baseStart_4276476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276583 : List Nat := [1, 1, 5, 1, 3, 2, 2, 2, 1, 2, 3]
def baseStart_4276583 : Nat := 118140960795 + 4276583 * 2 ^ 59
def prefixEnd_4276583 : Nat := 4983230072969 + 3 ^ 40 * 4276583 * 2
def baseEnd_4276583 : Nat := 2195942637846946583044859

theorem tailTrace_4276583 : CollatzResearch.WordTrace tailWord_4276583 prefixEnd_4276583 2195942637846946583044859 := by
  unfold tailWord_4276583
  simp only [CollatzResearch.WordTrace]
  refine ⟨155979796265677648072810403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103986530843785098715206935 155979796265677648072810403)
  ·
    refine ⟨233969694398516472109215605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155979796265677648072810403 233969694398516472109215605)
    ·
      refine ⟨21934658849860919260238963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 233969694398516472109215605 21934658849860919260238963)
      ·
        refine ⟨32901988274791378890358445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21934658849860919260238963 32901988274791378890358445)
        ·
          refine ⟨12338245603046767083884417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32901988274791378890358445 12338245603046767083884417)
          ·
            refine ⟨9253684202285075312913313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12338245603046767083884417 9253684202285075312913313)
            ·
              refine ⟨6940263151713806484684985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9253684202285075312913313 6940263151713806484684985)
              ·
                refine ⟨5205197363785354863513739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6940263151713806484684985 5205197363785354863513739)
                ·
                  refine ⟨7807796045678032295270609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5205197363785354863513739 7807796045678032295270609)
                  ·
                    refine ⟨5855847034258524221452957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7807796045678032295270609 5855847034258524221452957)
                    ·
                      refine ⟨2195942637846946583044859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5855847034258524221452957 2195942637846946583044859)
                      ·
                        rfl

theorem cell23_4276583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_4276583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276583 prefixEnd_4276583 := by exact prefixLift 4276583
  have htrace : WordTrace (prefixWord ++ tailWord_4276583) baseStart_4276583 baseEnd_4276583 := by
    simpa [prefixWord, tailWord_4276583, baseEnd_4276583] using wordTrace_append hprefix tailTrace_4276583
  have hstable : (prefixWord ++ tailWord_4276583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276583).length < 2 ^ (prefixWord ++ tailWord_4276583).sum := by decide
  have hdescent : baseEnd_4276583 < baseStart_4276583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276586 : List Nat := [3, 1, 3, 3, 1, 1, 4, 7]
def baseStart_4276586 : Nat := 118140960795 + 4276586 * 2 ^ 59
def prefixEnd_4276586 : Nat := 4983230072969 + 3 ^ 40 * 4276586 * 2
def baseEnd_4276586 : Nat := 81331265862552224863235

theorem tailTrace_4276586 : CollatzResearch.WordTrace tailWord_4276586 prefixEnd_4276586 81331265862552224863235 := by
  unfold tailWord_4276586
  simp only [CollatzResearch.WordTrace]
  refine ⟨38994976421166694896292403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103986603789777853056779741 38994976421166694896292403)
  ·
    refine ⟨58492464631750042344438605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38994976421166694896292403 58492464631750042344438605)
    ·
      refine ⟨21934674236906265879164477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58492464631750042344438605 21934674236906265879164477)
      ·
        refine ⟨8225502838839849704686679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21934674236906265879164477 8225502838839849704686679)
        ·
          refine ⟨12338254258259774557030019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8225502838839849704686679 12338254258259774557030019)
          ·
            refine ⟨18507381387389661835545029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12338254258259774557030019 18507381387389661835545029)
            ·
              refine ⟨3470134010135561594164693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18507381387389661835545029 3470134010135561594164693)
              ·
                refine ⟨81331265862552224863235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3470134010135561594164693 81331265862552224863235)
                ·
                  rfl

theorem cell23_4276586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 7].length) (baseStart_4276586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276586 prefixEnd_4276586 := by exact prefixLift 4276586
  have htrace : WordTrace (prefixWord ++ tailWord_4276586) baseStart_4276586 baseEnd_4276586 := by
    simpa [prefixWord, tailWord_4276586, baseEnd_4276586] using wordTrace_append hprefix tailTrace_4276586
  have hstable : (prefixWord ++ tailWord_4276586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276586).length < 2 ^ (prefixWord ++ tailWord_4276586).sum := by decide
  have hdescent : baseEnd_4276586 < baseStart_4276586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276597 : List Nat := [1, 3, 4, 1, 2, 1, 3, 3, 1, 2, 2]
def baseStart_4276597 : Nat := 118140960795 + 4276597 * 2 ^ 59
def prefixEnd_4276597 : Nat := 4983230072969 + 3 ^ 40 * 4276597 * 2
def baseEnd_4276597 : Nat := 2195949826576109528269795

theorem tailTrace_4276597 : CollatzResearch.WordTrace tailWord_4276597 prefixEnd_4276597 2195949826576109528269795 := by
  unfold tailWord_4276597
  simp only [CollatzResearch.WordTrace]
  refine ⟨155980306887626928463820045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103986871258417952309213363 155980306887626928463820045)
  ·
    refine ⟨58492615082860098173932517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155980306887626928463820045 58492615082860098173932517)
    ·
      refine ⟨10967365328036268407612347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58492615082860098173932517 10967365328036268407612347)
      ·
        refine ⟨16451047992054402611418521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10967365328036268407612347 16451047992054402611418521)
        ·
          refine ⟨12338285994040801958563891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16451047992054402611418521 12338285994040801958563891)
          ·
            refine ⟨18507428991061202937845837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12338285994040801958563891 18507428991061202937845837)
            ·
              refine ⟨6940285871647951101692189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18507428991061202937845837 6940285871647951101692189)
              ·
                refine ⟨2602607201867981663134571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6940285871647951101692189 2602607201867981663134571)
                ·
                  refine ⟨3903910802801972494701857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2602607201867981663134571 3903910802801972494701857)
                  ·
                    refine ⟨2927933102101479371026393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3903910802801972494701857 2927933102101479371026393)
                    ·
                      refine ⟨2195949826576109528269795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2927933102101479371026393 2195949826576109528269795)
                      ·
                        rfl

theorem cell23_4276597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_4276597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276597 prefixEnd_4276597 := by exact prefixLift 4276597
  have htrace : WordTrace (prefixWord ++ tailWord_4276597) baseStart_4276597 baseEnd_4276597 := by
    simpa [prefixWord, tailWord_4276597, baseEnd_4276597] using wordTrace_append hprefix tailTrace_4276597
  have hstable : (prefixWord ++ tailWord_4276597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276597).length < 2 ^ (prefixWord ++ tailWord_4276597).sum := by decide
  have hdescent : baseEnd_4276597 < baseStart_4276597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276639 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 5]
def baseStart_4276639 : Nat := 118140960795 + 4276639 * 2 ^ 59
def prefixEnd_4276639 : Nat := 4983230072969 + 3 ^ 40 * 4276639 * 2
def baseEnd_4276639 : Nat := 2195971392763598363944601

theorem tailTrace_4276639 : CollatzResearch.WordTrace tailWord_4276639 prefixEnd_4276639 2195971392763598363944601 := by
  unfold tailWord_4276639
  simp only [CollatzResearch.WordTrace]
  refine ⟨155981838753474769636848971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103987892502316513091232647 155981838753474769636848971)
  ·
    refine ⟨233972758130212154455273457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155981838753474769636848971 233972758130212154455273457)
    ·
      refine ⟨175479568597659115841455093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233972758130212154455273457 175479568597659115841455093)
      ·
        refine ⟨16451209556030542110136415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 175479568597659115841455093 16451209556030542110136415)
        ·
          refine ⟨24676814334045813165204623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16451209556030542110136415 24676814334045813165204623)
          ·
            refine ⟨37015221501068719747806935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24676814334045813165204623 37015221501068719747806935)
            ·
              refine ⟨55522832251603079621710403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37015221501068719747806935 55522832251603079621710403)
              ·
                refine ⟨83284248377404619432565605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55522832251603079621710403 83284248377404619432565605)
                ·
                  refine ⟨15615796570763366143606051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83284248377404619432565605 15615796570763366143606051)
                  ·
                    refine ⟨23423694856145049215409077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15615796570763366143606051 23423694856145049215409077)
                    ·
                      refine ⟨2195971392763598363944601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23423694856145049215409077 2195971392763598363944601)
                      ·
                        rfl

theorem cell23_4276639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_4276639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276639 prefixEnd_4276639 := by exact prefixLift 4276639
  have htrace : WordTrace (prefixWord ++ tailWord_4276639) baseStart_4276639 baseEnd_4276639 := by
    simpa [prefixWord, tailWord_4276639, baseEnd_4276639] using wordTrace_append hprefix tailTrace_4276639
  have hstable : (prefixWord ++ tailWord_4276639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276639).length < 2 ^ (prefixWord ++ tailWord_4276639).sum := by decide
  have hdescent : baseEnd_4276639 < baseStart_4276639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276640 : List Nat := [2, 1, 1, 4, 1, 5, 1, 2, 1, 3, 2]
def baseStart_4276640 : Nat := 118140960795 + 4276640 * 2 ^ 59
def prefixEnd_4276640 : Nat := 4983230072969 + 3 ^ 40 * 4276640 * 2
def baseEnd_4276640 : Nat := 2195971906244252860032097

theorem tailTrace_4276640 : CollatzResearch.WordTrace tailWord_4276640 prefixEnd_4276640 2195971906244252860032097 := by
  unfold tailWord_4276640
  simp only [CollatzResearch.WordTrace]
  refine ⟨77990937613235573403817687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103987916817647431205090249 77990937613235573403817687)
  ·
    refine ⟨116986406419853360105726531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77990937613235573403817687 116986406419853360105726531)
    ·
      refine ⟨175479609629780040158589797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116986406419853360105726531 175479609629780040158589797)
      ·
        refine ⟨32902426805583757529735587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 175479609629780040158589797 32902426805583757529735587)
        ·
          refine ⟨49353640208375636294603381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32902426805583757529735587 49353640208375636294603381)
          ·
            refine ⟨4626903769535215902619067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49353640208375636294603381 4626903769535215902619067)
            ·
              refine ⟨6940355654302823853928601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4626903769535215902619067 6940355654302823853928601)
              ·
                refine ⟨5205266740727117890446451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6940355654302823853928601 5205266740727117890446451)
                ·
                  refine ⟨7807900111090676835669677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5205266740727117890446451 7807900111090676835669677)
                  ·
                    refine ⟨2927962541659003813376129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7807900111090676835669677 2927962541659003813376129)
                    ·
                      refine ⟨2195971906244252860032097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2927962541659003813376129 2195971906244252860032097)
                      ·
                        rfl

theorem cell23_4276640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_4276640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276640 prefixEnd_4276640 := by exact prefixLift 4276640
  have htrace : WordTrace (prefixWord ++ tailWord_4276640) baseStart_4276640 baseEnd_4276640 := by
    simpa [prefixWord, tailWord_4276640, baseEnd_4276640] using wordTrace_append hprefix tailTrace_4276640
  have hstable : (prefixWord ++ tailWord_4276640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276640).length < 2 ^ (prefixWord ++ tailWord_4276640).sum := by decide
  have hdescent : baseEnd_4276640 < baseStart_4276640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276670 : List Nat := [4, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2]
def baseStart_4276670 : Nat := 118140960795 + 4276670 * 2 ^ 59
def prefixEnd_4276670 : Nat := 4983230072969 + 3 ^ 40 * 4276670 * 2
def baseEnd_4276670 : Nat := 2195987310663887742656959

theorem tailTrace_4276670 : CollatzResearch.WordTrace tailWord_4276670 prefixEnd_4276670 2195987310663887742656959 := by
  unfold tailWord_4276670
  simp only [CollatzResearch.WordTrace]
  refine ⟨19497871177045307741403433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103988646277574974620818309 19497871177045307741403433)
  ·
    refine ⟨14623403382783980806052575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19497871177045307741403433 14623403382783980806052575)
    ·
      refine ⟨21935105074175971209078863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14623403382783980806052575 21935105074175971209078863)
      ·
        refine ⟨32902657611263956813618295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21935105074175971209078863 32902657611263956813618295)
        ·
          refine ⟨49353986416895935220427443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32902657611263956813618295 49353986416895935220427443)
          ·
            refine ⟨74030979625343902830641165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49353986416895935220427443 74030979625343902830641165)
            ·
              refine ⟨27761617359503963561490437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74030979625343902830641165 27761617359503963561490437)
              ·
                refine ⟨5205303254906993167779457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27761617359503963561490437 5205303254906993167779457)
                ·
                  refine ⟨3903977441180244875834593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5205303254906993167779457 3903977441180244875834593)
                  ·
                    refine ⟨2927983080885183656875945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3903977441180244875834593 2927983080885183656875945)
                    ·
                      refine ⟨2195987310663887742656959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2927983080885183656875945 2195987310663887742656959)
                      ·
                        rfl

theorem cell23_4276670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_4276670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276670 prefixEnd_4276670 := by exact prefixLift 4276670
  have htrace : WordTrace (prefixWord ++ tailWord_4276670) baseStart_4276670 baseEnd_4276670 := by
    simpa [prefixWord, tailWord_4276670, baseEnd_4276670] using wordTrace_append hprefix tailTrace_4276670
  have hstable : (prefixWord ++ tailWord_4276670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276670).length < 2 ^ (prefixWord ++ tailWord_4276670).sum := by decide
  have hdescent : baseEnd_4276670 < baseStart_4276670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276689 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 4, 5]
def baseStart_4276689 : Nat := 118140960795 + 4276689 * 2 ^ 59
def prefixEnd_4276689 : Nat := 4983230072969 + 3 ^ 40 * 4276689 * 2
def baseEnd_4276689 : Nat := 731999022265441056106457

theorem tailTrace_4276689 : CollatzResearch.WordTrace tailWord_4276689 prefixEnd_4276689 731999022265441056106457 := by
  unfold tailWord_4276689
  simp only [CollatzResearch.WordTrace]
  refine ⟨155983662403293628176169121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103989108268862418784112747 155983662403293628176169121)
  ·
    refine ⟨116987746802470221132126841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155983662403293628176169121 116987746802470221132126841)
    ·
      refine ⟨87740810101852665849095131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116987746802470221132126841 87740810101852665849095131)
      ·
        refine ⟨131611215152778998773642697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87740810101852665849095131 131611215152778998773642697)
        ·
          refine ⟨98708411364584249080232023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131611215152778998773642697 98708411364584249080232023)
          ·
            refine ⟨148062617046876373620348035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98708411364584249080232023 148062617046876373620348035)
            ·
              refine ⟨222093925570314560430522053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148062617046876373620348035 222093925570314560430522053)
              ·
                refine ⟨41642611044433980080722885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 222093925570314560430522053 41642611044433980080722885)
                ·
                  refine ⟨7807989570831371265135541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41642611044433980080722885 7807989570831371265135541)
                  ·
                    refine ⟨731999022265441056106457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7807989570831371265135541 731999022265441056106457)
                    ·
                      rfl

theorem cell23_4276689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_4276689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276689 prefixEnd_4276689 := by exact prefixLift 4276689
  have htrace : WordTrace (prefixWord ++ tailWord_4276689) baseStart_4276689 baseEnd_4276689 := by
    simpa [prefixWord, tailWord_4276689, baseEnd_4276689] using wordTrace_append hprefix tailTrace_4276689
  have hstable : (prefixWord ++ tailWord_4276689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276689).length < 2 ^ (prefixWord ++ tailWord_4276689).sum := by decide
  have hdescent : baseEnd_4276689 < baseStart_4276689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276696 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 4, 5, 2]
def baseStart_4276696 : Nat := 118140960795 + 4276696 * 2 ^ 59
def prefixEnd_4276696 : Nat := 4983230072969 + 3 ^ 40 * 4276696 * 2
def baseEnd_4276696 : Nat := 2196000661160904640931839

theorem tailTrace_4276696 : CollatzResearch.WordTrace tailWord_4276696 prefixEnd_4276696 2196000661160904640931839 := by
  unfold tailWord_4276696
  simp only [CollatzResearch.WordTrace]
  refine ⟨77991958857134134185836971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103989278476178845581115961 77991958857134134185836971)
  ·
    refine ⟨116987938285701201278755457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77991958857134134185836971 116987938285701201278755457)
    ·
      refine ⟨87740953714275900959066593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116987938285701201278755457 87740953714275900959066593)
      ·
        refine ⟨65805715285706925719299945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87740953714275900959066593 65805715285706925719299945)
        ·
          refine ⟨49354286464280194289474959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65805715285706925719299945 49354286464280194289474959)
          ·
            refine ⟨74031429696420291434212439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49354286464280194289474959 74031429696420291434212439)
            ·
              refine ⟨111047144544630437151318659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74031429696420291434212439 111047144544630437151318659)
              ·
                refine ⟨166570716816945655726977989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111047144544630437151318659 166570716816945655726977989)
                ·
                  refine ⟨31232009403177310448808373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 166570716816945655726977989 31232009403177310448808373)
                  ·
                    refine ⟨2928000881547872854575785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31232009403177310448808373 2928000881547872854575785)
                    ·
                      refine ⟨2196000661160904640931839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2928000881547872854575785 2196000661160904640931839)
                      ·
                        rfl

theorem cell23_4276696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_4276696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276696 prefixEnd_4276696 := by exact prefixLift 4276696
  have htrace : WordTrace (prefixWord ++ tailWord_4276696) baseStart_4276696 baseEnd_4276696 := by
    simpa [prefixWord, tailWord_4276696, baseEnd_4276696] using wordTrace_append hprefix tailTrace_4276696
  have hstable : (prefixWord ++ tailWord_4276696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276696).length < 2 ^ (prefixWord ++ tailWord_4276696).sum := by decide
  have hdescent : baseEnd_4276696 < baseStart_4276696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276729 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 2, 3, 5]
def baseStart_4276729 : Nat := 118140960795 + 4276729 * 2 ^ 59
def prefixEnd_4276729 : Nat := 4983230072969 + 3 ^ 40 * 4276729 * 2
def baseEnd_4276729 : Nat := 2196017606022503011819187

theorem tailTrace_4276729 : CollatzResearch.WordTrace tailWord_4276729 prefixEnd_4276729 2196017606022503011819187 := by
  unfold tailWord_4276729
  simp only [CollatzResearch.WordTrace]
  refine ⟨155985121323148715007625241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103990080882099143338416827 155985121323148715007625241)
  ·
    refine ⟨116988840992361536255718931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155985121323148715007625241 116988840992361536255718931)
    ·
      refine ⟨175483261488542304383578397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116988840992361536255718931 175483261488542304383578397)
      ·
        refine ⟨65806223058203364143841899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175483261488542304383578397 65806223058203364143841899)
        ·
          refine ⟨98709334587305046215762849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65806223058203364143841899 98709334587305046215762849)
          ·
            refine ⟨74032000940478784661822137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98709334587305046215762849 74032000940478784661822137)
            ·
              refine ⟨55524000705359088496366603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74032000940478784661822137 55524000705359088496366603)
              ·
                refine ⟨83286001058038632744549905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55524000705359088496366603 83286001058038632744549905)
                ·
                  refine ⟨62464500793528974558412429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83286001058038632744549905 62464500793528974558412429)
                  ·
                    refine ⟨23424187797573365459404661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62464500793528974558412429 23424187797573365459404661)
                    ·
                      refine ⟨2196017606022503011819187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23424187797573365459404661 2196017606022503011819187)
                      ·
                        rfl

theorem cell23_4276729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_4276729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276729 prefixEnd_4276729 := by exact prefixLift 4276729
  have htrace : WordTrace (prefixWord ++ tailWord_4276729) baseStart_4276729 baseEnd_4276729 := by
    simpa [prefixWord, tailWord_4276729, baseEnd_4276729] using wordTrace_append hprefix tailTrace_4276729
  have hstable : (prefixWord ++ tailWord_4276729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276729).length < 2 ^ (prefixWord ++ tailWord_4276729).sum := by decide
  have hdescent : baseEnd_4276729 < baseStart_4276729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276739 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 6]
def baseStart_4276739 : Nat := 118140960795 + 4276739 * 2 ^ 59
def prefixEnd_4276739 : Nat := 4983230072969 + 3 ^ 40 * 4276739 * 2
def baseEnd_4276739 : Nat := 2196022740829047972694141

theorem tailTrace_4276739 : CollatzResearch.WordTrace tailWord_4276739 prefixEnd_4276739 2196022740829047972694141 := by
  unfold tailWord_4276739
  simp only [CollatzResearch.WordTrace]
  refine ⟨155985486053112486715489271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103990324035408324476992847 155985486053112486715489271)
  ·
    refine ⟨233978229079668730073233907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155985486053112486715489271 233978229079668730073233907)
    ·
      refine ⟨350967343619503095109850861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233978229079668730073233907 350967343619503095109850861)
      ·
        refine ⟨131612753857313660666194073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 350967343619503095109850861 131612753857313660666194073)
        ·
          refine ⟨98709565392985245499645555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131612753857313660666194073 98709565392985245499645555)
          ·
            refine ⟨148064348089477868249468333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98709565392985245499645555 148064348089477868249468333)
            ·
              refine ⟨55524130533554200593550625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148064348089477868249468333 55524130533554200593550625)
              ·
                refine ⟨41643097900165650445162969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55524130533554200593550625 41643097900165650445162969)
                ·
                  refine ⟨31232323425124237833872227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41643097900165650445162969 31232323425124237833872227)
                  ·
                    refine ⟨46848485137686356750808341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31232323425124237833872227 46848485137686356750808341)
                    ·
                      refine ⟨2196022740829047972694141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46848485137686356750808341 2196022740829047972694141)
                      ·
                        rfl

theorem cell23_4276739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_4276739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276739 prefixEnd_4276739 := by exact prefixLift 4276739
  have htrace : WordTrace (prefixWord ++ tailWord_4276739) baseStart_4276739 baseEnd_4276739 := by
    simpa [prefixWord, tailWord_4276739, baseEnd_4276739] using wordTrace_append hprefix tailTrace_4276739
  have hstable : (prefixWord ++ tailWord_4276739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276739).length < 2 ^ (prefixWord ++ tailWord_4276739).sum := by decide
  have hdescent : baseEnd_4276739 < baseStart_4276739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276746 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 3, 4, 3]
def baseStart_4276746 : Nat := 118140960795 + 4276746 * 2 ^ 59
def prefixEnd_4276746 : Nat := 4983230072969 + 3 ^ 40 * 4276746 * 2
def baseEnd_4276746 : Nat := 2196026335193629445306609

theorem tailTrace_4276746 : CollatzResearch.WordTrace tailWord_4276746 prefixEnd_4276746 2196026335193629445306609 := by
  unfold tailWord_4276746
  simp only [CollatzResearch.WordTrace]
  refine ⟨38996435341021781727748523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103990494242724751273996061 38996435341021781727748523)
  ·
    refine ⟨58494653011532672591622785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38996435341021781727748523 58494653011532672591622785)
    ·
      refine ⟨43870989758649504443717089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58494653011532672591622785 43870989758649504443717089)
      ·
        refine ⟨32903242318987128332787817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43870989758649504443717089 32903242318987128332787817)
        ·
          refine ⟨24677431739240346249590863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32903242318987128332787817 24677431739240346249590863)
          ·
            refine ⟨37016147608860519374386295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24677431739240346249590863 37016147608860519374386295)
            ·
              refine ⟨55524221413290779061579443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37016147608860519374386295 55524221413290779061579443)
              ·
                refine ⟨83286332119936168592369165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55524221413290779061579443 83286332119936168592369165)
                ·
                  refine ⟨31232374544976063222138437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83286332119936168592369165 31232374544976063222138437)
                  ·
                    refine ⟨5856070227183011854150957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31232374544976063222138437 5856070227183011854150957)
                    ·
                      refine ⟨2196026335193629445306609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5856070227183011854150957 2196026335193629445306609)
                      ·
                        rfl

theorem cell23_4276746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_4276746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276746 prefixEnd_4276746 := by exact prefixLift 4276746
  have htrace : WordTrace (prefixWord ++ tailWord_4276746) baseStart_4276746 baseEnd_4276746 := by
    simpa [prefixWord, tailWord_4276746, baseEnd_4276746] using wordTrace_append hprefix tailTrace_4276746
  have hstable : (prefixWord ++ tailWord_4276746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276746).length < 2 ^ (prefixWord ++ tailWord_4276746).sum := by decide
  have hdescent : baseEnd_4276746 < baseStart_4276746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276820 : List Nat := [2, 4, 1, 1, 1, 3, 1, 3, 2, 3, 2]
def baseStart_4276820 : Nat := 118140960795 + 4276820 * 2 ^ 59
def prefixEnd_4276820 : Nat := 4983230072969 + 3 ^ 40 * 4276820 * 2
def baseEnd_4276820 : Nat := 2196064332762062155781269

theorem tailTrace_4276820 : CollatzResearch.WordTrace tailWord_4276820 prefixEnd_4276820 2196064332762062155781269 := by
  unfold tailWord_4276820
  simp only [CollatzResearch.WordTrace]
  refine ⟨77994220182909518774593957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103992293577212691699458609 77994220182909518774593957)
  ·
    refine ⟨14623916284295534770236367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77994220182909518774593957 14623916284295534770236367)
    ·
      refine ⟨21935874426443302155354551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14623916284295534770236367 21935874426443302155354551)
      ·
        refine ⟨32903811639664953233031827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21935874426443302155354551 32903811639664953233031827)
        ·
          refine ⟨49355717459497429849547741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32903811639664953233031827 49355717459497429849547741)
          ·
            refine ⟨18508394047311536193580403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49355717459497429849547741 18508394047311536193580403)
            ·
              refine ⟨27762591070967304290370605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18508394047311536193580403 27762591070967304290370605)
              ·
                refine ⟨10410971651612739108888977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27762591070967304290370605 10410971651612739108888977)
                ·
                  refine ⟨7808228738709554331666733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10410971651612739108888977 7808228738709554331666733)
                  ·
                    refine ⟨2928085777016082874375025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7808228738709554331666733 2928085777016082874375025)
                    ·
                      refine ⟨2196064332762062155781269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2928085777016082874375025 2196064332762062155781269)
                      ·
                        rfl

theorem cell23_4276820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_4276820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276820 prefixEnd_4276820 := by exact prefixLift 4276820
  have htrace : WordTrace (prefixWord ++ tailWord_4276820) baseStart_4276820 baseEnd_4276820 := by
    simpa [prefixWord, tailWord_4276820, baseEnd_4276820] using wordTrace_append hprefix tailTrace_4276820
  have hstable : (prefixWord ++ tailWord_4276820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276820).length < 2 ^ (prefixWord ++ tailWord_4276820).sum := by decide
  have hdescent : baseEnd_4276820 < baseStart_4276820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276883 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 6, 1, 3]
def baseStart_4276883 : Nat := 118140960795 + 4276883 * 2 ^ 59
def prefixEnd_4276883 : Nat := 4983230072969 + 3 ^ 40 * 4276883 * 2
def baseEnd_4276883 : Nat := 2196096682043295409293479

theorem tailTrace_4276883 : CollatzResearch.WordTrace tailWord_4276883 prefixEnd_4276883 2196096682043295409293479 := by
  unfold tailWord_4276883
  simp only [CollatzResearch.WordTrace]
  refine ⟨155990738164590799308731303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103993825443060532872487535 155990738164590799308731303)
  ·
    refine ⟨233986107246886198963096955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155990738164590799308731303 233986107246886198963096955)
    ·
      refine ⟨350979160870329298444645433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233986107246886198963096955 350979160870329298444645433)
      ·
        refine ⟨263234370652746973833484075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350979160870329298444645433 263234370652746973833484075)
        ·
          refine ⟨394851555979120460750226113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263234370652746973833484075 394851555979120460750226113)
          ·
            refine ⟨296138666984340345562669585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 394851555979120460750226113 296138666984340345562669585)
            ·
              refine ⟨222104000238255259172002189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296138666984340345562669585 222104000238255259172002189)
              ·
                refine ⟨83289000089345722189500821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222104000238255259172002189 83289000089345722189500821)
                ·
                  refine ⟨3904171879188080727632851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 83289000089345722189500821 3904171879188080727632851)
                  ·
                    refine ⟨5856257818782121091449277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3904171879188080727632851 5856257818782121091449277)
                    ·
                      refine ⟨2196096682043295409293479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5856257818782121091449277 2196096682043295409293479)
                      ·
                        rfl

theorem cell23_4276883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 1, 3].length) (baseStart_4276883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276883 prefixEnd_4276883 := by exact prefixLift 4276883
  have htrace : WordTrace (prefixWord ++ tailWord_4276883) baseStart_4276883 baseEnd_4276883 := by
    simpa [prefixWord, tailWord_4276883, baseEnd_4276883] using wordTrace_append hprefix tailTrace_4276883
  have hstable : (prefixWord ++ tailWord_4276883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276883).length < 2 ^ (prefixWord ++ tailWord_4276883).sum := by decide
  have hdescent : baseEnd_4276883 < baseStart_4276883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276884 : List Nat := [2, 4, 2, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_4276884 : Nat := 118140960795 + 4276884 * 2 ^ 59
def prefixEnd_4276884 : Nat := 4983230072969 + 3 ^ 40 * 4276884 * 2
def baseEnd_4276884 : Nat := 2196097195523949905380975

theorem tailTrace_4276884 : CollatzResearch.WordTrace tailWord_4276884 prefixEnd_4276884 2196097195523949905380975 := by
  unfold tailWord_4276884
  simp only [CollatzResearch.WordTrace]
  refine ⟨77995387318793588239758853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103993849758391450986345137 77995387318793588239758853)
  ·
    refine ⟨14624135122273797794954785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77995387318793588239758853 14624135122273797794954785)
    ·
      refine ⟨10968101341705348346216089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14624135122273797794954785 10968101341705348346216089)
      ·
        refine ⟨8226076006279011259662067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10968101341705348346216089 8226076006279011259662067)
        ·
          refine ⟨12339114009418516889493101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8226076006279011259662067 12339114009418516889493101)
          ·
            refine ⟨4627167753531943833559913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12339114009418516889493101 4627167753531943833559913)
            ·
              refine ⟨3470375815148957875169935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4627167753531943833559913 3470375815148957875169935)
              ·
                refine ⟨5205563722723436812754903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3470375815148957875169935 5205563722723436812754903)
                ·
                  refine ⟨7808345584085155219132355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5205563722723436812754903 7808345584085155219132355)
                  ·
                    refine ⟨11712518376127732828698533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7808345584085155219132355 11712518376127732828698533)
                    ·
                      refine ⟨2196097195523949905380975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11712518376127732828698533 2196097195523949905380975)
                      ·
                        rfl

theorem cell23_4276884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_4276884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276884 prefixEnd_4276884 := by exact prefixLift 4276884
  have htrace : WordTrace (prefixWord ++ tailWord_4276884) baseStart_4276884 baseEnd_4276884 := by
    simpa [prefixWord, tailWord_4276884, baseEnd_4276884] using wordTrace_append hprefix tailTrace_4276884
  have hstable : (prefixWord ++ tailWord_4276884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276884).length < 2 ^ (prefixWord ++ tailWord_4276884).sum := by decide
  have hdescent : baseEnd_4276884 < baseStart_4276884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276900 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 4, 1, 3]
def baseStart_4276900 : Nat := 118140960795 + 4276900 * 2 ^ 59
def prefixEnd_4276900 : Nat := 4983230072969 + 3 ^ 40 * 4276900 * 2
def baseEnd_4276900 : Nat := 2196105411214421842780901

theorem tailTrace_4276900 : CollatzResearch.WordTrace tailWord_4276900 prefixEnd_4276900 2196105411214421842780901 := by
  unfold tailWord_4276900
  simp only [CollatzResearch.WordTrace]
  refine ⟨77995679102764605606050077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103994238803686140808066769 77995679102764605606050077)
  ·
    refine ⟨29248379663536727102268779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77995679102764605606050077 29248379663536727102268779)
    ·
      refine ⟨43872569495305090653403169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29248379663536727102268779 43872569495305090653403169)
      ·
        refine ⟨32904427121478817990052377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43872569495305090653403169 32904427121478817990052377)
        ·
          refine ⟨24678320341109113492539283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32904427121478817990052377 24678320341109113492539283)
          ·
            refine ⟨37017480511663670238808925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24678320341109113492539283 37017480511663670238808925)
            ·
              refine ⟨13881555191873876339553347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37017480511663670238808925 13881555191873876339553347)
              ·
                refine ⟨20822332787810814509330021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13881555191873876339553347 20822332787810814509330021)
                ·
                  refine ⟨3904187397714527720499379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20822332787810814509330021 3904187397714527720499379)
                  ·
                    refine ⟨5856281096571791580749069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3904187397714527720499379 5856281096571791580749069)
                    ·
                      refine ⟨2196105411214421842780901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5856281096571791580749069 2196105411214421842780901)
                      ·
                        rfl

theorem cell23_4276900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_4276900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276900 prefixEnd_4276900 := by exact prefixLift 4276900
  have htrace : WordTrace (prefixWord ++ tailWord_4276900) baseStart_4276900 baseEnd_4276900 := by
    simpa [prefixWord, tailWord_4276900, baseEnd_4276900] using wordTrace_append hprefix tailTrace_4276900
  have hstable : (prefixWord ++ tailWord_4276900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276900).length < 2 ^ (prefixWord ++ tailWord_4276900).sum := by decide
  have hdescent : baseEnd_4276900 < baseStart_4276900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276917 : List Nat := [1, 3, 3, 3, 1, 3, 1, 1, 1, 3, 3]
def baseStart_4276917 : Nat := 118140960795 + 4276917 * 2 ^ 59
def prefixEnd_4276917 : Nat := 4983230072969 + 3 ^ 40 * 4276917 * 2
def baseEnd_4276917 : Nat := 2196114140385548276268323

theorem tailTrace_4276917 : CollatzResearch.WordTrace tailWord_4276917 prefixEnd_4276917 2196114140385548276268323 := by
  unfold tailWord_4276917
  simp only [CollatzResearch.WordTrace]
  refine ⟨155991978246467623115469005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103994652164311748743646003 155991978246467623115469005)
  ·
    refine ⟨58496991842425358668300877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155991978246467623115469005 58496991842425358668300877)
    ·
      refine ⟨21936371940909509500612829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58496991842425358668300877 21936371940909509500612829)
      ·
        refine ⟨8226139477841066062729811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21936371940909509500612829 8226139477841066062729811)
        ·
          refine ⟨12339209216761599094094717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8226139477841066062729811 12339209216761599094094717)
          ·
            refine ⟨4627203456285599660285519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12339209216761599094094717 4627203456285599660285519)
            ·
              refine ⟨6940805184428399490428279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4627203456285599660285519 6940805184428399490428279)
              ·
                refine ⟨10411207776642599235642419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6940805184428399490428279 10411207776642599235642419)
                ·
                  refine ⟨15616811664963898853463629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10411207776642599235642419 15616811664963898853463629)
                  ·
                    refine ⟨5856304374361462070048861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15616811664963898853463629 5856304374361462070048861)
                    ·
                      refine ⟨2196114140385548276268323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5856304374361462070048861 2196114140385548276268323)
                      ·
                        rfl

theorem cell23_4276917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_4276917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276917 prefixEnd_4276917 := by exact prefixLift 4276917
  have htrace : WordTrace (prefixWord ++ tailWord_4276917) baseStart_4276917 baseEnd_4276917 := by
    simpa [prefixWord, tailWord_4276917, baseEnd_4276917] using wordTrace_append hprefix tailTrace_4276917
  have hstable : (prefixWord ++ tailWord_4276917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276917).length < 2 ^ (prefixWord ++ tailWord_4276917).sum := by decide
  have hdescent : baseEnd_4276917 < baseStart_4276917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276927 : List Nat := [1, 1, 2, 2, 2, 5, 2, 2, 1, 3, 2]
def baseStart_4276927 : Nat := 118140960795 + 4276927 * 2 ^ 59
def prefixEnd_4276927 : Nat := 4983230072969 + 3 ^ 40 * 4276927 * 2
def baseEnd_4276927 : Nat := 2196119275192093237143277

theorem tailTrace_4276927 : CollatzResearch.WordTrace tailWord_4276927 prefixEnd_4276927 2196119275192093237143277 := by
  unfold tailWord_4276927
  simp only [CollatzResearch.WordTrace]
  refine ⟨155992342976431394823333035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103994895317620929882222023 155992342976431394823333035)
  ·
    refine ⟨233988514464647092234999553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155992342976431394823333035 233988514464647092234999553)
    ·
      refine ⟨175491385848485319176249665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233988514464647092234999553 175491385848485319176249665)
      ·
        refine ⟨131618539386363989382187249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175491385848485319176249665 131618539386363989382187249)
        ·
          refine ⟨98713904539772992036640437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131618539386363989382187249 98713904539772992036640437)
          ·
            refine ⟨9254428550603718003435041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98713904539772992036640437 9254428550603718003435041)
            ·
              refine ⟨6940821412952788502576281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9254428550603718003435041 6940821412952788502576281)
              ·
                refine ⟨5205616059714591376932211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6940821412952788502576281 5205616059714591376932211)
                ·
                  refine ⟨7808424089571887065398317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5205616059714591376932211 7808424089571887065398317)
                  ·
                    refine ⟨2928159033589457649524369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7808424089571887065398317 2928159033589457649524369)
                    ·
                      refine ⟨2196119275192093237143277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2928159033589457649524369 2196119275192093237143277)
                      ·
                        rfl

theorem cell23_4276927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 3, 2].length) (baseStart_4276927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276927 prefixEnd_4276927 := by exact prefixLift 4276927
  have htrace : WordTrace (prefixWord ++ tailWord_4276927) baseStart_4276927 baseEnd_4276927 := by
    simpa [prefixWord, tailWord_4276927, baseEnd_4276927] using wordTrace_append hprefix tailTrace_4276927
  have hstable : (prefixWord ++ tailWord_4276927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276927).length < 2 ^ (prefixWord ++ tailWord_4276927).sum := by decide
  have hdescent : baseEnd_4276927 < baseStart_4276927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4276974 : List Nat := [4, 1, 2, 1, 1, 4, 1, 3, 2, 2, 2]
def baseStart_4276974 : Nat := 118140960795 + 4276974 * 2 ^ 59
def prefixEnd_4276974 : Nat := 4983230072969 + 3 ^ 40 * 4276974 * 2
def baseEnd_4276974 : Nat := 2196143408782854553255561

theorem tailTrace_4276974 : CollatzResearch.WordTrace tailWord_4276974 prefixEnd_4276974 2196143408782854553255561 := by
  unfold tailWord_4276974
  simp only [CollatzResearch.WordTrace]
  refine ⟨19499257150907640231286747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103996038138174081233529317 19499257150907640231286747)
  ·
    refine ⟨29248885726361460346930121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19499257150907640231286747 29248885726361460346930121)
    ·
      refine ⟨21936664294771095260197591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29248885726361460346930121 21936664294771095260197591)
      ·
        refine ⟨32904996442156642890296387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21936664294771095260197591 32904996442156642890296387)
        ·
          refine ⟨49357494663234964335444581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32904996442156642890296387 49357494663234964335444581)
          ·
            refine ⟨9254530249356555812895859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49357494663234964335444581 9254530249356555812895859)
            ·
              refine ⟨13881795374034833719343789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9254530249356555812895859 13881795374034833719343789)
              ·
                refine ⟨5205673265263062644753921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13881795374034833719343789 5205673265263062644753921)
                ·
                  refine ⟨3904254948947296983565441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5205673265263062644753921 3904254948947296983565441)
                  ·
                    refine ⟨2928191211710472737674081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3904254948947296983565441 2928191211710472737674081)
                    ·
                      refine ⟨2196143408782854553255561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2928191211710472737674081 2196143408782854553255561)
                      ·
                        rfl

theorem cell23_4276974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_4276974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4276974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4276974 prefixEnd_4276974 := by exact prefixLift 4276974
  have htrace : WordTrace (prefixWord ++ tailWord_4276974) baseStart_4276974 baseEnd_4276974 := by
    simpa [prefixWord, tailWord_4276974, baseEnd_4276974] using wordTrace_append hprefix tailTrace_4276974
  have hstable : (prefixWord ++ tailWord_4276974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4276974).length < 2 ^ (prefixWord ++ tailWord_4276974).sum := by decide
  have hdescent : baseEnd_4276974 < baseStart_4276974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4276974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277033 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 3, 4, 3]
def baseStart_4277033 : Nat := 118140960795 + 4277033 * 2 ^ 59
def prefixEnd_4277033 : Nat := 4983230072969 + 3 ^ 40 * 4277033 * 2
def baseEnd_4277033 : Nat := 2196173704141469822417789

theorem tailTrace_4277033 : CollatzResearch.WordTrace tailWord_4277033 prefixEnd_4277033 2196173704141469822417789 := by
  unfold tailWord_4277033
  simp only [CollatzResearch.WordTrace]
  refine ⟨155996209114047374926691753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103997472742698249951127835 155996209114047374926691753)
  ·
    refine ⟨116997156835535531195018815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155996209114047374926691753 116997156835535531195018815)
    ·
      refine ⟨175495735253303296792528223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116997156835535531195018815 175495735253303296792528223)
      ·
        refine ⟨263243602879954945188792335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175495735253303296792528223 263243602879954945188792335)
        ·
          refine ⟨394865404319932417783188503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263243602879954945188792335 394865404319932417783188503)
          ·
            refine ⟨592298106479898626674782755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394865404319932417783188503 592298106479898626674782755)
            ·
              refine ⟨888447159719847940012174133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592298106479898626674782755 888447159719847940012174133)
              ·
                refine ⟨83291921223735744376141325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 888447159719847940012174133 83291921223735744376141325)
                ·
                  refine ⟨31234470458900904141052997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83291921223735744376141325 31234470458900904141052997)
                  ·
                    refine ⟨5856463211043919526447437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31234470458900904141052997 5856463211043919526447437)
                    ·
                      refine ⟨2196173704141469822417789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5856463211043919526447437 2196173704141469822417789)
                      ·
                        rfl

theorem cell23_4277033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 4, 3].length) (baseStart_4277033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277033 prefixEnd_4277033 := by exact prefixLift 4277033
  have htrace : WordTrace (prefixWord ++ tailWord_4277033) baseStart_4277033 baseEnd_4277033 := by
    simpa [prefixWord, tailWord_4277033, baseEnd_4277033] using wordTrace_append hprefix tailTrace_4277033
  have hstable : (prefixWord ++ tailWord_4277033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277033).length < 2 ^ (prefixWord ++ tailWord_4277033).sum := by decide
  have hdescent : baseEnd_4277033 < baseStart_4277033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277044 : List Nat := [2, 5, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_4277044 : Nat := 118140960795 + 4277044 * 2 ^ 59
def prefixEnd_4277044 : Nat := 4983230072969 + 3 ^ 40 * 4277044 * 2
def baseEnd_4277044 : Nat := 732059784142889759793413

theorem tailTrace_4277044 : CollatzResearch.WordTrace tailWord_4277044 prefixEnd_4277044 732059784142889759793413 := by
  unfold tailWord_4277044
  simp only [CollatzResearch.WordTrace]
  refine ⟨77998305158503761902671093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103997740211338349203561457 77998305158503761902671093)
  ·
    refine ⟨7312341108609727678375415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77998305158503761902671093 7312341108609727678375415)
    ·
      refine ⟨10968511662914591517563123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7312341108609727678375415 10968511662914591517563123)
      ·
        refine ⟨16452767494371887276344685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10968511662914591517563123 16452767494371887276344685)
        ·
          refine ⟨6169787810389457728629257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16452767494371887276344685 6169787810389457728629257)
          ·
            refine ⟨4627340857792093296471943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6169787810389457728629257 4627340857792093296471943)
            ·
              refine ⟨6941011286688139944707915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4627340857792093296471943 6941011286688139944707915)
              ·
                refine ⟨10411516930032209917061873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6941011286688139944707915 10411516930032209917061873)
                ·
                  refine ⟨7808637697524157437796405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10411516930032209917061873 7808637697524157437796405)
                  ·
                    refine ⟨732059784142889759793413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7808637697524157437796405 732059784142889759793413)
                    ·
                      rfl

theorem cell23_4277044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_4277044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277044 prefixEnd_4277044 := by exact prefixLift 4277044
  have htrace : WordTrace (prefixWord ++ tailWord_4277044) baseStart_4277044 baseEnd_4277044 := by
    simpa [prefixWord, tailWord_4277044, baseEnd_4277044] using wordTrace_append hprefix tailTrace_4277044
  have hstable : (prefixWord ++ tailWord_4277044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277044).length < 2 ^ (prefixWord ++ tailWord_4277044).sum := by decide
  have hdescent : baseEnd_4277044 < baseStart_4277044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277093 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 2, 1, 7]
def baseStart_4277093 : Nat := 118140960795 + 4277093 * 2 ^ 59
def prefixEnd_4277093 : Nat := 4983230072969 + 3 ^ 40 * 4277093 * 2
def baseEnd_4277093 : Nat := 2196204512980739587667513

theorem tailTrace_4277093 : CollatzResearch.WordTrace tailWord_4277093 prefixEnd_4277093 2196204512980739587667513 := by
  unfold tailWord_4277093
  simp only [CollatzResearch.WordTrace]
  refine ⟨155998397493830005173875933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103998931662553336782583955 155998397493830005173875933)
  ·
    refine ⟨58499399060186251940203475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155998397493830005173875933 58499399060186251940203475)
    ·
      refine ⟨87749098590279377910305213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58499399060186251940203475 87749098590279377910305213)
      ·
        refine ⟨32905911971354766716364455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87749098590279377910305213 32905911971354766716364455)
        ·
          refine ⟨49358867957032150074546683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32905911971354766716364455 49358867957032150074546683)
          ·
            refine ⟨74038301935548225111820025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49358867957032150074546683 74038301935548225111820025)
            ·
              refine ⟨55528726451661168833865019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74038301935548225111820025 55528726451661168833865019)
              ·
                refine ⟨83293089677491753250797529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55528726451661168833865019 83293089677491753250797529)
                ·
                  refine ⟨62469817258118814938098147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83293089677491753250797529 62469817258118814938098147)
                  ·
                    refine ⟨93704725887178222407147221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62469817258118814938098147 93704725887178222407147221)
                    ·
                      refine ⟨2196204512980739587667513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93704725887178222407147221 2196204512980739587667513)
                      ·
                        rfl

theorem cell23_4277093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_4277093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277093 prefixEnd_4277093 := by exact prefixLift 4277093
  have htrace : WordTrace (prefixWord ++ tailWord_4277093) baseStart_4277093 baseEnd_4277093 := by
    simpa [prefixWord, tailWord_4277093, baseEnd_4277093] using wordTrace_append hprefix tailTrace_4277093
  have hstable : (prefixWord ++ tailWord_4277093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277093).length < 2 ^ (prefixWord ++ tailWord_4277093).sum := by decide
  have hdescent : baseEnd_4277093 < baseStart_4277093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277103 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 4]
def baseStart_4277103 : Nat := 118140960795 + 4277103 * 2 ^ 59
def prefixEnd_4277103 : Nat := 4983230072969 + 3 ^ 40 * 4277103 * 2
def baseEnd_4277103 : Nat := 2196209647787284548542467

theorem tailTrace_4277103 : CollatzResearch.WordTrace tailWord_4277103 prefixEnd_4277103 2196209647787284548542467 := by
  unfold tailWord_4277103
  simp only [CollatzResearch.WordTrace]
  refine ⟨155998762223793776881739963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103999174815862517921159975 155998762223793776881739963)
  ·
    refine ⟨233998143335690665322609945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155998762223793776881739963 233998143335690665322609945)
    ·
      refine ⟨175498607501767998991957459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233998143335690665322609945 175498607501767998991957459)
      ·
        refine ⟨263247911252651998487936189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175498607501767998991957459 263247911252651998487936189)
        ·
          refine ⟨98717966719744499432976071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 263247911252651998487936189 98717966719744499432976071)
          ·
            refine ⟨148076950079616749149464107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98717966719744499432976071 148076950079616749149464107)
            ·
              refine ⟨222115425119425123724196161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148076950079616749149464107 222115425119425123724196161)
              ·
                refine ⟨166586568839568842793147121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222115425119425123724196161 166586568839568842793147121)
                ·
                  refine ⟨124939926629676632094860341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166586568839568842793147121 124939926629676632094860341)
                  ·
                    refine ⟨11713118121532184258893157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 124939926629676632094860341 11713118121532184258893157)
                    ·
                      refine ⟨2196209647787284548542467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11713118121532184258893157 2196209647787284548542467)
                      ·
                        rfl

theorem cell23_4277103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 4].length) (baseStart_4277103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277103 prefixEnd_4277103 := by exact prefixLift 4277103
  have htrace : WordTrace (prefixWord ++ tailWord_4277103) baseStart_4277103 baseEnd_4277103 := by
    simpa [prefixWord, tailWord_4277103, baseEnd_4277103] using wordTrace_append hprefix tailTrace_4277103
  have hstable : (prefixWord ++ tailWord_4277103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277103).length < 2 ^ (prefixWord ++ tailWord_4277103).sum := by decide
  have hdescent : baseEnd_4277103 < baseStart_4277103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277154 : List Nat := [3, 3, 1, 2, 2, 1, 3, 2, 1, 1, 4]
def baseStart_4277154 : Nat := 118140960795 + 4277154 * 2 ^ 59
def prefixEnd_4277154 : Nat := 4983230072969 + 3 ^ 40 * 4277154 * 2
def baseEnd_4277154 : Nat := 2196235835300663849004733

theorem tailTrace_4277154 : CollatzResearch.WordTrace tailWord_4277154 prefixEnd_4277154 2196235835300663849004733 := by
  unfold tailWord_4277154
  simp only [CollatzResearch.WordTrace]
  refine ⟨39000155586652253147961629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104000414897739341727897677 39000155586652253147961629)
  ·
    refine ⟨14625058344994594930485611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39000155586652253147961629 14625058344994594930485611)
    ·
      refine ⟨21937587517491892395728417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14625058344994594930485611 21937587517491892395728417)
      ·
        refine ⟨16453190638118919296796313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21937587517491892395728417 16453190638118919296796313)
        ·
          refine ⟨12339892978589189472597235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16453190638118919296796313 12339892978589189472597235)
          ·
            refine ⟨18509839467883784208895853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12339892978589189472597235 18509839467883784208895853)
            ·
              refine ⟨6941189800456419078335945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18509839467883784208895853 6941189800456419078335945)
              ·
                refine ⟨5205892350342314308751959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6941189800456419078335945 5205892350342314308751959)
                ·
                  refine ⟨7808838525513471463127939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5205892350342314308751959 7808838525513471463127939)
                  ·
                    refine ⟨11713257788270207194691909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7808838525513471463127939 11713257788270207194691909)
                    ·
                      refine ⟨2196235835300663849004733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11713257788270207194691909 2196235835300663849004733)
                      ·
                        rfl

theorem cell23_4277154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_4277154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277154 prefixEnd_4277154 := by exact prefixLift 4277154
  have htrace : WordTrace (prefixWord ++ tailWord_4277154) baseStart_4277154 baseEnd_4277154 := by
    simpa [prefixWord, tailWord_4277154, baseEnd_4277154] using wordTrace_append hprefix tailTrace_4277154
  have hstable : (prefixWord ++ tailWord_4277154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277154).length < 2 ^ (prefixWord ++ tailWord_4277154).sum := by decide
  have hdescent : baseEnd_4277154 < baseStart_4277154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277163 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 6]
def baseStart_4277163 : Nat := 118140960795 + 4277163 * 2 ^ 59
def prefixEnd_4277163 : Nat := 4983230072969 + 3 ^ 40 * 4277163 * 2
def baseEnd_4277163 : Nat := 2196240456626554313792191

theorem tailTrace_4277163 : CollatzResearch.WordTrace tailWord_4277163 prefixEnd_4277163 2196240456626554313792191 := by
  unfold tailWord_4277163
  simp only [CollatzResearch.WordTrace]
  refine ⟨156000950603576407128924143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104000633735717604752616095 156000950603576407128924143)
  ·
    refine ⟨234001425905364610693386215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156000950603576407128924143 234001425905364610693386215)
    ·
      refine ⟨351002138858046916040079323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234001425905364610693386215 351002138858046916040079323)
      ·
        refine ⟨526503208287070374060118985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351002138858046916040079323 526503208287070374060118985)
        ·
          refine ⟨394877406215302780545089239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 526503208287070374060118985 394877406215302780545089239)
          ·
            refine ⟨592316109322954170817633859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394877406215302780545089239 592316109322954170817633859)
            ·
              refine ⟨888474163984431256226450789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592316109322954170817633859 888474163984431256226450789)
              ·
                refine ⟨166588905747080860542459523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 888474163984431256226450789 166588905747080860542459523)
                ·
                  refine ⟨249883358620621290813689285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166588905747080860542459523 249883358620621290813689285)
                  ·
                    refine ⟨46853129741366492027566741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 249883358620621290813689285 46853129741366492027566741)
                    ·
                      refine ⟨2196240456626554313792191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46853129741366492027566741 2196240456626554313792191)
                      ·
                        rfl

theorem cell23_4277163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 6].length) (baseStart_4277163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277163 prefixEnd_4277163 := by exact prefixLift 4277163
  have htrace : WordTrace (prefixWord ++ tailWord_4277163) baseStart_4277163 baseEnd_4277163 := by
    simpa [prefixWord, tailWord_4277163, baseEnd_4277163] using wordTrace_append hprefix tailTrace_4277163
  have hstable : (prefixWord ++ tailWord_4277163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277163).length < 2 ^ (prefixWord ++ tailWord_4277163).sum := by decide
  have hdescent : baseEnd_4277163 < baseStart_4277163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277204 : List Nat := [2, 4, 1, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_4277204 : Nat := 118140960795 + 4277204 * 2 ^ 59
def prefixEnd_4277204 : Nat := 4983230072969 + 3 ^ 40 * 4277204 * 2
def baseEnd_4277204 : Nat := 2196261509333388653379503

theorem tailTrace_4277204 : CollatzResearch.WordTrace tailWord_4277204 prefixEnd_4277204 2196261509333388653379503 := by
  unfold tailWord_4277204
  simp only [CollatzResearch.WordTrace]
  refine ⟨78001222998213935565583333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104001630664285247420777777 78001222998213935565583333)
  ·
    refine ⟨14625229312165112918546875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78001222998213935565583333 14625229312165112918546875)
    ·
      refine ⟨21937843968247669377820313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14625229312165112918546875 21937843968247669377820313)
      ·
        refine ⟨16453382976185752033365235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21937843968247669377820313 16453382976185752033365235)
        ·
          refine ⟨24680074464278628050047853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16453382976185752033365235 24680074464278628050047853)
          ·
            refine ⟨9255027924104485518767945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24680074464278628050047853 9255027924104485518767945)
            ·
              refine ⟨6941270943078364139075959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9255027924104485518767945 6941270943078364139075959)
              ·
                refine ⟨10411906414617546208613939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6941270943078364139075959 10411906414617546208613939)
                ·
                  refine ⟨15617859621926319312920909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10411906414617546208613939 15617859621926319312920909)
                  ·
                    refine ⟨5856697358222369742345341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15617859621926319312920909 5856697358222369742345341)
                    ·
                      refine ⟨2196261509333388653379503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5856697358222369742345341 2196261509333388653379503)
                      ·
                        rfl

theorem cell23_4277204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_4277204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277204 prefixEnd_4277204 := by exact prefixLift 4277204
  have htrace : WordTrace (prefixWord ++ tailWord_4277204) baseStart_4277204 baseEnd_4277204 := by
    simpa [prefixWord, tailWord_4277204, baseEnd_4277204] using wordTrace_append hprefix tailTrace_4277204
  have hstable : (prefixWord ++ tailWord_4277204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277204).length < 2 ^ (prefixWord ++ tailWord_4277204).sum := by decide
  have hdescent : baseEnd_4277204 < baseStart_4277204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277231 : List Nat := [1, 1, 2, 1, 4, 3, 4, 1, 1, 3, 2]
def baseStart_4277231 : Nat := 118140960795 + 4277231 * 2 ^ 59
def prefixEnd_4277231 : Nat := 4983230072969 + 3 ^ 40 * 4277231 * 2
def baseEnd_4277231 : Nat := 2196275373311060047741879

theorem tailTrace_4277231 : CollatzResearch.WordTrace tailWord_4277231 prefixEnd_4277231 2196275373311060047741879 := by
  unfold tailWord_4277231
  simp only [CollatzResearch.WordTrace]
  refine ⟨156003430767330054742399547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104002287178220036494933031 156003430767330054742399547)
  ·
    refine ⟨234005146150995082113599321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156003430767330054742399547 234005146150995082113599321)
    ·
      refine ⟨175503859613246311585199491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234005146150995082113599321 175503859613246311585199491)
      ·
        refine ⟨263255789419869467377799237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175503859613246311585199491 263255789419869467377799237)
        ·
          refine ⟨49360460516225525133337357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 263255789419869467377799237 49360460516225525133337357)
          ·
            refine ⟨18510172693584571925001509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49360460516225525133337357 18510172693584571925001509)
            ·
              refine ⟨3470657380047107235937783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18510172693584571925001509 3470657380047107235937783)
              ·
                refine ⟨5205986070070660853906675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3470657380047107235937783 5205986070070660853906675)
                ·
                  refine ⟨7808979105105991280860013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5205986070070660853906675 7808979105105991280860013)
                  ·
                    refine ⟨2928367164414746730322505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7808979105105991280860013 2928367164414746730322505)
                    ·
                      refine ⟨2196275373311060047741879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2928367164414746730322505 2196275373311060047741879)
                      ·
                        rfl

theorem cell23_4277231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 1, 3, 2].length) (baseStart_4277231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277231 prefixEnd_4277231 := by exact prefixLift 4277231
  have htrace : WordTrace (prefixWord ++ tailWord_4277231) baseStart_4277231 baseEnd_4277231 := by
    simpa [prefixWord, tailWord_4277231, baseEnd_4277231] using wordTrace_append hprefix tailTrace_4277231
  have hstable : (prefixWord ++ tailWord_4277231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277231).length < 2 ^ (prefixWord ++ tailWord_4277231).sum := by decide
  have hdescent : baseEnd_4277231 < baseStart_4277231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277238 : List Nat := [5, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3]
def baseStart_4277238 : Nat := 118140960795 + 4277238 * 2 ^ 59
def prefixEnd_4277238 : Nat := 4983230072969 + 3 ^ 40 * 4277238 * 2
def baseEnd_4277238 : Nat := 2196278967675641520354347

theorem tailTrace_4277238 : CollatzResearch.WordTrace tailWord_4277238 prefixEnd_4277238 2196278967675641520354347 := by
  unfold tailWord_4277238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9750230379894043433619023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104002457385536463291936245 9750230379894043433619023)
  ·
    refine ⟨14625345569841065150428535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9750230379894043433619023 14625345569841065150428535)
    ·
      refine ⟨21938018354761597725642803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14625345569841065150428535 21938018354761597725642803)
      ·
        refine ⟨32907027532142396588464205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21938018354761597725642803 32907027532142396588464205)
        ·
          refine ⟨12340135324553398720674077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32907027532142396588464205 12340135324553398720674077)
          ·
            refine ⟨4627550746707524520252779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12340135324553398720674077 4627550746707524520252779)
            ·
              refine ⟨6941326120061286780379169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4627550746707524520252779 6941326120061286780379169)
              ·
                refine ⟨5205994590045965085284377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6941326120061286780379169 5205994590045965085284377)
                ·
                  refine ⟨3904495942534473813963283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5205994590045965085284377 3904495942534473813963283)
                  ·
                    refine ⟨5856743913801710720944925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3904495942534473813963283 5856743913801710720944925)
                    ·
                      refine ⟨2196278967675641520354347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5856743913801710720944925 2196278967675641520354347)
                      ·
                        rfl

theorem cell23_4277238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_4277238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277238 prefixEnd_4277238 := by exact prefixLift 4277238
  have htrace : WordTrace (prefixWord ++ tailWord_4277238) baseStart_4277238 baseEnd_4277238 := by
    simpa [prefixWord, tailWord_4277238, baseEnd_4277238] using wordTrace_append hprefix tailTrace_4277238
  have hstable : (prefixWord ++ tailWord_4277238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277238).length < 2 ^ (prefixWord ++ tailWord_4277238).sum := by decide
  have hdescent : baseEnd_4277238 < baseStart_4277238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277297 : List Nat := [1, 2, 2, 3, 1, 2, 3, 2, 2, 5]
def baseStart_4277297 : Nat := 118140960795 + 4277297 * 2 ^ 59
def prefixEnd_4277297 : Nat := 4983230072969 + 3 ^ 40 * 4277297 * 2
def baseEnd_4277297 : Nat := 732103087678085596505525

theorem tailTrace_4277297 : CollatzResearch.WordTrace tailWord_4277297 prefixEnd_4277297 732103087678085596505525 := by
  unfold tailWord_4277297
  simp only [CollatzResearch.WordTrace]
  refine ⟨156005837985090948014302145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104003891990060632009534763 156005837985090948014302145)
  ·
    refine ⟨117004378488818211010726609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156005837985090948014302145 117004378488818211010726609)
    ·
      refine ⟨87753283866613658258044957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117004378488818211010726609 87753283866613658258044957)
      ·
        refine ⟨32907481449980121846766859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87753283866613658258044957 32907481449980121846766859)
        ·
          refine ⟨49361222174970182770150289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32907481449980121846766859 49361222174970182770150289)
          ·
            refine ⟨37020916631227637077612717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49361222174970182770150289 37020916631227637077612717)
            ·
              refine ⟨13882843736710363904104769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37020916631227637077612717 13882843736710363904104769)
              ·
                refine ⟨10412132802532772928078577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13882843736710363904104769 10412132802532772928078577)
                ·
                  refine ⟨7809099601899579696058933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10412132802532772928078577 7809099601899579696058933)
                  ·
                    refine ⟨732103087678085596505525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7809099601899579696058933 732103087678085596505525)
                    ·
                      rfl

theorem cell23_4277297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_4277297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277297 prefixEnd_4277297 := by exact prefixLift 4277297
  have htrace : WordTrace (prefixWord ++ tailWord_4277297) baseStart_4277297 baseEnd_4277297 := by
    simpa [prefixWord, tailWord_4277297, baseEnd_4277297] using wordTrace_append hprefix tailTrace_4277297
  have hstable : (prefixWord ++ tailWord_4277297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277297).length < 2 ^ (prefixWord ++ tailWord_4277297).sum := by decide
  have hdescent : baseEnd_4277297 < baseStart_4277297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277418 : List Nat := [3, 1, 5, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_4277418 : Nat := 118140960795 + 4277418 * 2 ^ 59
def prefixEnd_4277418 : Nat := 4983230072969 + 3 ^ 40 * 4277418 * 2
def baseEnd_4277418 : Nat := 2196371394193450816103519

theorem tailTrace_4277418 : CollatzResearch.WordTrace tailWord_4277418 prefixEnd_4277418 2196371394193450816103519 := by
  unfold tailWord_4277418
  simp only [CollatzResearch.WordTrace]
  refine ⟨39002562804413146419864227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104006834145101723786304605 39002562804413146419864227)
  ·
    refine ⟨58503844206619719629796341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39002562804413146419864227 58503844206619719629796341)
    ·
      refine ⟨5484735394370598715293407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58503844206619719629796341 5484735394370598715293407)
      ·
        refine ⟨8227103091555898072940111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5484735394370598715293407 8227103091555898072940111)
        ·
          refine ⟨12340654637333847109410167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8227103091555898072940111 12340654637333847109410167)
          ·
            refine ⟨18510981956000770664115251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12340654637333847109410167 18510981956000770664115251)
            ·
              refine ⟨27766472934001155996172877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18510981956000770664115251 27766472934001155996172877)
              ·
                refine ⟨10412427350250433498564829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27766472934001155996172877 10412427350250433498564829)
                ·
                  refine ⟨3904660256343912561961811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10412427350250433498564829 3904660256343912561961811)
                  ·
                    refine ⟨5856990384515868842942717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3904660256343912561961811 5856990384515868842942717)
                    ·
                      refine ⟨2196371394193450816103519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5856990384515868842942717 2196371394193450816103519)
                      ·
                        rfl

theorem cell23_4277418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_4277418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277418 prefixEnd_4277418 := by exact prefixLift 4277418
  have htrace : WordTrace (prefixWord ++ tailWord_4277418) baseStart_4277418 baseEnd_4277418 := by
    simpa [prefixWord, tailWord_4277418, baseEnd_4277418] using wordTrace_append hprefix tailTrace_4277418
  have hstable : (prefixWord ++ tailWord_4277418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277418).length < 2 ^ (prefixWord ++ tailWord_4277418).sum := by decide
  have hdescent : baseEnd_4277418 < baseStart_4277418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277427 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 5]
def baseStart_4277427 : Nat := 118140960795 + 4277427 * 2 ^ 59
def prefixEnd_4277427 : Nat := 4983230072969 + 3 ^ 40 * 4277427 * 2
def baseEnd_4277427 : Nat := 2196376015519341280890977

theorem tailTrace_4277427 : CollatzResearch.WordTrace tailWord_4277427 prefixEnd_4277427 2196376015519341280890977 := by
  unfold tailWord_4277427
  simp only [CollatzResearch.WordTrace]
  refine ⟨156010579474619980216534535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104007052983079986811023023 156010579474619980216534535)
  ·
    refine ⟨234015869211929970324801803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156010579474619980216534535 234015869211929970324801803)
    ·
      refine ⟨351023803817894955487202705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234015869211929970324801803 351023803817894955487202705)
      ·
        refine ⟨263267852863421216615402029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351023803817894955487202705 263267852863421216615402029)
        ·
          refine ⟨98725444823782956230775761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 263267852863421216615402029 98725444823782956230775761)
          ·
            refine ⟨74044083617837217173081821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98725444823782956230775761 74044083617837217173081821)
            ·
              refine ⟨27766531356688956439905683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74044083617837217173081821 27766531356688956439905683)
              ·
                refine ⟨41649797035033434659858525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27766531356688956439905683 41649797035033434659858525)
                ·
                  refine ⟨15618673888137537997446947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41649797035033434659858525 15618673888137537997446947)
                  ·
                    refine ⟨23428010832206306996170421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15618673888137537997446947 23428010832206306996170421)
                    ·
                      refine ⟨2196376015519341280890977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23428010832206306996170421 2196376015519341280890977)
                      ·
                        rfl

theorem cell23_4277427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 5].length) (baseStart_4277427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277427 prefixEnd_4277427 := by exact prefixLift 4277427
  have htrace : WordTrace (prefixWord ++ tailWord_4277427) baseStart_4277427 baseEnd_4277427 := by
    simpa [prefixWord, tailWord_4277427, baseEnd_4277427] using wordTrace_append hprefix tailTrace_4277427
  have hstable : (prefixWord ++ tailWord_4277427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277427).length < 2 ^ (prefixWord ++ tailWord_4277427).sum := by decide
  have hdescent : baseEnd_4277427 < baseStart_4277427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277446 : List Nat := [6, 1, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_4277446 : Nat := 118140960795 + 4277446 * 2 ^ 59
def prefixEnd_4277446 : Nat := 4983230072969 + 3 ^ 40 * 4277446 * 2
def baseEnd_4277446 : Nat := 732128590550592235517797

theorem tailTrace_4277446 : CollatzResearch.WordTrace tailWord_4277446 prefixEnd_4277446 732128590550592235517797 := by
  unfold tailWord_4277446
  simp only [CollatzResearch.WordTrace]
  refine ⟨4875352264423473326921131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 104007514974367430974317461 4875352264423473326921131)
  ·
    refine ⟨7313028396635209990381697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4875352264423473326921131 7313028396635209990381697)
    ·
      refine ⟨5484771297476407492786273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7313028396635209990381697 5484771297476407492786273)
      ·
        refine ⟨4113578473107305619589705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5484771297476407492786273 4113578473107305619589705)
        ·
          refine ⟨3085183854830479214692279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4113578473107305619589705 3085183854830479214692279)
          ·
            refine ⟨4627775782245718822038419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3085183854830479214692279 4627775782245718822038419)
            ·
              refine ⟨6941663673368578233057629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4627775782245718822038419 6941663673368578233057629)
              ·
                refine ⟨2603123877513216837396611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6941663673368578233057629 2603123877513216837396611)
                ·
                  refine ⟨3904685816269825256094917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2603123877513216837396611 3904685816269825256094917)
                  ·
                    refine ⟨732128590550592235517797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3904685816269825256094917 732128590550592235517797)
                    ·
                      rfl

theorem cell23_4277446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_4277446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277446 prefixEnd_4277446 := by exact prefixLift 4277446
  have htrace : WordTrace (prefixWord ++ tailWord_4277446) baseStart_4277446 baseEnd_4277446 := by
    simpa [prefixWord, tailWord_4277446, baseEnd_4277446] using wordTrace_append hprefix tailTrace_4277446
  have hstable : (prefixWord ++ tailWord_4277446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277446).length < 2 ^ (prefixWord ++ tailWord_4277446).sum := by decide
  have hdescent : baseEnd_4277446 < baseStart_4277446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277461 : List Nat := [1, 3, 2, 4, 1, 2, 2, 1, 1, 1, 5]
def baseStart_4277461 : Nat := 118140960795 + 4277461 * 2 ^ 59
def prefixEnd_4277461 : Nat := 4983230072969 + 3 ^ 40 * 4277461 * 2
def baseEnd_4277461 : Nat := 2196393473861594147865821

theorem tailTrace_4277461 : CollatzResearch.WordTrace tailWord_4277461 prefixEnd_4277461 2196393473861594147865821 := by
  unfold tailWord_4277461
  simp only [CollatzResearch.WordTrace]
  refine ⟨156011819556496804023272237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104007879704331202682181491 156011819556496804023272237)
  ·
    refine ⟨58504432333686301508727089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156011819556496804023272237 58504432333686301508727089)
    ·
      refine ⟨43878324250264726131545317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58504432333686301508727089 43878324250264726131545317)
      ·
        refine ⟨8227185796924636149664747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43878324250264726131545317 8227185796924636149664747)
        ·
          refine ⟨12340778695386954224497121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8227185796924636149664747 12340778695386954224497121)
          ·
            refine ⟨9255584021540215668372841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12340778695386954224497121 9255584021540215668372841)
            ·
              refine ⟨6941688016155161751279631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9255584021540215668372841 6941688016155161751279631)
              ·
                refine ⟨10412532024232742626919447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6941688016155161751279631 10412532024232742626919447)
                ·
                  refine ⟨15618798036349113940379171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10412532024232742626919447 15618798036349113940379171)
                  ·
                    refine ⟨23428197054523670910568757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15618798036349113940379171 23428197054523670910568757)
                    ·
                      refine ⟨2196393473861594147865821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23428197054523670910568757 2196393473861594147865821)
                      ·
                        rfl

theorem cell23_4277461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_4277461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277461 prefixEnd_4277461 := by exact prefixLift 4277461
  have htrace : WordTrace (prefixWord ++ tailWord_4277461) baseStart_4277461 baseEnd_4277461 := by
    simpa [prefixWord, tailWord_4277461, baseEnd_4277461] using wordTrace_append hprefix tailTrace_4277461
  have hstable : (prefixWord ++ tailWord_4277461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277461).length < 2 ^ (prefixWord ++ tailWord_4277461).sum := by decide
  have hdescent : baseEnd_4277461 < baseStart_4277461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277464 : List Nat := [2, 1, 2, 2, 5, 2, 9]
def baseStart_4277464 : Nat := 118140960795 + 4277464 * 2 ^ 59
def prefixEnd_4277464 : Nat := 4983230072969 + 3 ^ 40 * 4277464 * 2
def baseEnd_4277464 : Nat := 27115987830908118964547

theorem tailTrace_4277464 : CollatzResearch.WordTrace tailWord_4277464 prefixEnd_4277464 27115987830908118964547 := by
  unfold tailWord_4277464
  simp only [CollatzResearch.WordTrace]
  refine ⟨78005964487742967767815723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104007952650323957023754297 78005964487742967767815723)
  ·
    refine ⟨117008946731614451651723585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78005964487742967767815723 117008946731614451651723585)
    ·
      refine ⟨87756710048710838738792689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117008946731614451651723585 87756710048710838738792689)
      ·
        refine ⟨65817532536533129054094517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87756710048710838738792689 65817532536533129054094517)
        ·
          refine ⟨6170393675299980848821361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65817532536533129054094517 6170393675299980848821361)
          ·
            refine ⟨4627795256474985636616021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6170393675299980848821361 4627795256474985636616021)
            ·
              refine ⟨27115987830908118964547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4627795256474985636616021 27115987830908118964547)
              ·
                rfl

theorem cell23_4277464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 9].length) (baseStart_4277464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277464 prefixEnd_4277464 := by exact prefixLift 4277464
  have htrace : WordTrace (prefixWord ++ tailWord_4277464) baseStart_4277464 baseEnd_4277464 := by
    simpa [prefixWord, tailWord_4277464, baseEnd_4277464] using wordTrace_append hprefix tailTrace_4277464
  have hstable : (prefixWord ++ tailWord_4277464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277464).length < 2 ^ (prefixWord ++ tailWord_4277464).sum := by decide
  have hdescent : baseEnd_4277464 < baseStart_4277464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277485 : List Nat := [1, 5, 1, 2, 2, 3, 2, 1, 2, 4]
def baseStart_4277485 : Nat := 118140960795 + 4277485 * 2 ^ 59
def prefixEnd_4277485 : Nat := 4983230072969 + 3 ^ 40 * 4277485 * 2
def baseEnd_4277485 : Nat := 732135265799100684655237

theorem tailTrace_4277485 : CollatzResearch.WordTrace tailWord_4277485 prefixEnd_4277485 732135265799100684655237 := by
  unfold tailWord_4277485
  simp only [CollatzResearch.WordTrace]
  refine ⟨156012694908409856122145909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104008463272273237414763939 156012694908409856122145909)
  ·
    refine ⟨14626190147663424011451179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 156012694908409856122145909 14626190147663424011451179)
    ·
      refine ⟨21939285221495136017176769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14626190147663424011451179 21939285221495136017176769)
      ·
        refine ⟨16454463916121352012882577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21939285221495136017176769 16454463916121352012882577)
        ·
          refine ⟨12340847937091014009661933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16454463916121352012882577 12340847937091014009661933)
          ·
            refine ⟨4627817976409130253623225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12340847937091014009661933 4627817976409130253623225)
            ·
              refine ⟨3470863482306847690217419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4627817976409130253623225 3470863482306847690217419)
              ·
                refine ⟨5206295223460271535326129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3470863482306847690217419 5206295223460271535326129)
                ·
                  refine ⟨3904721417595203651494597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5206295223460271535326129 3904721417595203651494597)
                  ·
                    refine ⟨732135265799100684655237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3904721417595203651494597 732135265799100684655237)
                    ·
                      rfl

theorem cell23_4277485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_4277485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277485 prefixEnd_4277485 := by exact prefixLift 4277485
  have htrace : WordTrace (prefixWord ++ tailWord_4277485) baseStart_4277485 baseEnd_4277485 := by
    simpa [prefixWord, tailWord_4277485, baseEnd_4277485] using wordTrace_append hprefix tailTrace_4277485
  have hstable : (prefixWord ++ tailWord_4277485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277485).length < 2 ^ (prefixWord ++ tailWord_4277485).sum := by decide
  have hdescent : baseEnd_4277485 < baseStart_4277485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277547 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 9]
def baseStart_4277547 : Nat := 118140960795 + 4277547 * 2 ^ 59
def prefixEnd_4277547 : Nat := 4983230072969 + 3 ^ 40 * 4277547 * 2
def baseEnd_4277547 : Nat := 2196437633197880811390425

theorem tailTrace_4277547 : CollatzResearch.WordTrace tailWord_4277547 prefixEnd_4277547 2196437633197880811390425 := by
  unfold tailWord_4277547
  simp only [CollatzResearch.WordTrace]
  refine ⟨156014956234185240710902895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104009970822790160473935263 156014956234185240710902895)
  ·
    refine ⟨234022434351277861066354343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156014956234185240710902895 234022434351277861066354343)
    ·
      refine ⟨351033651526916791599531515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234022434351277861066354343 351033651526916791599531515)
      ·
        refine ⟨526550477290375187399297273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351033651526916791599531515 526550477290375187399297273)
        ·
          refine ⟨394912857967781390549472955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 526550477290375187399297273 394912857967781390549472955)
          ·
            refine ⟨592369286951672085824209433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394912857967781390549472955 592369286951672085824209433)
            ·
              refine ⟨444276965213754064368157075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 592369286951672085824209433 444276965213754064368157075)
              ·
                refine ⟨666415447820631096552235613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444276965213754064368157075 666415447820631096552235613)
                ·
                  refine ⟨249905792932736661207088355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 666415447820631096552235613 249905792932736661207088355)
                  ·
                    refine ⟨374858689399104991810632533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 249905792932736661207088355 374858689399104991810632533)
                    ·
                      refine ⟨2196437633197880811390425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 374858689399104991810632533 2196437633197880811390425)
                      ·
                        rfl

theorem cell23_4277547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 9].length) (baseStart_4277547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277547 prefixEnd_4277547 := by exact prefixLift 4277547
  have htrace : WordTrace (prefixWord ++ tailWord_4277547) baseStart_4277547 baseEnd_4277547 := by
    simpa [prefixWord, tailWord_4277547, baseEnd_4277547] using wordTrace_append hprefix tailTrace_4277547
  have hstable : (prefixWord ++ tailWord_4277547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277547).length < 2 ^ (prefixWord ++ tailWord_4277547).sum := by decide
  have hdescent : baseEnd_4277547 < baseStart_4277547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277554 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 9]
def baseStart_4277554 : Nat := 118140960795 + 4277554 * 2 ^ 59
def prefixEnd_4277554 : Nat := 4983230072969 + 3 ^ 40 * 4277554 * 2
def baseEnd_4277554 : Nat := 244049025284718031555877

theorem tailTrace_4277554 : CollatzResearch.WordTrace tailWord_4277554 prefixEnd_4277554 244049025284718031555877 := by
  unfold tailWord_4277554
  simp only [CollatzResearch.WordTrace]
  refine ⟨39003802886289970226601929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104010141030106587270938477 39003802886289970226601929)
  ·
    refine ⟨29252852164717477669951447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39003802886289970226601929 29252852164717477669951447)
    ·
      refine ⟨43879278247076216504927171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29252852164717477669951447 43879278247076216504927171)
      ·
        refine ⟨65818917370614324757390757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43879278247076216504927171 65818917370614324757390757)
        ·
          refine ⟨12341047006990185892010767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65818917370614324757390757 12341047006990185892010767)
          ·
            refine ⟨18511570510485278838016151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12341047006990185892010767 18511570510485278838016151)
            ·
              refine ⟨27767355765727918257024227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18511570510485278838016151 27767355765727918257024227)
              ·
                refine ⟨41651033648591877385536341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27767355765727918257024227 41651033648591877385536341)
                ·
                  refine ⟨244049025284718031555877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41651033648591877385536341 244049025284718031555877)
                  ·
                    rfl

theorem cell23_4277554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_4277554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277554 prefixEnd_4277554 := by exact prefixLift 4277554
  have htrace : WordTrace (prefixWord ++ tailWord_4277554) baseStart_4277554 baseEnd_4277554 := by
    simpa [prefixWord, tailWord_4277554, baseEnd_4277554] using wordTrace_append hprefix tailTrace_4277554
  have hstable : (prefixWord ++ tailWord_4277554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277554).length < 2 ^ (prefixWord ++ tailWord_4277554).sum := by decide
  have hdescent : baseEnd_4277554 < baseStart_4277554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277584 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 4, 5]
def baseStart_4277584 : Nat := 118140960795 + 4277584 * 2 ^ 59
def prefixEnd_4277584 : Nat := 4983230072969 + 3 ^ 40 * 4277584 * 2
def baseEnd_4277584 : Nat := 732152210660699055542585

theorem tailTrace_4277584 : CollatzResearch.WordTrace tailWord_4277584 prefixEnd_4277584 732152210660699055542585 := by
  unfold tailWord_4277584
  simp only [CollatzResearch.WordTrace]
  refine ⟨78008152867525598014999903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104010870490034130686666537 78008152867525598014999903)
  ·
    refine ⟨117012229301288397022499855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78008152867525598014999903 117012229301288397022499855)
    ·
      refine ⟨175518343951932595533749783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117012229301288397022499855 175518343951932595533749783)
      ·
        refine ⟨263277515927898893300624675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175518343951932595533749783 263277515927898893300624675)
        ·
          refine ⟨394916273891848339950937013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263277515927898893300624675 394916273891848339950937013)
          ·
            refine ⟨37023400677360781870400345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 394916273891848339950937013 37023400677360781870400345)
            ·
              refine ⟨27767550508020586402800259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37023400677360781870400345 27767550508020586402800259)
              ·
                refine ⟨41651325762030879604200389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27767550508020586402800259 41651325762030879604200389)
                ·
                  refine ⟨7809623580380789925787573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41651325762030879604200389 7809623580380789925787573)
                  ·
                    refine ⟨732152210660699055542585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7809623580380789925787573 732152210660699055542585)
                    ·
                      rfl

theorem cell23_4277584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 4, 5].length) (baseStart_4277584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277584 prefixEnd_4277584 := by exact prefixLift 4277584
  have htrace : WordTrace (prefixWord ++ tailWord_4277584) baseStart_4277584 baseEnd_4277584 := by
    simpa [prefixWord, tailWord_4277584, baseEnd_4277584] using wordTrace_append hprefix tailTrace_4277584
  have hstable : (prefixWord ++ tailWord_4277584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277584).length < 2 ^ (prefixWord ++ tailWord_4277584).sum := by decide
  have hdescent : baseEnd_4277584 < baseStart_4277584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277594 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5]
def baseStart_4277594 : Nat := 118140960795 + 4277594 * 2 ^ 59
def prefixEnd_4277594 : Nat := 4983230072969 + 3 ^ 40 * 4277594 * 2
def baseEnd_4277594 : Nat := 2196461766788642127502709

theorem tailTrace_4277594 : CollatzResearch.WordTrace tailWord_4277594 prefixEnd_4277594 2196461766788642127502709 := by
  unfold tailWord_4277594
  simp only [CollatzResearch.WordTrace]
  refine ⟨39004167616253741934465959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104011113643343311825242557 39004167616253741934465959)
  ·
    refine ⟨58506251424380612901698939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39004167616253741934465959 58506251424380612901698939)
    ·
      refine ⟨87759377136570919352548409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58506251424380612901698939 87759377136570919352548409)
      ·
        refine ⟨65819532852428189514411307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87759377136570919352548409 65819532852428189514411307)
        ·
          refine ⟨98729299278642284271616961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65819532852428189514411307 98729299278642284271616961)
          ·
            refine ⟨74046974458981713203712721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98729299278642284271616961 74046974458981713203712721)
            ·
              refine ⟨55535230844236284902784541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74046974458981713203712721 55535230844236284902784541)
              ·
                refine ⟨20825711566588606838544203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55535230844236284902784541 20825711566588606838544203)
                ·
                  refine ⟨31238567349882910257816305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20825711566588606838544203 31238567349882910257816305)
                  ·
                    refine ⟨23428925512412182693362229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31238567349882910257816305 23428925512412182693362229)
                    ·
                      refine ⟨2196461766788642127502709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23428925512412182693362229 2196461766788642127502709)
                      ·
                        rfl

theorem cell23_4277594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_4277594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277594 prefixEnd_4277594 := by exact prefixLift 4277594
  have htrace : WordTrace (prefixWord ++ tailWord_4277594) baseStart_4277594 baseEnd_4277594 := by
    simpa [prefixWord, tailWord_4277594, baseEnd_4277594] using wordTrace_append hprefix tailTrace_4277594
  have hstable : (prefixWord ++ tailWord_4277594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277594).length < 2 ^ (prefixWord ++ tailWord_4277594).sum := by decide
  have hdescent : baseEnd_4277594 < baseStart_4277594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277644 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 8]
def baseStart_4277644 : Nat := 118140960795 + 4277644 * 2 ^ 59
def prefixEnd_4277644 : Nat := 4983230072969 + 3 ^ 40 * 4277644 * 2
def baseEnd_4277644 : Nat := 244054160091262992430831

theorem tailTrace_4277644 : CollatzResearch.WordTrace tailWord_4277644 prefixEnd_4277644 244054160091262992430831 := by
  unfold tailWord_4277644
  simp only [CollatzResearch.WordTrace]
  refine ⟨78009247057416913138591993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104012329409889217518122657 78009247057416913138591993)
  ·
    refine ⟨58506935293062684853943995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78009247057416913138591993 58506935293062684853943995)
    ·
      refine ⟨87760402939594027280915993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58506935293062684853943995 87760402939594027280915993)
      ·
        refine ⟨65820302204695520460686995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87760402939594027280915993 65820302204695520460686995)
        ·
          refine ⟨98730453307043280691030493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65820302204695520460686995 98730453307043280691030493)
          ·
            refine ⟨37023919990141230259136435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98730453307043280691030493 37023919990141230259136435)
            ·
              refine ⟨55535879985211845388704653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37023919990141230259136435 55535879985211845388704653)
              ·
                refine ⟨20825954994454442020764245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55535879985211845388704653 20825954994454442020764245)
                ·
                  refine ⟨244054160091262992430831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20825954994454442020764245 244054160091262992430831)
                  ·
                    rfl

theorem cell23_4277644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 8].length) (baseStart_4277644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277644 prefixEnd_4277644 := by exact prefixLift 4277644
  have htrace : WordTrace (prefixWord ++ tailWord_4277644) baseStart_4277644 baseEnd_4277644 := by
    simpa [prefixWord, tailWord_4277644, baseEnd_4277644] using wordTrace_append hprefix tailTrace_4277644
  have hstable : (prefixWord ++ tailWord_4277644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277644).length < 2 ^ (prefixWord ++ tailWord_4277644).sum := by decide
  have hdescent : baseEnd_4277644 < baseStart_4277644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277711 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 4]
def baseStart_4277711 : Nat := 118140960795 + 4277711 * 2 ^ 59
def prefixEnd_4277711 : Nat := 4983230072969 + 3 ^ 40 * 4277711 * 2
def baseEnd_4277711 : Nat := 2196521844025218169739671

theorem tailTrace_4277711 : CollatzResearch.WordTrace tailWord_4277711 prefixEnd_4277711 2196521844025218169739671 := by
  unfold tailWord_4277711
  simp only [CollatzResearch.WordTrace]
  refine ⟨156020937805591096719872987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104013958537060731146581991 156020937805591096719872987)
  ·
    refine ⟨234031406708386645079809481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156020937805591096719872987 234031406708386645079809481)
    ·
      refine ⟨175523555031289983809857111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234031406708386645079809481 175523555031289983809857111)
      ·
        refine ⟨263285332546934975714785667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175523555031289983809857111 263285332546934975714785667)
        ·
          refine ⟨394927998820402463572178501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263285332546934975714785667 394927998820402463572178501)
          ·
            refine ⟨74048999778825461919783469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 394927998820402463572178501 74048999778825461919783469)
            ·
              refine ⟨27768374917059548219918801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74048999778825461919783469 27768374917059548219918801)
              ·
                refine ⟨20826281187794661164939101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27768374917059548219918801 20826281187794661164939101)
                ·
                  refine ⟨7809855445422997936852163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20826281187794661164939101 7809855445422997936852163)
                  ·
                    refine ⟨11714783168134496905278245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7809855445422997936852163 11714783168134496905278245)
                    ·
                      refine ⟨2196521844025218169739671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11714783168134496905278245 2196521844025218169739671)
                      ·
                        rfl

theorem cell23_4277711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 4].length) (baseStart_4277711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277711 prefixEnd_4277711 := by exact prefixLift 4277711
  have htrace : WordTrace (prefixWord ++ tailWord_4277711) baseStart_4277711 baseEnd_4277711 := by
    simpa [prefixWord, tailWord_4277711, baseEnd_4277711] using wordTrace_append hprefix tailTrace_4277711
  have hstable : (prefixWord ++ tailWord_4277711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277711).length < 2 ^ (prefixWord ++ tailWord_4277711).sum := by decide
  have hdescent : baseEnd_4277711 < baseStart_4277711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277721 : List Nat := [1, 2, 1, 2, 4, 2, 1, 3, 1, 6]
def baseStart_4277721 : Nat := 118140960795 + 4277721 * 2 ^ 59
def prefixEnd_4277721 : Nat := 4983230072969 + 3 ^ 40 * 4277721 * 2
def baseEnd_4277721 : Nat := 732175659610587710204875

theorem tailTrace_4277721 : CollatzResearch.WordTrace tailWord_4277721 prefixEnd_4277721 732175659610587710204875 := by
  unfold tailWord_4277721
  simp only [CollatzResearch.WordTrace]
  refine ⟨156021302535554868427737017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104014201690369912285158011 156021302535554868427737017)
  ·
    refine ⟨117015976901666151320802763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156021302535554868427737017 117015976901666151320802763)
    ·
      refine ⟨175523965352499226981204145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117015976901666151320802763 175523965352499226981204145)
      ·
        refine ⟨131642974014374420235903109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175523965352499226981204145 131642974014374420235903109)
        ·
          refine ⟨24683057627695203794231833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131642974014374420235903109 24683057627695203794231833)
          ·
            refine ⟨18512293220771402845673875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24683057627695203794231833 18512293220771402845673875)
            ·
              refine ⟨27768439831157104268510813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18512293220771402845673875 27768439831157104268510813)
              ·
                refine ⟨10413164936683914100691555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27768439831157104268510813 10413164936683914100691555)
                ·
                  refine ⟨15619747405025871151037333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10413164936683914100691555 15619747405025871151037333)
                  ·
                    refine ⟨732175659610587710204875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15619747405025871151037333 732175659610587710204875)
                    ·
                      rfl

theorem cell23_4277721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 6].length) (baseStart_4277721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277721 prefixEnd_4277721 := by exact prefixLift 4277721
  have htrace : WordTrace (prefixWord ++ tailWord_4277721) baseStart_4277721 baseEnd_4277721 := by
    simpa [prefixWord, tailWord_4277721, baseEnd_4277721] using wordTrace_append hprefix tailTrace_4277721
  have hstable : (prefixWord ++ tailWord_4277721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277721).length < 2 ^ (prefixWord ++ tailWord_4277721).sum := by decide
  have hdescent : baseEnd_4277721 < baseStart_4277721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277745 : List Nat := [1, 2, 2, 2, 3, 2, 4, 1, 1, 1, 4]
def baseStart_4277745 : Nat := 118140960795 + 4277745 * 2 ^ 59
def prefixEnd_4277745 : Nat := 4983230072969 + 3 ^ 40 * 4277745 * 2
def baseEnd_4277745 : Nat := 2196539302367471036714515

theorem tailTrace_4277745 : CollatzResearch.WordTrace tailWord_4277745 prefixEnd_4277745 2196539302367471036714515 := by
  unfold tailWord_4277745
  simp only [CollatzResearch.WordTrace]
  refine ⟨156022177887467920526610689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104014785258311947017740459 156022177887467920526610689)
  ·
    refine ⟨117016633415600940394958017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156022177887467920526610689 117016633415600940394958017)
    ·
      refine ⟨87762475061700705296218513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117016633415600940394958017 87762475061700705296218513)
      ·
        refine ⟨65821856296275528972163885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87762475061700705296218513 65821856296275528972163885)
        ·
          refine ⟨24683196111103323364561457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65821856296275528972163885 24683196111103323364561457)
          ·
            refine ⟨18512397083327492523421093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24683196111103323364561457 18512397083327492523421093)
            ·
              refine ⟨3471074453123904848141455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18512397083327492523421093 3471074453123904848141455)
              ·
                refine ⟨5206611679685857272212183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3471074453123904848141455 5206611679685857272212183)
                ·
                  refine ⟨7809917519528785908318275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5206611679685857272212183 7809917519528785908318275)
                  ·
                    refine ⟨11714876279293178862477413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7809917519528785908318275 11714876279293178862477413)
                    ·
                      refine ⟨2196539302367471036714515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11714876279293178862477413 2196539302367471036714515)
                      ·
                        rfl

theorem cell23_4277745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_4277745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277745 prefixEnd_4277745 := by exact prefixLift 4277745
  have htrace : WordTrace (prefixWord ++ tailWord_4277745) baseStart_4277745 baseEnd_4277745 := by
    simpa [prefixWord, tailWord_4277745, baseEnd_4277745] using wordTrace_append hprefix tailTrace_4277745
  have hstable : (prefixWord ++ tailWord_4277745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277745).length < 2 ^ (prefixWord ++ tailWord_4277745).sum := by decide
  have hdescent : baseEnd_4277745 < baseStart_4277745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277772 : List Nat := [2, 2, 1, 2, 5, 1, 3, 1, 2, 4]
def baseStart_4277772 : Nat := 118140960795 + 4277772 * 2 ^ 59
def prefixEnd_4277772 : Nat := 4983230072969 + 3 ^ 40 * 4277772 * 2
def baseEnd_4277772 : Nat := 732184388781714143692297

theorem tailTrace_4277772 : CollatzResearch.WordTrace tailWord_4277772 prefixEnd_4277772 732184388781714143692297 := by
  unfold tailWord_4277772
  simp only [CollatzResearch.WordTrace]
  refine ⟨78011581329185052068921785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104015441772246736091895713 78011581329185052068921785)
  ·
    refine ⟨58508685996888789051691339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78011581329185052068921785 58508685996888789051691339)
    ·
      refine ⟨87763028995333183577537009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58508685996888789051691339 87763028995333183577537009)
      ·
        refine ⟨65822271746499887683152757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87763028995333183577537009 65822271746499887683152757)
        ·
          refine ⟨6170837976234364470295571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65822271746499887683152757 6170837976234364470295571)
          ·
            refine ⟨9256256964351546705443357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6170837976234364470295571 9256256964351546705443357)
            ·
              refine ⟨3471096361631830014541259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9256256964351546705443357 3471096361631830014541259)
              ·
                refine ⟨5206644542447745021811889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3471096361631830014541259 5206644542447745021811889)
                ·
                  refine ⟨3904983406835808766358917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5206644542447745021811889 3904983406835808766358917)
                  ·
                    refine ⟨732184388781714143692297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3904983406835808766358917 732184388781714143692297)
                    ·
                      rfl

theorem cell23_4277772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 2, 4].length) (baseStart_4277772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277772 prefixEnd_4277772 := by exact prefixLift 4277772
  have htrace : WordTrace (prefixWord ++ tailWord_4277772) baseStart_4277772 baseEnd_4277772 := by
    simpa [prefixWord, tailWord_4277772, baseEnd_4277772] using wordTrace_append hprefix tailTrace_4277772
  have hstable : (prefixWord ++ tailWord_4277772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277772).length < 2 ^ (prefixWord ++ tailWord_4277772).sum := by decide
  have hdescent : baseEnd_4277772 < baseStart_4277772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277790 : List Nat := [4, 3, 3, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_4277790 : Nat := 118140960795 + 4277790 * 2 ^ 59
def prefixEnd_4277790 : Nat := 4983230072969 + 3 ^ 40 * 4277790 * 2
def baseEnd_4277790 : Nat := 2196562408996923360651809

theorem tailTrace_4277790 : CollatzResearch.WordTrace tailWord_4277790 prefixEnd_4277790 2196562408996923360651809 := by
  unfold tailWord_4277790
  simp only [CollatzResearch.WordTrace]
  refine ⟨19502977396538111651499853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104015879448203262141332549 19502977396538111651499853)
  ·
    refine ⟨7313616523701791869312445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19502977396538111651499853 7313616523701791869312445)
    ·
      refine ⟨2742606196388171950992167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7313616523701791869312445 2742606196388171950992167)
      ·
        refine ⟨4113909294582257926488251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2742606196388171950992167 4113909294582257926488251)
        ·
          refine ⟨6170863941873386889732377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4113909294582257926488251 6170863941873386889732377)
          ·
            refine ⟨4628147956405040167299283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6170863941873386889732377 4628147956405040167299283)
            ·
              refine ⟨6942221934607560250948925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4628147956405040167299283 6942221934607560250948925)
              ·
                refine ⟨2603333225477835094105847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6942221934607560250948925 2603333225477835094105847)
                ·
                  refine ⟨3904999838216752641158771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2603333225477835094105847 3904999838216752641158771)
                  ·
                    refine ⟨5857499757325128961738157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3904999838216752641158771 5857499757325128961738157)
                    ·
                      refine ⟨2196562408996923360651809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5857499757325128961738157 2196562408996923360651809)
                      ·
                        rfl

theorem cell23_4277790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_4277790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277790 prefixEnd_4277790 := by exact prefixLift 4277790
  have htrace : WordTrace (prefixWord ++ tailWord_4277790) baseStart_4277790 baseEnd_4277790 := by
    simpa [prefixWord, tailWord_4277790, baseEnd_4277790] using wordTrace_append hprefix tailTrace_4277790
  have hstable : (prefixWord ++ tailWord_4277790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277790).length < 2 ^ (prefixWord ++ tailWord_4277790).sum := by decide
  have hdescent : baseEnd_4277790 < baseStart_4277790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277791 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 5]
def baseStart_4277791 : Nat := 118140960795 + 4277791 * 2 ^ 59
def prefixEnd_4277791 : Nat := 4983230072969 + 3 ^ 40 * 4277791 * 2
def baseEnd_4277791 : Nat := 2196562922477577856739303

theorem tailTrace_4277791 : CollatzResearch.WordTrace tailWord_4277791 prefixEnd_4277791 2196562922477577856739303 := by
  unfold tailWord_4277791
  simp only [CollatzResearch.WordTrace]
  refine ⟨156023855645301270382785227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104015903763534180255190151 156023855645301270382785227)
  ·
    refine ⟨234035783467951905574177841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156023855645301270382785227 234035783467951905574177841)
    ·
      refine ⟨175526837600963929180633381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234035783467951905574177841 175526837600963929180633381)
      ·
        refine ⟨32911282050180736721368759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 175526837600963929180633381 32911282050180736721368759)
        ·
          refine ⟨49366923075271105082053139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32911282050180736721368759 49366923075271105082053139)
          ·
            refine ⟨74050384612906657623079709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49366923075271105082053139 74050384612906657623079709)
            ·
              refine ⟨27768894229839996608654891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74050384612906657623079709 27768894229839996608654891)
              ·
                refine ⟨41653341344759994912982337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27768894229839996608654891 41653341344759994912982337)
                ·
                  refine ⟨31240006008569996184736753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41653341344759994912982337 31240006008569996184736753)
                  ·
                    refine ⟨23430004506427497138552565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31240006008569996184736753 23430004506427497138552565)
                    ·
                      refine ⟨2196562922477577856739303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23430004506427497138552565 2196562922477577856739303)
                      ·
                        rfl

theorem cell23_4277791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_4277791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277791 prefixEnd_4277791 := by exact prefixLift 4277791
  have htrace : WordTrace (prefixWord ++ tailWord_4277791) baseStart_4277791 baseEnd_4277791 := by
    simpa [prefixWord, tailWord_4277791, baseEnd_4277791] using wordTrace_append hprefix tailTrace_4277791
  have hstable : (prefixWord ++ tailWord_4277791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277791).length < 2 ^ (prefixWord ++ tailWord_4277791).sum := by decide
  have hdescent : baseEnd_4277791 < baseStart_4277791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277841 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 9]
def baseStart_4277841 : Nat := 118140960795 + 4277841 * 2 ^ 59
def prefixEnd_4277841 : Nat := 4983230072969 + 3 ^ 40 * 4277841 * 2
def baseEnd_4277841 : Nat := 244065399612255851234897

theorem tailTrace_4277841 : CollatzResearch.WordTrace tailWord_4277841 prefixEnd_4277841 244065399612255851234897 := by
  unfold tailWord_4277841
  simp only [CollatzResearch.WordTrace]
  refine ⟨156025679295120128922105377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104017119530080085948070251 156025679295120128922105377)
  ·
    refine ⟨117019259471340096691579033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156025679295120128922105377 117019259471340096691579033)
    ·
      refine ⟨87764444603505072518684275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117019259471340096691579033 87764444603505072518684275)
      ·
        refine ⟨131646666905257608778026413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87764444603505072518684275 131646666905257608778026413)
        ·
          refine ⟨49367500089471603291759905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131646666905257608778026413 49367500089471603291759905)
          ·
            refine ⟨37025625067103702468819929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49367500089471603291759905 37025625067103702468819929)
            ·
              refine ⟨27769218800327776851614947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37025625067103702468819929 27769218800327776851614947)
              ·
                refine ⟨41653828200491665277422421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27769218800327776851614947 41653828200491665277422421)
                ·
                  refine ⟨244065399612255851234897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41653828200491665277422421 244065399612255851234897)
                  ·
                    rfl

theorem cell23_4277841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 9].length) (baseStart_4277841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277841 prefixEnd_4277841 := by exact prefixLift 4277841
  have htrace : WordTrace (prefixWord ++ tailWord_4277841) baseStart_4277841 baseEnd_4277841 := by
    simpa [prefixWord, tailWord_4277841, baseEnd_4277841] using wordTrace_append hprefix tailTrace_4277841
  have hstable : (prefixWord ++ tailWord_4277841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277841).length < 2 ^ (prefixWord ++ tailWord_4277841).sum := by decide
  have hdescent : baseEnd_4277841 < baseStart_4277841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277852 : List Nat := [2, 2, 4, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_4277852 : Nat := 118140960795 + 4277852 * 2 ^ 59
def prefixEnd_4277852 : Nat := 4983230072969 + 3 ^ 40 * 4277852 * 2
def baseEnd_4277852 : Nat := 2196594244797502118076523

theorem tailTrace_4277852 : CollatzResearch.WordTrace tailWord_4277852 prefixEnd_4277852 2196594244797502118076523 := by
  unfold tailWord_4277852
  simp only [CollatzResearch.WordTrace]
  refine ⟨78013040249040138900377905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104017386998720185200503873 78013040249040138900377905)
  ·
    refine ⟨58509780186780104175283429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78013040249040138900377905 58509780186780104175283429)
    ·
      refine ⟨10970583785021269532865643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58509780186780104175283429 10970583785021269532865643)
      ·
        refine ⟨16455875677531904299298465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10970583785021269532865643 16455875677531904299298465)
        ·
          refine ⟨12341906758148928224473849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16455875677531904299298465 12341906758148928224473849)
          ·
            refine ⟨9256430068611696168355387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12341906758148928224473849 9256430068611696168355387)
            ·
              refine ⟨13884645102917544252533081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9256430068611696168355387 13884645102917544252533081)
              ·
                refine ⟨10413483827188158189399811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13884645102917544252533081 10413483827188158189399811)
                ·
                  refine ⟨15620225740782237284099717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10413483827188158189399811 15620225740782237284099717)
                  ·
                    refine ⟨2928792326396669490768697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15620225740782237284099717 2928792326396669490768697)
                    ·
                      refine ⟨2196594244797502118076523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2928792326396669490768697 2196594244797502118076523)
                      ·
                        rfl

theorem cell23_4277852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_4277852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277852 prefixEnd_4277852 := by exact prefixLift 4277852
  have htrace : WordTrace (prefixWord ++ tailWord_4277852) baseStart_4277852 baseEnd_4277852 := by
    simpa [prefixWord, tailWord_4277852, baseEnd_4277852] using wordTrace_append hprefix tailTrace_4277852
  have hstable : (prefixWord ++ tailWord_4277852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277852).length < 2 ^ (prefixWord ++ tailWord_4277852).sum := by decide
  have hdescent : baseEnd_4277852 < baseStart_4277852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277868 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 3]
def baseStart_4277868 : Nat := 118140960795 + 4277868 * 2 ^ 59
def prefixEnd_4277868 : Nat := 4983230072969 + 3 ^ 40 * 4277868 * 2
def baseEnd_4277868 : Nat := 2196602460487974055476449

theorem tailTrace_4277868 : CollatzResearch.WordTrace tailWord_4277868 prefixEnd_4277868 2196602460487974055476449 := by
  unfold tailWord_4277868
  simp only [CollatzResearch.WordTrace]
  refine ⟨78013332033011156266669129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104017776044014875022225505 78013332033011156266669129)
  ·
    refine ⟨58509999024758367200001847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78013332033011156266669129 58509999024758367200001847)
    ·
      refine ⟨87764998537137550800002771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58509999024758367200001847 87764998537137550800002771)
      ·
        refine ⟨131647497805706326200004157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87764998537137550800002771 131647497805706326200004157)
        ·
          refine ⟨49367811677139872325001559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131647497805706326200004157 49367811677139872325001559)
          ·
            refine ⟨74051717515709808487502339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49367811677139872325001559 74051717515709808487502339)
            ·
              refine ⟨111077576273564712731253509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74051717515709808487502339 111077576273564712731253509)
              ·
                refine ⟨20827045551293383637110033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111077576273564712731253509 20827045551293383637110033)
                ·
                  refine ⟨15620284163470037727832525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20827045551293383637110033 15620284163470037727832525)
                  ·
                    refine ⟨5857606561301264147937197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15620284163470037727832525 5857606561301264147937197)
                    ·
                      refine ⟨2196602460487974055476449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5857606561301264147937197 2196602460487974055476449)
                      ·
                        rfl

theorem cell23_4277868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_4277868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277868 prefixEnd_4277868 := by exact prefixLift 4277868
  have htrace : WordTrace (prefixWord ++ tailWord_4277868) baseStart_4277868 baseEnd_4277868 := by
    simpa [prefixWord, tailWord_4277868, baseEnd_4277868] using wordTrace_append hprefix tailTrace_4277868
  have hstable : (prefixWord ++ tailWord_4277868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277868).length < 2 ^ (prefixWord ++ tailWord_4277868).sum := by decide
  have hdescent : baseEnd_4277868 < baseStart_4277868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277871 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 3, 7]
def baseStart_4277871 : Nat := 118140960795 + 4277871 * 2 ^ 59
def prefixEnd_4277871 : Nat := 4983230072969 + 3 ^ 40 * 4277871 * 2
def baseEnd_4277871 : Nat := 732201333643312514579645

theorem tailTrace_4277871 : CollatzResearch.WordTrace tailWord_4277871 prefixEnd_4277871 732201333643312514579645 := by
  unfold tailWord_4277871
  simp only [CollatzResearch.WordTrace]
  refine ⟨156026773485011444045697467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104017848990007629363798311 156026773485011444045697467)
  ·
    refine ⟨234040160227517166068546201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156026773485011444045697467 234040160227517166068546201)
    ·
      refine ⟨175530120170637874551409651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234040160227517166068546201 175530120170637874551409651)
      ·
        refine ⟨263295180255956811827114477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175530120170637874551409651 263295180255956811827114477)
        ·
          refine ⟨98735692595983804435167929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 263295180255956811827114477 98735692595983804435167929)
          ·
            refine ⟨74051769446987853326375947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98735692595983804435167929 74051769446987853326375947)
            ·
              refine ⟨111077654170481779989563921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74051769446987853326375947 111077654170481779989563921)
              ·
                refine ⟨83308240627861334992172941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111077654170481779989563921 83308240627861334992172941)
                ·
                  refine ⟨31240590235448000622064853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83308240627861334992172941 31240590235448000622064853)
                  ·
                    refine ⟨732201333643312514579645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31240590235448000622064853 732201333643312514579645)
                    ·
                      rfl

theorem cell23_4277871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 7].length) (baseStart_4277871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277871 prefixEnd_4277871 := by exact prefixLift 4277871
  have htrace : WordTrace (prefixWord ++ tailWord_4277871) baseStart_4277871 baseEnd_4277871 := by
    simpa [prefixWord, tailWord_4277871, baseEnd_4277871] using wordTrace_append hprefix tailTrace_4277871
  have hstable : (prefixWord ++ tailWord_4277871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277871).length < 2 ^ (prefixWord ++ tailWord_4277871).sum := by decide
  have hdescent : baseEnd_4277871 < baseStart_4277871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277885 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 2, 3, 3]
def baseStart_4277885 : Nat := 118140960795 + 4277885 * 2 ^ 59
def prefixEnd_4277885 : Nat := 4983230072969 + 3 ^ 40 * 4277885 * 2
def baseEnd_4277885 : Nat := 2196611189659100488963871

theorem tailTrace_4277885 : CollatzResearch.WordTrace tailWord_4277885 prefixEnd_4277885 2196611189659100488963871 := by
  unfold tailWord_4277885
  simp only [CollatzResearch.WordTrace]
  refine ⟨156027284106960724436707109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104018189404640482957804739 156027284106960724436707109)
  ·
    refine ⟨29255115770055135831882583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156027284106960724436707109 29255115770055135831882583)
    ·
      refine ⟨43882673655082703747823875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29255115770055135831882583 43882673655082703747823875)
      ·
        refine ⟨65824010482624055621735813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43882673655082703747823875 65824010482624055621735813)
        ·
          refine ⟨12342001965492010429075465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65824010482624055621735813 12342001965492010429075465)
          ·
            refine ⟨9256501474119007821806599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12342001965492010429075465 9256501474119007821806599)
            ·
              refine ⟨13884752211178511732709899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9256501474119007821806599 13884752211178511732709899)
              ·
                refine ⟨20827128316767767599064849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13884752211178511732709899 20827128316767767599064849)
                ·
                  refine ⟨15620346237575825699298637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20827128316767767599064849 15620346237575825699298637)
                  ·
                    refine ⟨5857629839090934637236989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15620346237575825699298637 5857629839090934637236989)
                    ·
                      refine ⟨2196611189659100488963871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5857629839090934637236989 2196611189659100488963871)
                      ·
                        rfl

theorem cell23_4277885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_4277885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277885 prefixEnd_4277885 := by exact prefixLift 4277885
  have htrace : WordTrace (prefixWord ++ tailWord_4277885) baseStart_4277885 baseEnd_4277885 := by
    simpa [prefixWord, tailWord_4277885, baseEnd_4277885] using wordTrace_append hprefix tailTrace_4277885
  have hstable : (prefixWord ++ tailWord_4277885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277885).length < 2 ^ (prefixWord ++ tailWord_4277885).sum := by decide
  have hdescent : baseEnd_4277885 < baseStart_4277885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277925 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 2, 4, 2]
def baseStart_4277925 : Nat := 118140960795 + 4277925 * 2 ^ 59
def prefixEnd_4277925 : Nat := 4983230072969 + 3 ^ 40 * 4277925 * 2
def baseEnd_4277925 : Nat := 2196631728885280332463687

theorem tailTrace_4277925 : CollatzResearch.WordTrace tailWord_4277925 prefixEnd_4277925 2196631728885280332463687 := by
  unfold tailWord_4277925
  simp only [CollatzResearch.WordTrace]
  refine ⟨156028743026815811268163229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104019162017877207512108819 156028743026815811268163229)
  ·
    refine ⟨58510778635055929225561211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156028743026815811268163229 58510778635055929225561211)
    ·
      refine ⟨87766167952583893838341817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58510778635055929225561211 87766167952583893838341817)
      ·
        refine ⟨65824625964437920378756363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87766167952583893838341817 65824625964437920378756363)
        ·
          refine ⟨98736938946656880568134545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65824625964437920378756363 98736938946656880568134545)
          ·
            refine ⟨74052704209992660426100909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98736938946656880568134545 74052704209992660426100909)
            ·
              refine ⟨27769764078747247659787841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74052704209992660426100909 27769764078747247659787841)
              ·
                refine ⟨20827323059060435744840881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27769764078747247659787841 20827323059060435744840881)
                ·
                  refine ⟨15620492294295326808630661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20827323059060435744840881 15620492294295326808630661)
                  ·
                    refine ⟨2928842305180373776618249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15620492294295326808630661 2928842305180373776618249)
                    ·
                      refine ⟨2196631728885280332463687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2928842305180373776618249 2196631728885280332463687)
                      ·
                        rfl

theorem cell23_4277925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_4277925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277925 prefixEnd_4277925 := by exact prefixLift 4277925
  have htrace : WordTrace (prefixWord ++ tailWord_4277925) baseStart_4277925 baseEnd_4277925 := by
    simpa [prefixWord, tailWord_4277925, baseEnd_4277925] using wordTrace_append hprefix tailTrace_4277925
  have hstable : (prefixWord ++ tailWord_4277925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277925).length < 2 ^ (prefixWord ++ tailWord_4277925).sum := by decide
  have hdescent : baseEnd_4277925 < baseStart_4277925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277935 : List Nat := [1, 1, 2, 1, 2, 4, 4, 1, 3, 4]
def baseStart_4277935 : Nat := 118140960795 + 4277935 * 2 ^ 59
def prefixEnd_4277935 : Nat := 4983230072969 + 3 ^ 40 * 4277935 * 2
def baseEnd_4277935 : Nat := 732212287897275097779547

theorem tailTrace_4277935 : CollatzResearch.WordTrace tailWord_4277935 prefixEnd_4277935 732212287897275097779547 := by
  unfold tailWord_4277935
  simp only [CollatzResearch.WordTrace]
  refine ⟨156029107756779582976027259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104019405171186388650684839 156029107756779582976027259)
  ·
    refine ⟨234043661635169374464040889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156029107756779582976027259 234043661635169374464040889)
    ·
      refine ⟨175532746226377030848030667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234043661635169374464040889 175532746226377030848030667)
      ·
        refine ⟨263299119339565546272046001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175532746226377030848030667 263299119339565546272046001)
        ·
          refine ⟨197474339504674159704034501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263299119339565546272046001 197474339504674159704034501)
          ·
            refine ⟨37026438657126404944506469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 197474339504674159704034501 37026438657126404944506469)
            ·
              refine ⟨6942457248211200927094963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37026438657126404944506469 6942457248211200927094963)
              ·
                refine ⟨10413685872316801390642445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6942457248211200927094963 10413685872316801390642445)
                ·
                  refine ⟨3905132202118800521490917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10413685872316801390642445 3905132202118800521490917)
                  ·
                    refine ⟨732212287897275097779547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3905132202118800521490917 732212287897275097779547)
                    ·
                      rfl

theorem cell23_4277935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 4].length) (baseStart_4277935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277935 prefixEnd_4277935 := by exact prefixLift 4277935
  have htrace : WordTrace (prefixWord ++ tailWord_4277935) baseStart_4277935 baseEnd_4277935 := by
    simpa [prefixWord, tailWord_4277935, baseEnd_4277935] using wordTrace_append hprefix tailTrace_4277935
  have hstable : (prefixWord ++ tailWord_4277935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277935).length < 2 ^ (prefixWord ++ tailWord_4277935).sum := by decide
  have hdescent : baseEnd_4277935 < baseStart_4277935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277942 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_4277942 : Nat := 118140960795 + 4277942 * 2 ^ 59
def prefixEnd_4277942 : Nat := 4983230072969 + 3 ^ 40 * 4277942 * 2
def baseEnd_4277942 : Nat := 2196640458056406765951109

theorem tailTrace_4277942 : CollatzResearch.WordTrace tailWord_4277942 prefixEnd_4277942 2196640458056406765951109 := by
  unfold tailWord_4277942
  simp only [CollatzResearch.WordTrace]
  refine ⟨9751835191734638948220755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104019575378502815447688053 9751835191734638948220755)
  ·
    refine ⟨14627752787601958422331133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9751835191734638948220755 14627752787601958422331133)
    ·
      refine ⟨5485407295350734408374175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14627752787601958422331133 5485407295350734408374175)
      ·
        refine ⟨8228110943026101612561263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5485407295350734408374175 8228110943026101612561263)
        ·
          refine ⟨12342166414539152418841895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8228110943026101612561263 12342166414539152418841895)
          ·
            refine ⟨18513249621808728628262843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12342166414539152418841895 18513249621808728628262843)
            ·
              refine ⟨27769874432713092942394265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18513249621808728628262843 27769874432713092942394265)
              ·
                refine ⟨20827405824534819706795699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27769874432713092942394265 20827405824534819706795699)
                ·
                  refine ⟨31241108736802229560193549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20827405824534819706795699 31241108736802229560193549)
                  ·
                    refine ⟨11715415776300836085072581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31241108736802229560193549 11715415776300836085072581)
                    ·
                      refine ⟨2196640458056406765951109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11715415776300836085072581 2196640458056406765951109)
                      ·
                        rfl

theorem cell23_4277942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_4277942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277942 prefixEnd_4277942 := by exact prefixLift 4277942
  have htrace : WordTrace (prefixWord ++ tailWord_4277942) baseStart_4277942 baseEnd_4277942 := by
    simpa [prefixWord, tailWord_4277942, baseEnd_4277942] using wordTrace_append hprefix tailTrace_4277942
  have hstable : (prefixWord ++ tailWord_4277942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277942).length < 2 ^ (prefixWord ++ tailWord_4277942).sum := by decide
  have hdescent : baseEnd_4277942 < baseStart_4277942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4277969 : List Nat := [1, 2, 2, 1, 2, 6, 1, 3, 1, 4]
def baseStart_4277969 : Nat := 118140960795 + 4277969 * 2 ^ 59
def prefixEnd_4277969 : Nat := 4983230072969 + 3 ^ 40 * 4277969 * 2
def baseEnd_4277969 : Nat := 732218107344692720104495

theorem tailTrace_4277969 : CollatzResearch.WordTrace tailWord_4277969 prefixEnd_4277969 732218107344692720104495 := by
  unfold tailWord_4277969
  simp only [CollatzResearch.WordTrace]
  refine ⟨156030347838656406782764961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104020231892437604521843307 156030347838656406782764961)
  ·
    refine ⟨117022760878992305087073721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156030347838656406782764961 117022760878992305087073721)
    ·
      refine ⟨87767070659244228815305291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117022760878992305087073721 87767070659244228815305291)
      ·
        refine ⟨131650605988866343222957937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87767070659244228815305291 131650605988866343222957937)
        ·
          refine ⟨98737954491649757417218453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131650605988866343222957937 98737954491649757417218453)
          ·
            refine ⟨4628341616796082378932115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 98737954491649757417218453 4628341616796082378932115)
            ·
              refine ⟨6942512425194123568398173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4628341616796082378932115 6942512425194123568398173)
              ·
                refine ⟨2603442159447796338149315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6942512425194123568398173 2603442159447796338149315)
                ·
                  refine ⟨3905163239171694507223973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2603442159447796338149315 3905163239171694507223973)
                  ·
                    refine ⟨732218107344692720104495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3905163239171694507223973 732218107344692720104495)
                    ·
                      rfl

theorem cell23_4277969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 1, 4].length) (baseStart_4277969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4277969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4277969 prefixEnd_4277969 := by exact prefixLift 4277969
  have htrace : WordTrace (prefixWord ++ tailWord_4277969) baseStart_4277969 baseEnd_4277969 := by
    simpa [prefixWord, tailWord_4277969, baseEnd_4277969] using wordTrace_append hprefix tailTrace_4277969
  have hstable : (prefixWord ++ tailWord_4277969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4277969).length < 2 ^ (prefixWord ++ tailWord_4277969).sum := by decide
  have hdescent : baseEnd_4277969 < baseStart_4277969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4277969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278002 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 4, 3, 2]
def baseStart_4278002 : Nat := 118140960795 + 4278002 * 2 ^ 59
def prefixEnd_4278002 : Nat := 4983230072969 + 3 ^ 40 * 4278002 * 2
def baseEnd_4278002 : Nat := 2196671266895676531200833

theorem tailTrace_4278002 : CollatzResearch.WordTrace tailWord_4278002 prefixEnd_4278002 2196671266895676531200833 := by
  unfold tailWord_4278002
  simp only [CollatzResearch.WordTrace]
  refine ⟨39007887861884213354679065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104021034298357902279144173 39007887861884213354679065)
  ·
    refine ⟨29255915896413160016009299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39007887861884213354679065 29255915896413160016009299)
    ·
      refine ⟨43883873844619740024013949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29255915896413160016009299 43883873844619740024013949)
      ·
        refine ⟨16456452691732402509005231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43883873844619740024013949 16456452691732402509005231)
        ·
          refine ⟨24684679037598603763507847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16456452691732402509005231 24684679037598603763507847)
          ·
            refine ⟨37027018556397905645261771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24684679037598603763507847 37027018556397905645261771)
            ·
              refine ⟨55540527834596858467892657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37027018556397905645261771 55540527834596858467892657)
              ·
                refine ⟨41655395875947643850919493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55540527834596858467892657 41655395875947643850919493)
                ·
                  refine ⟨7810386726740183222047405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41655395875947643850919493 7810386726740183222047405)
                  ·
                    refine ⟨2928895022527568708267777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7810386726740183222047405 2928895022527568708267777)
                    ·
                      refine ⟨2196671266895676531200833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2928895022527568708267777 2196671266895676531200833)
                      ·
                        rfl

theorem cell23_4278002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_4278002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278002 prefixEnd_4278002 := by exact prefixLift 4278002
  have htrace : WordTrace (prefixWord ++ tailWord_4278002) baseStart_4278002 baseEnd_4278002 := by
    simpa [prefixWord, tailWord_4278002, baseEnd_4278002] using wordTrace_append hprefix tailTrace_4278002
  have hstable : (prefixWord ++ tailWord_4278002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278002).length < 2 ^ (prefixWord ++ tailWord_4278002).sum := by decide
  have hdescent : baseEnd_4278002 < baseStart_4278002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278015 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 2, 6, 2]
def baseStart_4278015 : Nat := 118140960795 + 4278015 * 2 ^ 59
def prefixEnd_4278015 : Nat := 4983230072969 + 3 ^ 40 * 4278015 * 2
def baseEnd_4278015 : Nat := 2196677942144184980338273

theorem tailTrace_4278015 : CollatzResearch.WordTrace tailWord_4278015 prefixEnd_4278015 2196677942144184980338273 := by
  unfold tailWord_4278015
  simp only [CollatzResearch.WordTrace]
  refine ⟨156032025596489756638939499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104021350397659837759292999 156032025596489756638939499)
  ·
    refine ⟨234048038394734634958409249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156032025596489756638939499 234048038394734634958409249)
    ·
      refine ⟨175536028796050976218806937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234048038394734634958409249 175536028796050976218806937)
      ·
        refine ⟨131652021597038232164105203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175536028796050976218806937 131652021597038232164105203)
        ·
          refine ⟨197478032395557348246157805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131652021597038232164105203 197478032395557348246157805)
          ·
            refine ⟨74054262148334005592309177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197478032395557348246157805 74054262148334005592309177)
            ·
              refine ⟨55540696611250504194231883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74054262148334005592309177 55540696611250504194231883)
              ·
                refine ⟨83311044916875756291347825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55540696611250504194231883 83311044916875756291347825)
                ·
                  refine ⟨62483283687656817218510869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83311044916875756291347825 62483283687656817218510869)
                  ·
                    refine ⟨2928903922858913307117697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62483283687656817218510869 2928903922858913307117697)
                    ·
                      refine ⟨2196677942144184980338273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2928903922858913307117697 2196677942144184980338273)
                      ·
                        rfl

theorem cell23_4278015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 6, 2].length) (baseStart_4278015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278015 prefixEnd_4278015 := by exact prefixLift 4278015
  have htrace : WordTrace (prefixWord ++ tailWord_4278015) baseStart_4278015 baseEnd_4278015 := by
    simpa [prefixWord, tailWord_4278015, baseEnd_4278015] using wordTrace_append hprefix tailTrace_4278015
  have hstable : (prefixWord ++ tailWord_4278015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278015).length < 2 ^ (prefixWord ++ tailWord_4278015).sum := by decide
  have hdescent : baseEnd_4278015 < baseStart_4278015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278042 : List Nat := [3, 1, 1, 3, 2, 2, 1, 4, 2, 4]
def baseStart_4278042 : Nat := 118140960795 + 4278042 * 2 ^ 59
def prefixEnd_4278042 : Nat := 4983230072969 + 3 ^ 40 * 4278042 * 2
def baseEnd_4278042 : Nat := 732230602040618791566883

theorem tailTrace_4278042 : CollatzResearch.WordTrace tailWord_4278042 prefixEnd_4278042 732230602040618791566883 := by
  unfold tailWord_4278042
  simp only [CollatzResearch.WordTrace]
  refine ⟨39008252591847985062543095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104022006911594626833448253 39008252591847985062543095)
  ·
    refine ⟨58512378887771977593814643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39008252591847985062543095 58512378887771977593814643)
    ·
      refine ⟨87768568331657966390721965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58512378887771977593814643 87768568331657966390721965)
      ·
        refine ⟨32913213124371737396520737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87768568331657966390721965 32913213124371737396520737)
        ·
          refine ⟨24684909843278803047390553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32913213124371737396520737 24684909843278803047390553)
          ·
            refine ⟨18513682382459102285542915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24684909843278803047390553 18513682382459102285542915)
            ·
              refine ⟨27770523573688653428314373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18513682382459102285542915 27770523573688653428314373)
              ·
                refine ⟨5206973170066622517808945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27770523573688653428314373 5206973170066622517808945)
                ·
                  refine ⟨3905229877549966888356709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5206973170066622517808945 3905229877549966888356709)
                  ·
                    refine ⟨732230602040618791566883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3905229877549966888356709 732230602040618791566883)
                    ·
                      rfl

theorem cell23_4278042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 2, 4].length) (baseStart_4278042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278042 prefixEnd_4278042 := by exact prefixLift 4278042
  have htrace : WordTrace (prefixWord ++ tailWord_4278042) baseStart_4278042 baseEnd_4278042 := by
    simpa [prefixWord, tailWord_4278042, baseEnd_4278042] using wordTrace_append hprefix tailTrace_4278042
  have hstable : (prefixWord ++ tailWord_4278042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278042).length < 2 ^ (prefixWord ++ tailWord_4278042).sum := by decide
  have hdescent : baseEnd_4278042 < baseStart_4278042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278052 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 3, 2, 3]
def baseStart_4278052 : Nat := 118140960795 + 4278052 * 2 ^ 59
def prefixEnd_4278052 : Nat := 4983230072969 + 3 ^ 40 * 4278052 * 2
def baseEnd_4278052 : Nat := 2196696940928401335575603

theorem tailTrace_4278052 : CollatzResearch.WordTrace tailWord_4278052 prefixEnd_4278052 2196696940928401335575603 := by
  unfold tailWord_4278052
  simp only [CollatzResearch.WordTrace]
  refine ⟨78016687548677855979018205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104022250064903807972024273 78016687548677855979018205)
  ·
    refine ⟨29256257830754195992131827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78016687548677855979018205 29256257830754195992131827)
    ·
      refine ⟨43884386746131293988197741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29256257830754195992131827 43884386746131293988197741)
      ·
        refine ⟨16456645029799235245574153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43884386746131293988197741 16456645029799235245574153)
        ·
          refine ⟨12342483772349426434180615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16456645029799235245574153 12342483772349426434180615)
          ·
            refine ⟨18513725658524139651270923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12342483772349426434180615 18513725658524139651270923)
            ·
              refine ⟨27770588487786209476906385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18513725658524139651270923 27770588487786209476906385)
              ·
                refine ⟨20827941365839657107679789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27770588487786209476906385 20827941365839657107679789)
                ·
                  refine ⟨7810478012189871415379921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20827941365839657107679789 7810478012189871415379921)
                  ·
                    refine ⟨5857858509142403561534941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7810478012189871415379921 5857858509142403561534941)
                    ·
                      refine ⟨2196696940928401335575603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5857858509142403561534941 2196696940928401335575603)
                      ·
                        rfl

theorem cell23_4278052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_4278052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278052 prefixEnd_4278052 := by exact prefixLift 4278052
  have htrace : WordTrace (prefixWord ++ tailWord_4278052) baseStart_4278052 baseEnd_4278052 := by
    simpa [prefixWord, tailWord_4278052, baseEnd_4278052] using wordTrace_append hprefix tailTrace_4278052
  have hstable : (prefixWord ++ tailWord_4278052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278052).length < 2 ^ (prefixWord ++ tailWord_4278052).sum := by decide
  have hdescent : baseEnd_4278052 < baseStart_4278052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278116 : List Nat := [2, 3, 1, 1, 6, 1, 1, 1, 1, 3, 3]
def baseStart_4278116 : Nat := 118140960795 + 4278116 * 2 ^ 59
def prefixEnd_4278116 : Nat := 4983230072969 + 3 ^ 40 * 4278116 * 2
def baseEnd_4278116 : Nat := 2196729803690289085175309

theorem tailTrace_4278116 : CollatzResearch.WordTrace tailWord_4278116 prefixEnd_4278116 2196729803690289085175309 := by
  unfold tailWord_4278116
  simp only [CollatzResearch.WordTrace]
  refine ⟨78017854684561925444183101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104023806246082567258910801 78017854684561925444183101)
  ·
    refine ⟨29256695506710722041568663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78017854684561925444183101 29256695506710722041568663)
    ·
      refine ⟨43885043260066083062352995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29256695506710722041568663 43885043260066083062352995)
      ·
        refine ⟨65827564890099124593529493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43885043260066083062352995 65827564890099124593529493)
        ·
          refine ⟨3085667104223396465321695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65827564890099124593529493 3085667104223396465321695)
          ·
            refine ⟨4628500656335094697982543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3085667104223396465321695 4628500656335094697982543)
            ·
              refine ⟨6942750984502642046973815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4628500656335094697982543 6942750984502642046973815)
              ·
                refine ⟨10414126476753963070460723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6942750984502642046973815 10414126476753963070460723)
                ·
                  refine ⟨15621189715130944605691085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10414126476753963070460723 15621189715130944605691085)
                  ·
                    refine ⟨5857946143174104227134157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15621189715130944605691085 5857946143174104227134157)
                    ·
                      refine ⟨2196729803690289085175309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5857946143174104227134157 2196729803690289085175309)
                      ·
                        rfl

theorem cell23_4278116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_4278116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278116 prefixEnd_4278116 := by exact prefixLift 4278116
  have htrace : WordTrace (prefixWord ++ tailWord_4278116) baseStart_4278116 baseEnd_4278116 := by
    simpa [prefixWord, tailWord_4278116, baseEnd_4278116] using wordTrace_append hprefix tailTrace_4278116
  have hstable : (prefixWord ++ tailWord_4278116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278116).length < 2 ^ (prefixWord ++ tailWord_4278116).sum := by decide
  have hdescent : baseEnd_4278116 < baseStart_4278116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278126 : List Nat := [4, 1, 2, 3, 1, 1, 1, 4, 1, 3, 2]
def baseStart_4278126 : Nat := 118140960795 + 4278126 * 2 ^ 59
def prefixEnd_4278126 : Nat := 4983230072969 + 3 ^ 40 * 4278126 * 2
def baseEnd_4278126 : Nat := 2196734938496834046050263

theorem tailTrace_4278126 : CollatzResearch.WordTrace tailWord_4278126 prefixEnd_4278126 2196734938496834046050263 := by
  unfold tailWord_4278126
  simp only [CollatzResearch.WordTrace]
  refine ⟨19504509262385952824528779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104024049399391748397486821 19504509262385952824528779)
  ·
    refine ⟨29256763893578929236793169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19504509262385952824528779 29256763893578929236793169)
    ·
      refine ⟨21942572920184196927594877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29256763893578929236793169 21942572920184196927594877)
      ·
        refine ⟨8228464845069073847848079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21942572920184196927594877 8228464845069073847848079)
        ·
          refine ⟨12342697267603610771772119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8228464845069073847848079 12342697267603610771772119)
          ·
            refine ⟨18514045901405416157658179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12342697267603610771772119 18514045901405416157658179)
            ·
              refine ⟨27771068852108124236487269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18514045901405416157658179 27771068852108124236487269)
              ·
                refine ⟨5207075409770273294341363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27771068852108124236487269 5207075409770273294341363)
                ·
                  refine ⟨7810613114655409941512045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5207075409770273294341363 7810613114655409941512045)
                  ·
                    refine ⟨2928979917995778728067017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7810613114655409941512045 2928979917995778728067017)
                    ·
                      refine ⟨2196734938496834046050263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2928979917995778728067017 2196734938496834046050263)
                      ·
                        rfl

theorem cell23_4278126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_4278126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278126 prefixEnd_4278126 := by exact prefixLift 4278126
  have htrace : WordTrace (prefixWord ++ tailWord_4278126) baseStart_4278126 baseEnd_4278126 := by
    simpa [prefixWord, tailWord_4278126, baseEnd_4278126] using wordTrace_append hprefix tailTrace_4278126
  have hstable : (prefixWord ++ tailWord_4278126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278126).length < 2 ^ (prefixWord ++ tailWord_4278126).sum := by decide
  have hdescent : baseEnd_4278126 < baseStart_4278126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278173 : List Nat := [1, 4, 2, 1, 2, 2, 4, 1, 2, 2, 2]
def baseStart_4278173 : Nat := 118140960795 + 4278173 * 2 ^ 59
def prefixEnd_4278173 : Nat := 4983230072969 + 3 ^ 40 * 4278173 * 2
def baseEnd_4278173 : Nat := 2196759072087595362162547

theorem tailTrace_4278173 : CollatzResearch.WordTrace tailWord_4278173 prefixEnd_4278173 2196759072087595362162547 := by
  unfold tailWord_4278173
  simp only [CollatzResearch.WordTrace]
  refine ⟨156037788329917349623191173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104025192219944899748794115 156037788329917349623191173)
  ·
    refine ⟨29257085311859503054348345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156037788329917349623191173 29257085311859503054348345)
    ·
      refine ⟨21942813983894627290761259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29257085311859503054348345 21942813983894627290761259)
      ·
        refine ⟨32914220975841940936141889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21942813983894627290761259 32914220975841940936141889)
        ·
          refine ⟨24685665731881455702106417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32914220975841940936141889 24685665731881455702106417)
          ·
            refine ⟨18514249298911091776579813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24685665731881455702106417 18514249298911091776579813)
            ·
              refine ⟨3471421743545829708108715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18514249298911091776579813 3471421743545829708108715)
              ·
                refine ⟨5207132615318744562163073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3471421743545829708108715 5207132615318744562163073)
                ·
                  refine ⟨3905349461489058421622305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5207132615318744562163073 3905349461489058421622305)
                  ·
                    refine ⟨2929012096116793816216729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3905349461489058421622305 2929012096116793816216729)
                    ·
                      refine ⟨2196759072087595362162547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2929012096116793816216729 2196759072087595362162547)
                      ·
                        rfl

theorem cell23_4278173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_4278173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278173 prefixEnd_4278173 := by exact prefixLift 4278173
  have htrace : WordTrace (prefixWord ++ tailWord_4278173) baseStart_4278173 baseEnd_4278173 := by
    simpa [prefixWord, tailWord_4278173, baseEnd_4278173] using wordTrace_append hprefix tailTrace_4278173
  have hstable : (prefixWord ++ tailWord_4278173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278173).length < 2 ^ (prefixWord ++ tailWord_4278173).sum := by decide
  have hdescent : baseEnd_4278173 < baseStart_4278173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278190 : List Nat := [4, 1, 5, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_4278190 : Nat := 118140960795 + 4278190 * 2 ^ 59
def prefixEnd_4278190 : Nat := 4983230072969 + 3 ^ 40 * 4278190 * 2
def baseEnd_4278190 : Nat := 2196767801258721795649969

theorem tailTrace_4278190 : CollatzResearch.WordTrace tailWord_4278190 prefixEnd_4278190 2196767801258721795649969 := by
  unfold tailWord_4278190
  simp only [CollatzResearch.WordTrace]
  refine ⟨19504801046356970190820003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104025605580570507684373349 19504801046356970190820003)
  ·
    refine ⟨29257201569535455286230005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19504801046356970190820003 29257201569535455286230005)
    ·
      refine ⟨2742862647143948933084063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29257201569535455286230005 2742862647143948933084063)
      ·
        refine ⟨4114293970715923399626095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2742862647143948933084063 4114293970715923399626095)
        ·
          refine ⟨6171440956073885099439143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4114293970715923399626095 6171440956073885099439143)
          ·
            refine ⟨9257161434110827649158715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6171440956073885099439143 9257161434110827649158715)
            ·
              refine ⟨13885742151166241473738073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9257161434110827649158715 13885742151166241473738073)
              ·
                refine ⟨10414306613374681105303555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13885742151166241473738073 10414306613374681105303555)
                ·
                  refine ⟨15621459920062021657955333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10414306613374681105303555 15621459920062021657955333)
                  ·
                    refine ⟨2929023735011629060866625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15621459920062021657955333 2929023735011629060866625)
                    ·
                      refine ⟨2196767801258721795649969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2929023735011629060866625 2196767801258721795649969)
                      ·
                        rfl

theorem cell23_4278190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_4278190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278190 prefixEnd_4278190 := by exact prefixLift 4278190
  have htrace : WordTrace (prefixWord ++ tailWord_4278190) baseStart_4278190 baseEnd_4278190 := by
    simpa [prefixWord, tailWord_4278190, baseEnd_4278190] using wordTrace_append hprefix tailTrace_4278190
  have hstable : (prefixWord ++ tailWord_4278190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278190).length < 2 ^ (prefixWord ++ tailWord_4278190).sum := by decide
  have hdescent : baseEnd_4278190 < baseStart_4278190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278215 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_4278215 : Nat := 118140960795 + 4278215 * 2 ^ 59
def prefixEnd_4278215 : Nat := 4983230072969 + 3 ^ 40 * 4278215 * 2
def baseEnd_4278215 : Nat := 2196780638275084197837353

theorem tailTrace_4278215 : CollatzResearch.WordTrace tailWord_4278215 prefixEnd_4278215 2196780638275084197837353 := by
  unfold tailWord_4278215
  simp only [CollatzResearch.WordTrace]
  refine ⟨156039320195765190796220099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104026213463843460530813399 156039320195765190796220099)
  ·
    refine ⟨234058980293647786194330149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156039320195765190796220099 234058980293647786194330149)
    ·
      refine ⟨43886058805058959911436903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 234058980293647786194330149 43886058805058959911436903)
      ·
        refine ⟨65829088207588439867155355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43886058805058959911436903 65829088207588439867155355)
        ·
          refine ⟨98743632311382659800733033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65829088207588439867155355 98743632311382659800733033)
          ·
            refine ⟨74057724233536994850549775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98743632311382659800733033 74057724233536994850549775)
            ·
              refine ⟨111086586350305492275824663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74057724233536994850549775 111086586350305492275824663)
              ·
                refine ⟨166629879525458238413736995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111086586350305492275824663 166629879525458238413736995)
                ·
                  refine ⟨249944819288187357620605493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166629879525458238413736995 249944819288187357620605493)
                  ·
                    refine ⟨23432326808267564776931765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 249944819288187357620605493 23432326808267564776931765)
                    ·
                      refine ⟨2196780638275084197837353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23432326808267564776931765 2196780638275084197837353)
                      ·
                        rfl

theorem cell23_4278215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_4278215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278215 prefixEnd_4278215 := by exact prefixLift 4278215
  have htrace : WordTrace (prefixWord ++ tailWord_4278215) baseStart_4278215 baseEnd_4278215 := by
    simpa [prefixWord, tailWord_4278215, baseEnd_4278215] using wordTrace_append hprefix tailTrace_4278215
  have hstable : (prefixWord ++ tailWord_4278215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278215).length < 2 ^ (prefixWord ++ tailWord_4278215).sum := by decide
  have hdescent : baseEnd_4278215 < baseStart_4278215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278225 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 4, 1, 6]
def baseStart_4278225 : Nat := 118140960795 + 4278225 * 2 ^ 59
def prefixEnd_4278225 : Nat := 4983230072969 + 3 ^ 40 * 4278225 * 2
def baseEnd_4278225 : Nat := 2196785773081629158712307

theorem tailTrace_4278225 : CollatzResearch.WordTrace tailWord_4278225 prefixEnd_4278225 2196785773081629158712307 := by
  unfold tailWord_4278225
  simp only [CollatzResearch.WordTrace]
  refine ⟨156039684925728962504084129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104026456617152641669389419 156039684925728962504084129)
  ·
    refine ⟨117029763694296721878063097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156039684925728962504084129 117029763694296721878063097)
    ·
      refine ⟨87772322770722541408547323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117029763694296721878063097 87772322770722541408547323)
      ·
        refine ⟨131658484156083812112820985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87772322770722541408547323 131658484156083812112820985)
        ·
          refine ⟨98743863117062859084615739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131658484156083812112820985 98743863117062859084615739)
          ·
            refine ⟨148115794675594288626923609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98743863117062859084615739 148115794675594288626923609)
            ·
              refine ⟨111086846006695716470192707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148115794675594288626923609 111086846006695716470192707)
              ·
                refine ⟨166630269010043574705289061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111086846006695716470192707 166630269010043574705289061)
                ·
                  refine ⟨31243175439383170257241699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 166630269010043574705289061 31243175439383170257241699)
                  ·
                    refine ⟨46864763159074755385862549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31243175439383170257241699 46864763159074755385862549)
                    ·
                      refine ⟨2196785773081629158712307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46864763159074755385862549 2196785773081629158712307)
                      ·
                        rfl

theorem cell23_4278225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_4278225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278225 prefixEnd_4278225 := by exact prefixLift 4278225
  have htrace : WordTrace (prefixWord ++ tailWord_4278225) baseStart_4278225 baseEnd_4278225 := by
    simpa [prefixWord, tailWord_4278225, baseEnd_4278225] using wordTrace_append hprefix tailTrace_4278225
  have hstable : (prefixWord ++ tailWord_4278225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278225).length < 2 ^ (prefixWord ++ tailWord_4278225).sum := by decide
  have hdescent : baseEnd_4278225 < baseStart_4278225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278229 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 1, 6, 2]
def baseStart_4278229 : Nat := 118140960795 + 4278229 * 2 ^ 59
def prefixEnd_4278229 : Nat := 4983230072969 + 3 ^ 40 * 4278229 * 2
def baseEnd_4278229 : Nat := 2196787827004247143062289

theorem tailTrace_4278229 : CollatzResearch.WordTrace tailWord_4278229 prefixEnd_4278229 2196787827004247143062289 := by
  unfold tailWord_4278229
  simp only [CollatzResearch.WordTrace]
  refine ⟨156039830817714471187229741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104026553878476314124819827 156039830817714471187229741)
  ·
    refine ⟨58514936556642926695211153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156039830817714471187229741 58514936556642926695211153)
    ·
      refine ⟨43886202417482195021408365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58514936556642926695211153 43886202417482195021408365)
      ·
        refine ⟨16457325906555823133028137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43886202417482195021408365 16457325906555823133028137)
        ·
          refine ⟨12342994429916867349771103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16457325906555823133028137 12342994429916867349771103)
          ·
            refine ⟨18514491644875301024656655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12342994429916867349771103 18514491644875301024656655)
            ·
              refine ⟨27771737467312951536984983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18514491644875301024656655 27771737467312951536984983)
              ·
                refine ⟨41657606200969427305477475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27771737467312951536984983 41657606200969427305477475)
                ·
                  refine ⟨62486409301454140958216213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41657606200969427305477475 62486409301454140958216213)
                  ·
                    refine ⟨2929050436005662857416385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62486409301454140958216213 2929050436005662857416385)
                    ·
                      refine ⟨2196787827004247143062289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2929050436005662857416385 2196787827004247143062289)
                      ·
                        rfl

theorem cell23_4278229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_4278229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278229 prefixEnd_4278229 := by exact prefixLift 4278229
  have htrace : WordTrace (prefixWord ++ tailWord_4278229) baseStart_4278229 baseEnd_4278229 := by
    simpa [prefixWord, tailWord_4278229, baseEnd_4278229] using wordTrace_append hprefix tailTrace_4278229
  have hstable : (prefixWord ++ tailWord_4278229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278229).length < 2 ^ (prefixWord ++ tailWord_4278229).sum := by decide
  have hdescent : baseEnd_4278229 < baseStart_4278229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278232 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 1, 4, 3]
def baseStart_4278232 : Nat := 118140960795 + 4278232 * 2 ^ 59
def prefixEnd_4278232 : Nat := 4983230072969 + 3 ^ 40 * 4278232 * 2
def baseEnd_4278232 : Nat := 2196789367446210631324775

theorem tailTrace_4278232 : CollatzResearch.WordTrace tailWord_4278232 prefixEnd_4278232 2196789367446210631324775 := by
  unfold tailWord_4278232
  simp only [CollatzResearch.WordTrace]
  refine ⟨78019970118351801349794475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104026626824469068466392633 78019970118351801349794475)
  ·
    refine ⟨117029955177527702024691713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78019970118351801349794475 117029955177527702024691713)
    ·
      refine ⟨87772466383145776518518785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117029955177527702024691713 87772466383145776518518785)
      ·
        refine ⟨65829349787359332388889089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87772466383145776518518785 65829349787359332388889089)
        ·
          refine ⟨49372012340519499291666817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65829349787359332388889089 49372012340519499291666817)
          ·
            refine ⟨37029009255389624468750113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49372012340519499291666817 37029009255389624468750113)
            ·
              refine ⟨27771756941542218351562585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37029009255389624468750113 27771756941542218351562585)
              ·
                refine ⟨20828817706156663763671939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27771756941542218351562585 20828817706156663763671939)
                ·
                  refine ⟨31243226559234995645507909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20828817706156663763671939 31243226559234995645507909)
                  ·
                    refine ⟨5858104979856561683532733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31243226559234995645507909 5858104979856561683532733)
                    ·
                      refine ⟨2196789367446210631324775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5858104979856561683532733 2196789367446210631324775)
                      ·
                        rfl

theorem cell23_4278232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_4278232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278232 prefixEnd_4278232 := by exact prefixLift 4278232
  have htrace : WordTrace (prefixWord ++ tailWord_4278232) baseStart_4278232 baseEnd_4278232 := by
    simpa [prefixWord, tailWord_4278232, baseEnd_4278232] using wordTrace_append hprefix tailTrace_4278232
  have hstable : (prefixWord ++ tailWord_4278232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278232).length < 2 ^ (prefixWord ++ tailWord_4278232).sum := by decide
  have hdescent : baseEnd_4278232 < baseStart_4278232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278239 : List Nat := [1, 1, 2, 3, 4, 2, 1, 2, 3, 4]
def baseStart_4278239 : Nat := 118140960795 + 4278239 * 2 ^ 59
def prefixEnd_4278239 : Nat := 4983230072969 + 3 ^ 40 * 4278239 * 2
def baseEnd_4278239 : Nat := 732264320603597367979081

theorem tailTrace_4278239 : CollatzResearch.WordTrace tailWord_4278239 prefixEnd_4278239 732264320603597367979081 := by
  unfold tailWord_4278239
  simp only [CollatzResearch.WordTrace]
  refine ⟨156040195547678242895093771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104026797031785495263395847 156040195547678242895093771)
  ·
    refine ⟨234060293321517364342640657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156040195547678242895093771 234060293321517364342640657)
    ·
      refine ⟨175545219991138023256980493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234060293321517364342640657 175545219991138023256980493)
      ·
        refine ⟨65829457496676758721367685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175545219991138023256980493 65829457496676758721367685)
        ·
          refine ⟨12343023280626892260256441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65829457496676758721367685 12343023280626892260256441)
          ·
            refine ⟨9257267460470169195192331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12343023280626892260256441 9257267460470169195192331)
            ·
              refine ⟨13885901190705253792788497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9257267460470169195192331 13885901190705253792788497)
              ·
                refine ⟨10414425893028940344591373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13885901190705253792788497 10414425893028940344591373)
                ·
                  refine ⟨3905409709885852629221765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10414425893028940344591373 3905409709885852629221765)
                  ·
                    refine ⟨732264320603597367979081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3905409709885852629221765 732264320603597367979081)
                    ·
                      rfl

theorem cell23_4278239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 4].length) (baseStart_4278239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278239 prefixEnd_4278239 := by exact prefixLift 4278239
  have htrace : WordTrace (prefixWord ++ tailWord_4278239) baseStart_4278239 baseEnd_4278239 := by
    simpa [prefixWord, tailWord_4278239, baseEnd_4278239] using wordTrace_append hprefix tailTrace_4278239
  have hstable : (prefixWord ++ tailWord_4278239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278239).length < 2 ^ (prefixWord ++ tailWord_4278239).sum := by decide
  have hdescent : baseEnd_4278239 < baseStart_4278239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278306 : List Nat := [3, 3, 1, 1, 1, 2, 2, 3, 2, 3, 2]
def baseStart_4278306 : Nat := 118140960795 + 4278306 * 2 ^ 59
def prefixEnd_4278306 : Nat := 4983230072969 + 3 ^ 40 * 4278306 * 2
def baseEnd_4278306 : Nat := 2196827365014643341799435

theorem tailTrace_4278306 : CollatzResearch.WordTrace tailWord_4278306 prefixEnd_4278306 2196827365014643341799435 := by
  unfold tailWord_4278306
  simp only [CollatzResearch.WordTrace]
  refine ⟨39010659809608878334445693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104028426158957008891855181 39010659809608878334445693)
  ·
    refine ⟨14628997428603329375417135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39010659809608878334445693 14628997428603329375417135)
    ·
      refine ⟨21943496142904994063125703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14628997428603329375417135 21943496142904994063125703)
      ·
        refine ⟨32915244214357491094688555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21943496142904994063125703 32915244214357491094688555)
        ·
          refine ⟨49372866321536236642032833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32915244214357491094688555 49372866321536236642032833)
          ·
            refine ⟨37029649741152177481524625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49372866321536236642032833 37029649741152177481524625)
            ·
              refine ⟨27772237305864133111143469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37029649741152177481524625 27772237305864133111143469)
              ·
                refine ⟨10414588989699049916678801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27772237305864133111143469 10414588989699049916678801)
                ·
                  refine ⟨7810941742274287437509101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10414588989699049916678801 7810941742274287437509101)
                  ·
                    refine ⟨2929103153352857789065913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7810941742274287437509101 2929103153352857789065913)
                    ·
                      refine ⟨2196827365014643341799435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2929103153352857789065913 2196827365014643341799435)
                      ·
                        rfl

theorem cell23_4278306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_4278306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278306 prefixEnd_4278306 := by exact prefixLift 4278306
  have htrace : WordTrace (prefixWord ++ tailWord_4278306) baseStart_4278306 baseEnd_4278306 := by
    simpa [prefixWord, tailWord_4278306, baseEnd_4278306] using wordTrace_append hprefix tailTrace_4278306
  have hstable : (prefixWord ++ tailWord_4278306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278306).length < 2 ^ (prefixWord ++ tailWord_4278306).sum := by decide
  have hdescent : baseEnd_4278306 < baseStart_4278306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278332 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_4278332 : Nat := 118140960795 + 4278332 * 2 ^ 59
def prefixEnd_4278332 : Nat := 4983230072969 + 3 ^ 40 * 4278332 * 2
def baseEnd_4278332 : Nat := 2196840715511660240074315

theorem tailTrace_4278332 : CollatzResearch.WordTrace tailWord_4278332 prefixEnd_4278332 2196840715511660240074315 := by
  unfold tailWord_4278332
  simp only [CollatzResearch.WordTrace]
  refine ⟨78021793768170659889114625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104029058357560879852152833 78021793768170659889114625)
  ·
    refine ⟨58516345326127994916835969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78021793768170659889114625 58516345326127994916835969)
    ·
      refine ⟨43887258994595996187626977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58516345326127994916835969 43887258994595996187626977)
      ·
        refine ⟨32915444245946997140720233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43887258994595996187626977 32915444245946997140720233)
        ·
          refine ⟨24686583184460247855540175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32915444245946997140720233 24686583184460247855540175)
          ·
            refine ⟨37029874776690371783310263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24686583184460247855540175 37029874776690371783310263)
            ·
              refine ⟨55544812165035557674965395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37029874776690371783310263 55544812165035557674965395)
              ·
                refine ⟨83317218247553336512448093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55544812165035557674965395 83317218247553336512448093)
                ·
                  refine ⟨31243956842832501192168035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83317218247553336512448093 31243956842832501192168035)
                  ·
                    refine ⟨46865935264248751788252053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31243956842832501192168035 46865935264248751788252053)
                    ·
                      refine ⟨2196840715511660240074315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46865935264248751788252053 2196840715511660240074315)
                      ·
                        rfl

theorem cell23_4278332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_4278332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278332 prefixEnd_4278332 := by exact prefixLift 4278332
  have htrace : WordTrace (prefixWord ++ tailWord_4278332) baseStart_4278332 baseEnd_4278332 := by
    simpa [prefixWord, tailWord_4278332, baseEnd_4278332] using wordTrace_append hprefix tailTrace_4278332
  have hstable : (prefixWord ++ tailWord_4278332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278332).length < 2 ^ (prefixWord ++ tailWord_4278332).sum := by decide
  have hdescent : baseEnd_4278332 < baseStart_4278332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278349 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_4278349 : Nat := 118140960795 + 4278349 * 2 ^ 59
def prefixEnd_4278349 : Nat := 4983230072969 + 3 ^ 40 * 4278349 * 2
def baseEnd_4278349 : Nat := 2196849444682786673561737

theorem tailTrace_4278349 : CollatzResearch.WordTrace tailWord_4278349 prefixEnd_4278349 2196849444682786673561737 := by
  unfold tailWord_4278349
  simp only [CollatzResearch.WordTrace]
  refine ⟨156044207577279731681598101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104029471718186487787732067 156044207577279731681598101)
  ·
    refine ⟨7314572230184987422574911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 156044207577279731681598101 7314572230184987422574911)
    ·
      refine ⟨10971858345277481133862367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7314572230184987422574911 10971858345277481133862367)
      ·
        refine ⟨16457787517916221700793551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10971858345277481133862367 16457787517916221700793551)
        ·
          refine ⟨24686681276874332551190327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16457787517916221700793551 24686681276874332551190327)
          ·
            refine ⟨37030021915311498826785491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24686681276874332551190327 37030021915311498826785491)
            ·
              refine ⟨55545032872967248240178237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37030021915311498826785491 55545032872967248240178237)
              ·
                refine ⟨20829387327362718090066839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55545032872967248240178237 20829387327362718090066839)
                ·
                  refine ⟨31244080991044077135100259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20829387327362718090066839 31244080991044077135100259)
                  ·
                    refine ⟨46866121486566115702650389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31244080991044077135100259 46866121486566115702650389)
                    ·
                      refine ⟨2196849444682786673561737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46866121486566115702650389 2196849444682786673561737)
                      ·
                        rfl

theorem cell23_4278349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_4278349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278349 prefixEnd_4278349 := by exact prefixLift 4278349
  have htrace : WordTrace (prefixWord ++ tailWord_4278349) baseStart_4278349 baseEnd_4278349 := by
    simpa [prefixWord, tailWord_4278349, baseEnd_4278349] using wordTrace_append hprefix tailTrace_4278349
  have hstable : (prefixWord ++ tailWord_4278349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278349).length < 2 ^ (prefixWord ++ tailWord_4278349).sum := by decide
  have hdescent : baseEnd_4278349 < baseStart_4278349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278370 : List Nat := [3, 3, 2, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_4278370 : Nat := 118140960795 + 4278370 * 2 ^ 59
def prefixEnd_4278370 : Nat := 4983230072969 + 3 ^ 40 * 4278370 * 2
def baseEnd_4278370 : Nat := 2196860227776531091399141

theorem tailTrace_4278370 : CollatzResearch.WordTrace tailWord_4278370 prefixEnd_4278370 2196860227776531091399141 := by
  unfold tailWord_4278370
  simp only [CollatzResearch.WordTrace]
  refine ⟨39011243377550913067028141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104029982340135768178741709 39011243377550913067028141)
  ·
    refine ⟨14629216266581592400135553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39011243377550913067028141 14629216266581592400135553)
    ·
      refine ⟨10971912199936194300101665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14629216266581592400135553 10971912199936194300101665)
      ·
        refine ⟨8228934149952145725076249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10971912199936194300101665 8228934149952145725076249)
        ·
          refine ⟨6171700612464109293807187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8228934149952145725076249 6171700612464109293807187)
          ·
            refine ⟨9257550918696163940710781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6171700612464109293807187 9257550918696163940710781)
            ·
              refine ⟨3471581594511061477766543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9257550918696163940710781 3471581594511061477766543)
              ·
                refine ⟨5207372391766592216649815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3471581594511061477766543 5207372391766592216649815)
                ·
                  refine ⟨7811058587649888324974723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5207372391766592216649815 7811058587649888324974723)
                  ·
                    refine ⟨11716587881474832487462085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7811058587649888324974723 11716587881474832487462085)
                    ·
                      refine ⟨2196860227776531091399141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11716587881474832487462085 2196860227776531091399141)
                      ·
                        rfl

theorem cell23_4278370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_4278370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278370 prefixEnd_4278370 := by exact prefixLift 4278370
  have htrace : WordTrace (prefixWord ++ tailWord_4278370) baseStart_4278370 baseEnd_4278370 := by
    simpa [prefixWord, tailWord_4278370, baseEnd_4278370] using wordTrace_append hprefix tailTrace_4278370
  have hstable : (prefixWord ++ tailWord_4278370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278370).length < 2 ^ (prefixWord ++ tailWord_4278370).sum := by decide
  have hdescent : baseEnd_4278370 < baseStart_4278370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278373 : List Nat := [1, 3, 1, 3, 2, 3, 3, 1, 1, 2, 3]
def baseStart_4278373 : Nat := 118140960795 + 4278373 * 2 ^ 59
def prefixEnd_4278373 : Nat := 4983230072969 + 3 ^ 40 * 4278373 * 2
def baseEnd_4278373 : Nat := 2196861768218494579661627

theorem tailTrace_4278373 : CollatzResearch.WordTrace tailWord_4278373 prefixEnd_4278373 2196861768218494579661627 := by
  unfold tailWord_4278373
  simp only [CollatzResearch.WordTrace]
  refine ⟨156045082929192783780471773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104030055286128522520314515 156045082929192783780471773)
  ·
    refine ⟨58516906098447293917676915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156045082929192783780471773 58516906098447293917676915)
    ·
      refine ⟨87775359147670940876515373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58516906098447293917676915 87775359147670940876515373)
      ·
        refine ⟨32915759680376602828693265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87775359147670940876515373 32915759680376602828693265)
        ·
          refine ⟨24686819760282452121519949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32915759680376602828693265 24686819760282452121519949)
          ·
            refine ⟨9257557410105919545569981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24686819760282452121519949 9257557410105919545569981)
            ·
              refine ⟨3471584028789719829588743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9257557410105919545569981 3471584028789719829588743)
              ·
                refine ⟨5207376043184579744383115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3471584028789719829588743 5207376043184579744383115)
                ·
                  refine ⟨7811064064776869616574673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5207376043184579744383115 7811064064776869616574673)
                  ·
                    refine ⟨5858298048582652212431005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7811064064776869616574673 5858298048582652212431005)
                    ·
                      refine ⟨2196861768218494579661627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5858298048582652212431005 2196861768218494579661627)
                      ·
                        rfl

theorem cell23_4278373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_4278373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278373 prefixEnd_4278373 := by exact prefixLift 4278373
  have htrace : WordTrace (prefixWord ++ tailWord_4278373) baseStart_4278373 baseEnd_4278373 := by
    simpa [prefixWord, tailWord_4278373, baseEnd_4278373] using wordTrace_append hprefix tailTrace_4278373
  have hstable : (prefixWord ++ tailWord_4278373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278373).length < 2 ^ (prefixWord ++ tailWord_4278373).sum := by decide
  have hdescent : baseEnd_4278373 < baseStart_4278373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278396 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 3, 3, 2]
def baseStart_4278396 : Nat := 118140960795 + 4278396 * 2 ^ 59
def prefixEnd_4278396 : Nat := 4983230072969 + 3 ^ 40 * 4278396 * 2
def baseEnd_4278396 : Nat := 2196873578273547989674021

theorem tailTrace_4278396 : CollatzResearch.WordTrace tailWord_4278396 prefixEnd_4278396 2196873578273547989674021 := by
  unfold tailWord_4278396
  simp only [CollatzResearch.WordTrace]
  refine ⟨78022960904054729354279521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104030614538739639139039361 78022960904054729354279521)
  ·
    refine ⟨58517220678041047015709641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78022960904054729354279521 58517220678041047015709641)
    ·
      refine ⟨43887915508530785261782231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58517220678041047015709641 43887915508530785261782231)
      ·
        refine ⟨65831873262796177892673347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43887915508530785261782231 65831873262796177892673347)
        ·
          refine ⟨98747809894194266839010021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65831873262796177892673347 98747809894194266839010021)
          ·
            refine ⟨18515214355161425032314379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98747809894194266839010021 18515214355161425032314379)
            ·
              refine ⟨27772821532742137548471569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18515214355161425032314379 27772821532742137548471569)
              ·
                refine ⟨20829616149556603161353677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27772821532742137548471569 20829616149556603161353677)
                ·
                  refine ⟨7811106056083726185507629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20829616149556603161353677 7811106056083726185507629)
                  ·
                    refine ⟨2929164771031397319565361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7811106056083726185507629 2929164771031397319565361)
                    ·
                      refine ⟨2196873578273547989674021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2929164771031397319565361 2196873578273547989674021)
                      ·
                        rfl

theorem cell23_4278396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_4278396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278396 prefixEnd_4278396 := by exact prefixLift 4278396
  have htrace : WordTrace (prefixWord ++ tailWord_4278396) baseStart_4278396 baseEnd_4278396 := by
    simpa [prefixWord, tailWord_4278396, baseEnd_4278396] using wordTrace_append hprefix tailTrace_4278396
  have hstable : (prefixWord ++ tailWord_4278396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278396).length < 2 ^ (prefixWord ++ tailWord_4278396).sum := by decide
  have hdescent : baseEnd_4278396 < baseStart_4278396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278459 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 3]
def baseStart_4278459 : Nat := 118140960795 + 4278459 * 2 ^ 59
def prefixEnd_4278459 : Nat := 4983230072969 + 3 ^ 40 * 4278459 * 2
def baseEnd_4278459 : Nat := 2196905927554781243186231

theorem tailTrace_4278459 : CollatzResearch.WordTrace tailWord_4278459 prefixEnd_4278459 2196905927554781243186231 := by
  unfold tailWord_4278459
  simp only [CollatzResearch.WordTrace]
  refine ⟨156048219606881220468102431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104032146404587480312068287 156048219606881220468102431)
  ·
    refine ⟨234072329410321830702153647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156048219606881220468102431 234072329410321830702153647)
    ·
      refine ⟨351108494115482746053230471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234072329410321830702153647 351108494115482746053230471)
      ·
        refine ⟨526662741173224119079845707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351108494115482746053230471 526662741173224119079845707)
        ·
          refine ⟨789994111759836178619768561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 526662741173224119079845707 789994111759836178619768561)
          ·
            refine ⟨592495583819877133964826421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 789994111759836178619768561 592495583819877133964826421)
            ·
              refine ⟨55546460983113481309202477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 592495583819877133964826421 55546460983113481309202477)
              ·
                refine ⟨20829922868667555490950929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55546460983113481309202477 20829922868667555490950929)
                ·
                  refine ⟨15622442151500666618213197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20829922868667555490950929 15622442151500666618213197)
                  ·
                    refine ⟨5858415806812749981829949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15622442151500666618213197 5858415806812749981829949)
                    ·
                      refine ⟨2196905927554781243186231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5858415806812749981829949 2196905927554781243186231)
                      ·
                        rfl

theorem cell23_4278459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 3].length) (baseStart_4278459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278459 prefixEnd_4278459 := by exact prefixLift 4278459
  have htrace : WordTrace (prefixWord ++ tailWord_4278459) baseStart_4278459 baseEnd_4278459 := by
    simpa [prefixWord, tailWord_4278459, baseEnd_4278459] using wordTrace_append hprefix tailTrace_4278459
  have hstable : (prefixWord ++ tailWord_4278459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278459).length < 2 ^ (prefixWord ++ tailWord_4278459).sum := by decide
  have hdescent : baseEnd_4278459 < baseStart_4278459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278460 : List Nat := [2, 2, 2, 3, 3, 2, 1, 1, 1, 4, 2]
def baseStart_4278460 : Nat := 118140960795 + 4278460 * 2 ^ 59
def prefixEnd_4278460 : Nat := 4983230072969 + 3 ^ 40 * 4278460 * 2
def baseEnd_4278460 : Nat := 2196906441035435739273727

theorem tailTrace_4278460 : CollatzResearch.WordTrace tailWord_4278460 prefixEnd_4278460 2196906441035435739273727 := by
  unfold tailWord_4278460
  simp only [CollatzResearch.WordTrace]
  refine ⟨78024128039938798819444417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104032170719918398425925889 78024128039938798819444417)
  ·
    refine ⟨58518096029954099114583313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78024128039938798819444417 58518096029954099114583313)
    ·
      refine ⟨43888572022465574335937485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58518096029954099114583313 43888572022465574335937485)
      ·
        refine ⟨16458214508424590375976557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43888572022465574335937485 16458214508424590375976557)
        ·
          refine ⟨6171830440659221390991209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16458214508424590375976557 6171830440659221390991209)
          ·
            refine ⟨4628872830494416043243407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6171830440659221390991209 4628872830494416043243407)
            ·
              refine ⟨6943309245741624064865111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4628872830494416043243407 6943309245741624064865111)
              ·
                refine ⟨10414963868612436097297667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6943309245741624064865111 10414963868612436097297667)
                ·
                  refine ⟨15622445802918654145946501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10414963868612436097297667 15622445802918654145946501)
                  ·
                    refine ⟨2929208588047247652364969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15622445802918654145946501 2929208588047247652364969)
                    ·
                      refine ⟨2196906441035435739273727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2929208588047247652364969 2196906441035435739273727)
                      ·
                        rfl

theorem cell23_4278460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_4278460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278460 prefixEnd_4278460 := by exact prefixLift 4278460
  have htrace : WordTrace (prefixWord ++ tailWord_4278460) baseStart_4278460 baseEnd_4278460 := by
    simpa [prefixWord, tailWord_4278460, baseEnd_4278460] using wordTrace_append hprefix tailTrace_4278460
  have hstable : (prefixWord ++ tailWord_4278460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278460).length < 2 ^ (prefixWord ++ tailWord_4278460).sum := by decide
  have hdescent : baseEnd_4278460 < baseStart_4278460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278479 : List Nat := [1, 1, 2, 1, 1, 3, 4, 3, 2, 5]
def baseStart_4278479 : Nat := 118140960795 + 4278479 * 2 ^ 59
def prefixEnd_4278479 : Nat := 4983230072969 + 3 ^ 40 * 4278479 * 2
def baseEnd_4278479 : Nat := 732305399055957054978713

theorem tailTrace_4278479 : CollatzResearch.WordTrace tailWord_4278479 prefixEnd_4278479 732305399055957054978713 := by
  unfold tailWord_4278479
  simp only [CollatzResearch.WordTrace]
  refine ⟨156048949066808763883830491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104032632711205842589220327 156048949066808763883830491)
  ·
    refine ⟨234073423600213145825745737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156048949066808763883830491 234073423600213145825745737)
    ·
      refine ⟨175555067700159859369309303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234073423600213145825745737 175555067700159859369309303)
      ·
        refine ⟨263332601550239789053963955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175555067700159859369309303 263332601550239789053963955)
        ·
          refine ⟨394998902325359683580945933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263332601550239789053963955 394998902325359683580945933)
          ·
            refine ⟨148124588372009881342854725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 394998902325359683580945933 148124588372009881342854725)
            ·
              refine ⟨27773360319751852751785261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148124588372009881342854725 27773360319751852751785261)
              ·
                refine ⟨10415010119906944781919473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27773360319751852751785261 10415010119906944781919473)
                ·
                  refine ⟨7811257589930208586439605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10415010119906944781919473 7811257589930208586439605)
                  ·
                    refine ⟨732305399055957054978713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7811257589930208586439605 732305399055957054978713)
                    ·
                      rfl

theorem cell23_4278479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 5].length) (baseStart_4278479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278479 prefixEnd_4278479 := by exact prefixLift 4278479
  have htrace : WordTrace (prefixWord ++ tailWord_4278479) baseStart_4278479 baseEnd_4278479 := by
    simpa [prefixWord, tailWord_4278479, baseEnd_4278479] using wordTrace_append hprefix tailTrace_4278479
  have hstable : (prefixWord ++ tailWord_4278479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278479).length < 2 ^ (prefixWord ++ tailWord_4278479).sum := by decide
  have hdescent : baseEnd_4278479 < baseStart_4278479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278560 : List Nat := [2, 1, 1, 5, 2, 2, 1, 4, 1, 4]
def baseStart_4278560 : Nat := 118140960795 + 4278560 * 2 ^ 59
def prefixEnd_4278560 : Nat := 4983230072969 + 3 ^ 40 * 4278560 * 2
def baseEnd_4278560 : Nat := 732319263033628449341089

theorem tailTrace_4278560 : CollatzResearch.WordTrace tailWord_4278560 prefixEnd_4278560 732319263033628449341089 := by
  unfold tailWord_4278560
  simp only [CollatzResearch.WordTrace]
  refine ⟨78025951689757657358764567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104034602253010209811686089 78025951689757657358764567)
  ·
    refine ⟨117038927534636486038146851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78025951689757657358764567 117038927534636486038146851)
    ·
      refine ⟨175558391301954729057220277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117038927534636486038146851 175558391301954729057220277)
      ·
        refine ⟨16458599184558255849114401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 175558391301954729057220277 16458599184558255849114401)
        ·
          refine ⟨12343949388418691886835801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16458599184558255849114401 12343949388418691886835801)
          ·
            refine ⟨9257962041314018915126851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12343949388418691886835801 9257962041314018915126851)
            ·
              refine ⟨13886943061971028372690277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9257962041314018915126851 13886943061971028372690277)
              ·
                refine ⟨2603801824119567819879427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13886943061971028372690277 2603801824119567819879427)
                ·
                  refine ⟨3905702736179351729819141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2603801824119567819879427 3905702736179351729819141)
                  ·
                    refine ⟨732319263033628449341089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3905702736179351729819141 732319263033628449341089)
                    ·
                      rfl

theorem cell23_4278560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 1, 4].length) (baseStart_4278560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278560 prefixEnd_4278560 := by exact prefixLift 4278560
  have htrace : WordTrace (prefixWord ++ tailWord_4278560) baseStart_4278560 baseEnd_4278560 := by
    simpa [prefixWord, tailWord_4278560, baseEnd_4278560] using wordTrace_append hprefix tailTrace_4278560
  have hstable : (prefixWord ++ tailWord_4278560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278560).length < 2 ^ (prefixWord ++ tailWord_4278560).sum := by decide
  have hdescent : baseEnd_4278560 < baseStart_4278560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278579 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 7]
def baseStart_4278579 : Nat := 118140960795 + 4278579 * 2 ^ 59
def prefixEnd_4278579 : Nat := 4983230072969 + 3 ^ 40 * 4278579 * 2
def baseEnd_4278579 : Nat := 2196967545233320773685679

theorem tailTrace_4278579 : CollatzResearch.WordTrace tailWord_4278579 prefixEnd_4278579 2196967545233320773685679 := by
  unfold tailWord_4278579
  simp only [CollatzResearch.WordTrace]
  refine ⟨156052596366446480962470791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104035064244297653974980527 156052596366446480962470791)
  ·
    refine ⟨234078894549669721443706187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156052596366446480962470791 234078894549669721443706187)
    ·
      refine ⟨351118341824504582165559281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234078894549669721443706187 351118341824504582165559281)
      ·
        refine ⟨263338756368378436624169461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351118341824504582165559281 263338756368378436624169461)
        ·
          refine ⟨24688008409535478433515887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 263338756368378436624169461 24688008409535478433515887)
          ·
            refine ⟨37032012614303217650273831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24688008409535478433515887 37032012614303217650273831)
            ·
              refine ⟨55548018921454826475410747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37032012614303217650273831 55548018921454826475410747)
              ·
                refine ⟨83322028382182239713116121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55548018921454826475410747 83322028382182239713116121)
                ·
                  refine ⟨62491521286636679784837091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83322028382182239713116121 62491521286636679784837091)
                  ·
                    refine ⟨93737281929955019677255637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62491521286636679784837091 93737281929955019677255637)
                    ·
                      refine ⟨2196967545233320773685679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93737281929955019677255637 2196967545233320773685679)
                      ·
                        rfl

theorem cell23_4278579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_4278579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278579 prefixEnd_4278579 := by exact prefixLift 4278579
  have htrace : WordTrace (prefixWord ++ tailWord_4278579) baseStart_4278579 baseEnd_4278579 := by
    simpa [prefixWord, tailWord_4278579, baseEnd_4278579] using wordTrace_append hprefix tailTrace_4278579
  have hstable : (prefixWord ++ tailWord_4278579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278579).length < 2 ^ (prefixWord ++ tailWord_4278579).sum := by decide
  have hdescent : baseEnd_4278579 < baseStart_4278579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278586 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 3, 5]
def baseStart_4278586 : Nat := 118140960795 + 4278586 * 2 ^ 59
def prefixEnd_4278586 : Nat := 4983230072969 + 3 ^ 40 * 4278586 * 2
def baseEnd_4278586 : Nat := 732323713199300748766049

theorem tailTrace_4278586 : CollatzResearch.WordTrace tailWord_4278586 prefixEnd_4278586 732323713199300748766049 := by
  unfold tailWord_4278586
  simp only [CollatzResearch.WordTrace]
  refine ⟨39013212919355280289493903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104035234451614080771983741 39013212919355280289493903)
  ·
    refine ⟨58519819379032920434240855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39013212919355280289493903 58519819379032920434240855)
    ·
      refine ⟨87779729068549380651361283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58519819379032920434240855 87779729068549380651361283)
      ·
        refine ⟨131669593602824070977041925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87779729068549380651361283 131669593602824070977041925)
        ·
          refine ⟨24688048800529513308195361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131669593602824070977041925 24688048800529513308195361)
          ·
            refine ⟨18516036600397134981146521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24688048800529513308195361 18516036600397134981146521)
            ·
              refine ⟨13887027450297851235859891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18516036600397134981146521 13887027450297851235859891)
              ·
                refine ⟨20830541175446776853789837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13887027450297851235859891 20830541175446776853789837)
                ·
                  refine ⟨7811452940792541320171189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20830541175446776853789837 7811452940792541320171189)
                  ·
                    refine ⟨732323713199300748766049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7811452940792541320171189 732323713199300748766049)
                    ·
                      rfl

theorem cell23_4278586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_4278586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278586 prefixEnd_4278586 := by exact prefixLift 4278586
  have htrace : WordTrace (prefixWord ++ tailWord_4278586) baseStart_4278586 baseEnd_4278586 := by
    simpa [prefixWord, tailWord_4278586, baseEnd_4278586] using wordTrace_append hprefix tailTrace_4278586
  have hstable : (prefixWord ++ tailWord_4278586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278586).length < 2 ^ (prefixWord ++ tailWord_4278586).sum := by decide
  have hdescent : baseEnd_4278586 < baseStart_4278586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278600 : List Nat := [2, 1, 3, 1, 1, 2, 3, 5, 1, 1, 3]
def baseStart_4278600 : Nat := 118140960795 + 4278600 * 2 ^ 59
def prefixEnd_4278600 : Nat := 4983230072969 + 3 ^ 40 * 4278600 * 2
def baseEnd_4278600 : Nat := 2196978328327065191523083

theorem tailTrace_4278600 : CollatzResearch.WordTrace tailWord_4278600 prefixEnd_4278600 2196978328327065191523083 := by
  unfold tailWord_4278600
  simp only [CollatzResearch.WordTrace]
  refine ⟨78026681149685200774492627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104035574866246934365990169 78026681149685200774492627)
  ·
    refine ⟨117040021724527801161738941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78026681149685200774492627 117040021724527801161738941)
    ·
      refine ⟨43890008146697925435652103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117040021724527801161738941 43890008146697925435652103)
      ·
        refine ⟨65835012220046888153478155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43890008146697925435652103 65835012220046888153478155)
        ·
          refine ⟨98752518330070332230217233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65835012220046888153478155 98752518330070332230217233)
          ·
            refine ⟨74064388747552749172662925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98752518330070332230217233 74064388747552749172662925)
            ·
              refine ⟨27774145780332280939748597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74064388747552749172662925 27774145780332280939748597)
              ·
                refine ⟨2603826166906151338101431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27774145780332280939748597 2603826166906151338101431)
                ·
                  refine ⟨3905739250359227007152147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2603826166906151338101431 3905739250359227007152147)
                  ·
                    refine ⟨5858608875538840510728221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3905739250359227007152147 5858608875538840510728221)
                    ·
                      refine ⟨2196978328327065191523083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5858608875538840510728221 2196978328327065191523083)
                      ·
                        rfl

theorem cell23_4278600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 1, 1, 3].length) (baseStart_4278600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278600 prefixEnd_4278600 := by exact prefixLift 4278600
  have htrace : WordTrace (prefixWord ++ tailWord_4278600) baseStart_4278600 baseEnd_4278600 := by
    simpa [prefixWord, tailWord_4278600, baseEnd_4278600] using wordTrace_append hprefix tailTrace_4278600
  have hstable : (prefixWord ++ tailWord_4278600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278600).length < 2 ^ (prefixWord ++ tailWord_4278600).sum := by decide
  have hdescent : baseEnd_4278600 < baseStart_4278600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278606 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4]
def baseStart_4278606 : Nat := 118140960795 + 4278606 * 2 ^ 59
def prefixEnd_4278606 : Nat := 4983230072969 + 3 ^ 40 * 4278606 * 2
def baseEnd_4278606 : Nat := 2196981409210992168048055

theorem tailTrace_4278606 : CollatzResearch.WordTrace tailWord_4278606 prefixEnd_4278606 2196981409210992168048055 := by
  unfold tailWord_4278606
  simp only [CollatzResearch.WordTrace]
  refine ⟨19506697642168583071712959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104035720758232443049135781 19506697642168583071712959)
  ·
    refine ⟨29260046463252874607569439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19506697642168583071712959 29260046463252874607569439)
    ·
      refine ⟨43890069694879311911354159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29260046463252874607569439 43890069694879311911354159)
      ·
        refine ⟨65835104542318967867031239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43890069694879311911354159 65835104542318967867031239)
        ·
          refine ⟨98752656813478451800546859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65835104542318967867031239 98752656813478451800546859)
          ·
            refine ⟨148128985220217677700820289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98752656813478451800546859 148128985220217677700820289)
            ·
              refine ⟨111096738915163258275615217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148128985220217677700820289 111096738915163258275615217)
              ·
                refine ⟨83322554186372443706711413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111096738915163258275615217 83322554186372443706711413)
                ·
                  refine ⟨7811489454972416597504195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83322554186372443706711413 7811489454972416597504195)
                  ·
                    refine ⟨11717234182458624896256293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7811489454972416597504195 11717234182458624896256293)
                    ·
                      refine ⟨2196981409210992168048055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11717234182458624896256293 2196981409210992168048055)
                      ·
                        rfl

theorem cell23_4278606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_4278606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278606 prefixEnd_4278606 := by exact prefixLift 4278606
  have htrace : WordTrace (prefixWord ++ tailWord_4278606) baseStart_4278606 baseEnd_4278606 := by
    simpa [prefixWord, tailWord_4278606, baseEnd_4278606] using wordTrace_append hprefix tailTrace_4278606
  have hstable : (prefixWord ++ tailWord_4278606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278606).length < 2 ^ (prefixWord ++ tailWord_4278606).sum := by decide
  have hdescent : baseEnd_4278606 < baseStart_4278606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278640 : List Nat := [2, 1, 1, 1, 4, 3, 2, 2, 3, 2, 2]
def baseStart_4278640 : Nat := 118140960795 + 4278640 * 2 ^ 59
def prefixEnd_4278640 : Nat := 4983230072969 + 3 ^ 40 * 4278640 * 2
def baseEnd_4278640 : Nat := 2196998867553245035022899

theorem tailTrace_4278640 : CollatzResearch.WordTrace tailWord_4278640 prefixEnd_4278640 2196998867553245035022899 := by
  unfold tailWord_4278640
  simp only [CollatzResearch.WordTrace]
  refine ⟨78027410609612744190220687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104036547479483658920294249 78027410609612744190220687)
  ·
    refine ⟨117041115914419116285331031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78027410609612744190220687 117041115914419116285331031)
    ·
      refine ⟨175561673871628674427996547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117041115914419116285331031 175561673871628674427996547)
      ·
        refine ⟨263342510807443011641994821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175561673871628674427996547 263342510807443011641994821)
        ·
          refine ⟨49376720776395564682874029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 263342510807443011641994821 49376720776395564682874029)
          ·
            refine ⟨18516270291148336756077761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49376720776395564682874029 18516270291148336756077761)
            ·
              refine ⟨13887202718361252567058321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18516270291148336756077761 13887202718361252567058321)
              ·
                refine ⟨10415402038770939425293741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13887202718361252567058321 10415402038770939425293741)
                ·
                  refine ⟨3905775764539102284485153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10415402038770939425293741 3905775764539102284485153)
                  ·
                    refine ⟨2929331823404326713363865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3905775764539102284485153 2929331823404326713363865)
                    ·
                      refine ⟨2196998867553245035022899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2929331823404326713363865 2196998867553245035022899)
                      ·
                        rfl

theorem cell23_4278640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 3, 2, 2].length) (baseStart_4278640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278640 prefixEnd_4278640 := by exact prefixLift 4278640
  have htrace : WordTrace (prefixWord ++ tailWord_4278640) baseStart_4278640 baseEnd_4278640 := by
    simpa [prefixWord, tailWord_4278640, baseEnd_4278640] using wordTrace_append hprefix tailTrace_4278640
  have hstable : (prefixWord ++ tailWord_4278640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278640).length < 2 ^ (prefixWord ++ tailWord_4278640).sum := by decide
  have hdescent : baseEnd_4278640 < baseStart_4278640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278724 : List Nat := [2, 3, 3, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_4278724 : Nat := 118140960795 + 4278724 * 2 ^ 59
def prefixEnd_4278724 : Nat := 4983230072969 + 3 ^ 40 * 4278724 * 2
def baseEnd_4278724 : Nat := 2197041999928222706372513

theorem tailTrace_4278724 : CollatzResearch.WordTrace tailWord_4278724 prefixEnd_4278724 2197041999928222706372513 := by
  unfold tailWord_4278724
  simp only [CollatzResearch.WordTrace]
  refine ⟨78028942475460585363249613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104038589967280780484332817 78028942475460585363249613)
  ·
    refine ⟨29260853428297719511218605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78028942475460585363249613 29260853428297719511218605)
    ·
      refine ⟨10972820035611644816706977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29260853428297719511218605 10972820035611644816706977)
      ·
        refine ⟨8229615026708733612530233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10972820035611644816706977 8229615026708733612530233)
        ·
          refine ⟨6172211270031550209397675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8229615026708733612530233 6172211270031550209397675)
          ·
            refine ⟨9258316905047325314096513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6172211270031550209397675 9258316905047325314096513)
            ·
              refine ⟨6943737678785493985572385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9258316905047325314096513 6943737678785493985572385)
              ·
                refine ⟨5207803259089120489179289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6943737678785493985572385 5207803259089120489179289)
                ·
                  refine ⟨3905852444316840366884467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5207803259089120489179289 3905852444316840366884467)
                  ·
                    refine ⟨5858778666475260550326701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3905852444316840366884467 5858778666475260550326701)
                    ·
                      refine ⟨2197041999928222706372513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5858778666475260550326701 2197041999928222706372513)
                      ·
                        rfl

theorem cell23_4278724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_4278724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278724 prefixEnd_4278724 := by exact prefixLift 4278724
  have htrace : WordTrace (prefixWord ++ tailWord_4278724) baseStart_4278724 baseEnd_4278724 := by
    simpa [prefixWord, tailWord_4278724, baseEnd_4278724] using wordTrace_append hprefix tailTrace_4278724
  have hstable : (prefixWord ++ tailWord_4278724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278724).length < 2 ^ (prefixWord ++ tailWord_4278724).sum := by decide
  have hdescent : baseEnd_4278724 < baseStart_4278724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278840 : List Nat := [2, 1, 2, 1, 4, 1, 3, 2, 2, 2, 3]
def baseStart_4278840 : Nat := 118140960795 + 4278840 * 2 ^ 59
def prefixEnd_4278840 : Nat := 4983230072969 + 3 ^ 40 * 4278840 * 2
def baseEnd_4278840 : Nat := 2197101563684144252521979

theorem tailTrace_4278840 : CollatzResearch.WordTrace tailWord_4278840 prefixEnd_4278840 2197101563684144252521979 := by
  unfold tailWord_4278840
  simp only [CollatzResearch.WordTrace]
  refine ⟨78031057909250461268860987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104041410545667281691814649 78031057909250461268860987)
  ·
    refine ⟨117046586863875691903291481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78031057909250461268860987 117046586863875691903291481)
    ·
      refine ⟨87784940147906768927468611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117046586863875691903291481 87784940147906768927468611)
      ·
        refine ⟨131677410221860153391202917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87784940147906768927468611 131677410221860153391202917)
        ·
          refine ⟨24689514416598778760850547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131677410221860153391202917 24689514416598778760850547)
          ·
            refine ⟨37034271624898168141275821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24689514416598778760850547 37034271624898168141275821)
            ·
              refine ⟨13887851859336813052978433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37034271624898168141275821 13887851859336813052978433)
              ·
                refine ⟨10415888894502609789733825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13887851859336813052978433 10415888894502609789733825)
                ·
                  refine ⟨7811916670876957342300369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10415888894502609789733825 7811916670876957342300369)
                  ·
                    refine ⟨5858937503157718006725277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7811916670876957342300369 5858937503157718006725277)
                    ·
                      refine ⟨2197101563684144252521979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5858937503157718006725277 2197101563684144252521979)
                      ·
                        rfl

theorem cell23_4278840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_4278840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278840 prefixEnd_4278840 := by exact prefixLift 4278840
  have htrace : WordTrace (prefixWord ++ tailWord_4278840) baseStart_4278840 baseEnd_4278840 := by
    simpa [prefixWord, tailWord_4278840, baseEnd_4278840] using wordTrace_append hprefix tailTrace_4278840
  have hstable : (prefixWord ++ tailWord_4278840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278840).length < 2 ^ (prefixWord ++ tailWord_4278840).sum := by decide
  have hdescent : baseEnd_4278840 < baseStart_4278840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278880 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 1, 5, 2]
def baseStart_4278880 : Nat := 118140960795 + 4278880 * 2 ^ 59
def prefixEnd_4278880 : Nat := 4983230072969 + 3 ^ 40 * 4278880 * 2
def baseEnd_4278880 : Nat := 2197122102910324096021795

theorem tailTrace_4278880 : CollatzResearch.WordTrace tailWord_4278880 prefixEnd_4278880 2197122102910324096021795 := by
  unfold tailWord_4278880
  simp only [CollatzResearch.WordTrace]
  refine ⟨78031787369178004684589047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104042383158904006246118729 78031787369178004684589047)
  ·
    refine ⟨117047681053767007026883571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78031787369178004684589047 117047681053767007026883571)
    ·
      refine ⟨175571521580650510540325357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117047681053767007026883571 175571521580650510540325357)
      ·
        refine ⟨65839320592743941452622009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175571521580650510540325357 65839320592743941452622009)
        ·
          refine ⟨49379490444557956089466507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65839320592743941452622009 49379490444557956089466507)
          ·
            refine ⟨74069235666836934134199761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49379490444557956089466507 74069235666836934134199761)
            ·
              refine ⟨55551926750127700600649821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74069235666836934134199761 55551926750127700600649821)
              ·
                refine ⟨20831972531297887725243683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55551926750127700600649821 20831972531297887725243683)
                ·
                  refine ⟨31247958796946831587865525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20831972531297887725243683 31247958796946831587865525)
                  ·
                    refine ⟨2929496137213765461362393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31247958796946831587865525 2929496137213765461362393)
                    ·
                      refine ⟨2197122102910324096021795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2929496137213765461362393 2197122102910324096021795)
                      ·
                        rfl

theorem cell23_4278880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_4278880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278880 prefixEnd_4278880 := by exact prefixLift 4278880
  have htrace : WordTrace (prefixWord ++ tailWord_4278880) baseStart_4278880 baseEnd_4278880 := by
    simpa [prefixWord, tailWord_4278880, baseEnd_4278880] using wordTrace_append hprefix tailTrace_4278880
  have hstable : (prefixWord ++ tailWord_4278880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278880).length < 2 ^ (prefixWord ++ tailWord_4278880).sum := by decide
  have hdescent : baseEnd_4278880 < baseStart_4278880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278898 : List Nat := [3, 2, 1, 2, 5, 1, 2, 2, 1, 4]
def baseStart_4278898 : Nat := 118140960795 + 4278898 * 2 ^ 59
def prefixEnd_4278898 : Nat := 4983230072969 + 3 ^ 40 * 4278898 * 2
def baseEnd_4278898 : Nat := 732377115187368341865571

theorem tailTrace_4278898 : CollatzResearch.WordTrace tailWord_4278898 prefixEnd_4278898 732377115187368341865571 := by
  unfold tailWord_4278898
  simp only [CollatzResearch.WordTrace]
  refine ⟨39016057813072699610833337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104042820834860532295555565 39016057813072699610833337)
  ·
    refine ⟨29262043359804524708125003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39016057813072699610833337 29262043359804524708125003)
    ·
      refine ⟨43893065039706787062187505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29262043359804524708125003 43893065039706787062187505)
      ·
        refine ⟨32919798779780090296640629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43893065039706787062187505 32919798779780090296640629)
        ·
          refine ⟨3086231135604383465310059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32919798779780090296640629 3086231135604383465310059)
          ·
            refine ⟨4629346703406575197965089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3086231135604383465310059 4629346703406575197965089)
            ·
              refine ⟨3472010027554931398473817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4629346703406575197965089 3472010027554931398473817)
              ·
                refine ⟨2604007520666198548855363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3472010027554931398473817 2604007520666198548855363)
                ·
                  refine ⟨3906011280999297823283045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2604007520666198548855363 3906011280999297823283045)
                  ·
                    refine ⟨732377115187368341865571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3906011280999297823283045 732377115187368341865571)
                    ·
                      rfl

theorem cell23_4278898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_4278898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278898 prefixEnd_4278898 := by exact prefixLift 4278898
  have htrace : WordTrace (prefixWord ++ tailWord_4278898) baseStart_4278898 baseEnd_4278898 := by
    simpa [prefixWord, tailWord_4278898, baseEnd_4278898] using wordTrace_append hprefix tailTrace_4278898
  have hstable : (prefixWord ++ tailWord_4278898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278898).length < 2 ^ (prefixWord ++ tailWord_4278898).sum := by decide
  have hdescent : baseEnd_4278898 < baseStart_4278898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278927 : List Nat := [1, 1, 2, 1, 1, 1, 1, 8, 3, 2, 2]
def baseStart_4278927 : Nat := 118140960795 + 4278927 * 2 ^ 59
def prefixEnd_4278927 : Nat := 4983230072969 + 3 ^ 40 * 4278927 * 2
def baseEnd_4278927 : Nat := 2197146236501085412134079

theorem tailTrace_4278927 : CollatzResearch.WordTrace tailWord_4278927 prefixEnd_4278927 2197146236501085412134079 := by
  unfold tailWord_4278927
  simp only [CollatzResearch.WordTrace]
  refine ⟨156065288969185736396139035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104043525979457157597426023 156065288969185736396139035)
  ·
    refine ⟨234097933453778604594208553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156065288969185736396139035 234097933453778604594208553)
    ·
      refine ⟨175573450090333953445656415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234097933453778604594208553 175573450090333953445656415)
      ·
        refine ⟨263360175135500930168484623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175573450090333953445656415 263360175135500930168484623)
        ·
          refine ⟨395040262703251395252726935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263360175135500930168484623 395040262703251395252726935)
          ·
            refine ⟨592560394054877092879090403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395040262703251395252726935 592560394054877092879090403)
            ·
              refine ⟨888840591082315639318635605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592560394054877092879090403 888840591082315639318635605)
              ·
                refine ⟨10416100676745886398265261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 888840591082315639318635605 10416100676745886398265261)
                ·
                  refine ⟨3906037753779707399349473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10416100676745886398265261 3906037753779707399349473)
                  ·
                    refine ⟨2929528315334780549512105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3906037753779707399349473 2929528315334780549512105)
                    ·
                      refine ⟨2197146236501085412134079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2929528315334780549512105 2197146236501085412134079)
                      ·
                        rfl

theorem cell23_4278927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 2, 2].length) (baseStart_4278927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278927 prefixEnd_4278927 := by exact prefixLift 4278927
  have htrace : WordTrace (prefixWord ++ tailWord_4278927) baseStart_4278927 baseEnd_4278927 := by
    simpa [prefixWord, tailWord_4278927, baseEnd_4278927] using wordTrace_append hprefix tailTrace_4278927
  have hstable : (prefixWord ++ tailWord_4278927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278927).length < 2 ^ (prefixWord ++ tailWord_4278927).sum := by decide
  have hdescent : baseEnd_4278927 < baseStart_4278927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278938 : List Nat := [3, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3]
def baseStart_4278938 : Nat := 118140960795 + 4278938 * 2 ^ 59
def prefixEnd_4278938 : Nat := 4983230072969 + 3 ^ 40 * 4278938 * 2
def baseEnd_4278938 : Nat := 2197151884788284869096529

theorem tailTrace_4278938 : CollatzResearch.WordTrace tailWord_4278938 prefixEnd_4278938 2197151884788284869096529 := by
  unfold tailWord_4278938
  simp only [CollatzResearch.WordTrace]
  refine ⟨39016422543036471318697367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104043793448097256849859645 39016422543036471318697367)
  ·
    refine ⟨58524633814554706978046051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39016422543036471318697367 58524633814554706978046051)
    ·
      refine ⟨87786950721832060467069077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58524633814554706978046051 87786950721832060467069077)
      ·
        refine ⟨4115013315085877834393863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 87786950721832060467069077 4115013315085877834393863)
        ·
          refine ⟨6172519972628816751590795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4115013315085877834393863 6172519972628816751590795)
          ·
            refine ⟨9258779958943225127386193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6172519972628816751590795 9258779958943225127386193)
            ·
              refine ⟨6944084969207418845539645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9258779958943225127386193 6944084969207418845539645)
              ·
                refine ⟨2604031863452782067077367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6944084969207418845539645 2604031863452782067077367)
                ·
                  refine ⟨3906047795179173100616051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2604031863452782067077367 3906047795179173100616051)
                  ·
                    refine ⟨5859071692768759650924077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3906047795179173100616051 5859071692768759650924077)
                    ·
                      refine ⟨2197151884788284869096529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5859071692768759650924077 2197151884788284869096529)
                      ·
                        rfl

theorem cell23_4278938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_4278938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278938 prefixEnd_4278938 := by exact prefixLift 4278938
  have htrace : WordTrace (prefixWord ++ tailWord_4278938) baseStart_4278938 baseEnd_4278938 := by
    simpa [prefixWord, tailWord_4278938, baseEnd_4278938] using wordTrace_append hprefix tailTrace_4278938
  have hstable : (prefixWord ++ tailWord_4278938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278938).length < 2 ^ (prefixWord ++ tailWord_4278938).sum := by decide
  have hdescent : baseEnd_4278938 < baseStart_4278938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278983 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_4278983 : Nat := 118140960795 + 4278983 * 2 ^ 59
def prefixEnd_4278983 : Nat := 4983230072969 + 3 ^ 40 * 4278983 * 2
def baseEnd_4278983 : Nat := 2197174991417737193033821

theorem tailTrace_4278983 : CollatzResearch.WordTrace tailWord_4278983 prefixEnd_4278983 2197174991417737193033821 := by
  unfold tailWord_4278983
  simp only [CollatzResearch.WordTrace]
  refine ⟨156067331456982857960177603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104044887637988571973451735 156067331456982857960177603)
  ·
    refine ⟨234100997185474286940266405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156067331456982857960177603 234100997185474286940266405)
    ·
      refine ⟨43893936972276428801299951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 234100997185474286940266405 43893936972276428801299951)
      ·
        refine ⟨65840905458414643201949927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43893936972276428801299951 65840905458414643201949927)
        ·
          refine ⟨98761358187621964802924891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65840905458414643201949927 98761358187621964802924891)
          ·
            refine ⟨148142037281432947204387337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98761358187621964802924891 148142037281432947204387337)
            ·
              refine ⟨111106527961074710403290503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148142037281432947204387337 111106527961074710403290503)
              ·
                refine ⟨166659791941612065604935755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111106527961074710403290503 166659791941612065604935755)
                ·
                  refine ⟨249989687912418098407403633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166659791941612065604935755 249989687912418098407403633)
                  ·
                    refine ⟨187492265934313573805552725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 249989687912418098407403633 187492265934313573805552725)
                    ·
                      refine ⟨2197174991417737193033821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 187492265934313573805552725 2197174991417737193033821)
                      ·
                        rfl

theorem cell23_4278983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_4278983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278983 prefixEnd_4278983 := by exact prefixLift 4278983
  have htrace : WordTrace (prefixWord ++ tailWord_4278983) baseStart_4278983 baseEnd_4278983 := by
    simpa [prefixWord, tailWord_4278983, baseEnd_4278983] using wordTrace_append hprefix tailTrace_4278983
  have hstable : (prefixWord ++ tailWord_4278983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278983).length < 2 ^ (prefixWord ++ tailWord_4278983).sum := by decide
  have hdescent : baseEnd_4278983 < baseStart_4278983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4278990 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_4278990 : Nat := 118140960795 + 4278990 * 2 ^ 59
def prefixEnd_4278990 : Nat := 4983230072969 + 3 ^ 40 * 4278990 * 2
def baseEnd_4278990 : Nat := 2197178585782318665646289

theorem tailTrace_4278990 : CollatzResearch.WordTrace tailWord_4278990 prefixEnd_4278990 2197178585782318665646289 := by
  unfold tailWord_4278990
  simp only [CollatzResearch.WordTrace]
  refine ⟨19508448345994687269460303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104045057845304998770454949 19508448345994687269460303)
  ·
    refine ⟨29262672518992030904190455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19508448345994687269460303 29262672518992030904190455)
    ·
      refine ⟨43894008778488046356285683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29262672518992030904190455 43894008778488046356285683)
      ·
        refine ⟨65841013167732069534428525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43894008778488046356285683 65841013167732069534428525)
        ·
          refine ⟨24690379937899526075410697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65841013167732069534428525 24690379937899526075410697)
          ·
            refine ⟨18517784953424644556558023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24690379937899526075410697 18517784953424644556558023)
            ·
              refine ⟨27776677430136966834837035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18517784953424644556558023 27776677430136966834837035)
              ·
                refine ⟨41665016145205450252255553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27776677430136966834837035 41665016145205450252255553)
                ·
                  refine ⟨31248762108904087689191665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41665016145205450252255553 31248762108904087689191665)
                  ·
                    refine ⟨23436571581678065766893749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31248762108904087689191665 23436571581678065766893749)
                    ·
                      refine ⟨2197178585782318665646289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23436571581678065766893749 2197178585782318665646289)
                      ·
                        rfl

theorem cell23_4278990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_4278990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4278990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4278990 prefixEnd_4278990 := by exact prefixLift 4278990
  have htrace : WordTrace (prefixWord ++ tailWord_4278990) baseStart_4278990 baseEnd_4278990 := by
    simpa [prefixWord, tailWord_4278990, baseEnd_4278990] using wordTrace_append hprefix tailTrace_4278990
  have hstable : (prefixWord ++ tailWord_4278990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4278990).length < 2 ^ (prefixWord ++ tailWord_4278990).sum := by decide
  have hdescent : baseEnd_4278990 < baseStart_4278990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4278990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279020 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 3]
def baseStart_4279020 : Nat := 118140960795 + 4279020 * 2 ^ 59
def prefixEnd_4279020 : Nat := 4983230072969 + 3 ^ 40 * 4279020 * 2
def baseEnd_4279020 : Nat := 2197193990201953548271151

theorem tailTrace_4279020 : CollatzResearch.WordTrace tailWord_4279020 prefixEnd_4279020 2197193990201953548271151 := by
  unfold tailWord_4279020
  simp only [CollatzResearch.WordTrace]
  refine ⟨78034340478924406639637257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104045787305232542186183009 78034340478924406639637257)
  ·
    refine ⟨58525755359193304979727943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78034340478924406639637257 58525755359193304979727943)
    ·
      refine ⟨87788633038789957469591915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58525755359193304979727943 87788633038789957469591915)
      ·
        refine ⟨131682949558184936204387873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87788633038789957469591915 131682949558184936204387873)
        ·
          refine ⟨98762212168638702153290905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131682949558184936204387873 98762212168638702153290905)
          ·
            refine ⟨74071659126479026614968179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98762212168638702153290905 74071659126479026614968179)
            ·
              refine ⟨111107488689718539922452269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74071659126479026614968179 111107488689718539922452269)
              ·
                refine ⟨41665308258644452470919601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111107488689718539922452269 41665308258644452470919601)
                ·
                  refine ⟨31248981193983339353189701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41665308258644452470919601 31248981193983339353189701)
                  ·
                    refine ⟨5859183973871876128723069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31248981193983339353189701 5859183973871876128723069)
                    ·
                      refine ⟨2197193990201953548271151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5859183973871876128723069 2197193990201953548271151)
                      ·
                        rfl

theorem cell23_4279020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_4279020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279020 prefixEnd_4279020 := by exact prefixLift 4279020
  have htrace : WordTrace (prefixWord ++ tailWord_4279020) baseStart_4279020 baseEnd_4279020 := by
    simpa [prefixWord, tailWord_4279020, baseEnd_4279020] using wordTrace_append hprefix tailTrace_4279020
  have hstable : (prefixWord ++ tailWord_4279020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279020).length < 2 ^ (prefixWord ++ tailWord_4279020).sum := by decide
  have hdescent : baseEnd_4279020 < baseStart_4279020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279038 : List Nat := [4, 2, 2, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_4279038 : Nat := 118140960795 + 4279038 * 2 ^ 59
def prefixEnd_4279038 : Nat := 4983230072969 + 3 ^ 40 * 4279038 * 2
def baseEnd_4279038 : Nat := 2197203232853734477846069

theorem tailTrace_4279038 : CollatzResearch.WordTrace tailWord_4279038 prefixEnd_4279038 2197203232853734477846069 := by
  unfold tailWord_4279038
  simp only [CollatzResearch.WordTrace]
  refine ⟨19508667183972950294178721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104046224981189068235619845 19508667183972950294178721)
  ·
    refine ⟨14631500387979712720634041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19508667183972950294178721 14631500387979712720634041)
    ·
      refine ⟨10973625290984784540475531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14631500387979712720634041 10973625290984784540475531)
      ·
        refine ⟨16460437936477176810713297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10973625290984784540475531 16460437936477176810713297)
        ·
          refine ⟨12345328452357882608034973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16460437936477176810713297 12345328452357882608034973)
          ·
            refine ⟨4629498169634205978013115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12345328452357882608034973 4629498169634205978013115)
            ·
              refine ⟨6944247254451308967019673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4629498169634205978013115 6944247254451308967019673)
              ·
                refine ⟨5208185440838481725264755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6944247254451308967019673 5208185440838481725264755)
                ·
                  refine ⟨7812278161257722587897133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5208185440838481725264755 7812278161257722587897133)
                  ·
                    refine ⟨2929604310471645970461425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7812278161257722587897133 2929604310471645970461425)
                    ·
                      refine ⟨2197203232853734477846069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2929604310471645970461425 2197203232853734477846069)
                      ·
                        rfl

theorem cell23_4279038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_4279038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279038 prefixEnd_4279038 := by exact prefixLift 4279038
  have htrace : WordTrace (prefixWord ++ tailWord_4279038) baseStart_4279038 baseEnd_4279038 := by
    simpa [prefixWord, tailWord_4279038, baseEnd_4279038] using wordTrace_append hprefix tailTrace_4279038
  have hstable : (prefixWord ++ tailWord_4279038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279038).length < 2 ^ (prefixWord ++ tailWord_4279038).sum := by decide
  have hdescent : baseEnd_4279038 < baseStart_4279038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279074 : List Nat := [3, 3, 1, 1, 2, 3, 1, 4, 5]
def baseStart_4279074 : Nat := 118140960795 + 4279074 * 2 ^ 59
def prefixEnd_4279074 : Nat := 4983230072969 + 3 ^ 40 * 4279074 * 2
def baseEnd_4279074 : Nat := 244135746461921815221767

theorem tailTrace_4279074 : CollatzResearch.WordTrace tailWord_4279074 prefixEnd_4279074 244135746461921815221767 := by
  unfold tailWord_4279074
  simp only [CollatzResearch.WordTrace]
  refine ⟨39017662624913295125435069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104047100333102120334493517 39017662624913295125435069)
  ·
    refine ⟨14631623484342485672038151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39017662624913295125435069 14631623484342485672038151)
    ·
      refine ⟨21947435226513728508057227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14631623484342485672038151 21947435226513728508057227)
      ·
        refine ⟨32921152839770592762085841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21947435226513728508057227 32921152839770592762085841)
        ·
          refine ⟨24690864629827944571564381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32921152839770592762085841 24690864629827944571564381)
          ·
            refine ⟨9259074236185479214336643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24690864629827944571564381 9259074236185479214336643)
            ·
              refine ⟨13888611354278218821504965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9259074236185479214336643 13888611354278218821504965)
              ·
                refine ⟨2604114628927166029032181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13888611354278218821504965 2604114628927166029032181)
                ·
                  refine ⟨244135746461921815221767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2604114628927166029032181 244135746461921815221767)
                  ·
                    rfl

theorem cell23_4279074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_4279074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279074 prefixEnd_4279074 := by exact prefixLift 4279074
  have htrace : WordTrace (prefixWord ++ tailWord_4279074) baseStart_4279074 baseEnd_4279074 := by
    simpa [prefixWord, tailWord_4279074, baseEnd_4279074] using wordTrace_append hprefix tailTrace_4279074
  have hstable : (prefixWord ++ tailWord_4279074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279074).length < 2 ^ (prefixWord ++ tailWord_4279074).sum := by decide
  have hdescent : baseEnd_4279074 < baseStart_4279074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279077 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 1, 7, 2]
def baseStart_4279077 : Nat := 118140960795 + 4279077 * 2 ^ 59
def prefixEnd_4279077 : Nat := 4983230072969 + 3 ^ 40 * 4279077 * 2
def baseEnd_4279077 : Nat := 2197223258599259825258389

theorem tailTrace_4279077 : CollatzResearch.WordTrace tailWord_4279077 prefixEnd_4279077 2197223258599259825258389 := by
  unfold tailWord_4279077
  simp only [CollatzResearch.WordTrace]
  refine ⟨156070759918642312014099485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104047173279094874676066323 156070759918642312014099485)
  ·
    refine ⟨58526534969490867005287307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156070759918642312014099485 58526534969490867005287307)
    ·
      refine ⟨87789802454236300507930961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58526534969490867005287307 87789802454236300507930961)
      ·
        refine ⟨65842351840677225380948221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87789802454236300507930961 65842351840677225380948221)
        ·
          refine ⟨24690881940253959517855583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65842351840677225380948221 24690881940253959517855583)
          ·
            refine ⟨37036322910380939276783375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24690881940253959517855583 37036322910380939276783375)
            ·
              refine ⟨55554484365571408915175063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37036322910380939276783375 55554484365571408915175063)
              ·
                refine ⟨83331726548357113372762595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55554484365571408915175063 83331726548357113372762595)
                ·
                  refine ⟨124997589822535670059143893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83331726548357113372762595 124997589822535670059143893)
                  ·
                    refine ⟨2929631011465679767011185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 124997589822535670059143893 2929631011465679767011185)
                    ·
                      refine ⟨2197223258599259825258389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2929631011465679767011185 2197223258599259825258389)
                      ·
                        rfl

theorem cell23_4279077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_4279077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279077 prefixEnd_4279077 := by exact prefixLift 4279077
  have htrace : WordTrace (prefixWord ++ tailWord_4279077) baseStart_4279077 baseEnd_4279077 := by
    simpa [prefixWord, tailWord_4279077, baseEnd_4279077] using wordTrace_append hprefix tailTrace_4279077
  have hstable : (prefixWord ++ tailWord_4279077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279077).length < 2 ^ (prefixWord ++ tailWord_4279077).sum := by decide
  have hdescent : baseEnd_4279077 < baseStart_4279077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279107 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 1, 6, 2]
def baseStart_4279107 : Nat := 118140960795 + 4279107 * 2 ^ 59
def prefixEnd_4279107 : Nat := 4983230072969 + 3 ^ 40 * 4279107 * 2
def baseEnd_4279107 : Nat := 2197238663018894707883251

theorem tailTrace_4279107 : CollatzResearch.WordTrace tailWord_4279107 prefixEnd_4279107 2197238663018894707883251 := by
  unfold tailWord_4279107
  simp only [CollatzResearch.WordTrace]
  refine ⟨156071854108533627137691575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104047902739022418091794383 156071854108533627137691575)
  ·
    refine ⟨234107781162800440706537363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156071854108533627137691575 234107781162800440706537363)
    ·
      refine ⟨351161671744200661059806045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234107781162800440706537363 351161671744200661059806045)
      ·
        refine ⟨131685626904075247897427267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 351161671744200661059806045 131685626904075247897427267)
        ·
          refine ⟨197528440356112871846140901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131685626904075247897427267 197528440356112871846140901)
          ·
            refine ⟨37036582566771163471151419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 197528440356112871846140901 37036582566771163471151419)
            ·
              refine ⟨55554873850156745206727129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37036582566771163471151419 55554873850156745206727129)
              ·
                refine ⟨41666155387617558905045347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55554873850156745206727129 41666155387617558905045347)
                ·
                  refine ⟨62499233081426338357568021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41666155387617558905045347 62499233081426338357568021)
                  ·
                    refine ⟨2929651550691859610511001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62499233081426338357568021 2929651550691859610511001)
                    ·
                      refine ⟨2197238663018894707883251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2929651550691859610511001 2197238663018894707883251)
                      ·
                        rfl

theorem cell23_4279107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 6, 2].length) (baseStart_4279107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279107 prefixEnd_4279107 := by exact prefixLift 4279107
  have htrace : WordTrace (prefixWord ++ tailWord_4279107) baseStart_4279107 baseEnd_4279107 := by
    simpa [prefixWord, tailWord_4279107, baseEnd_4279107] using wordTrace_append hprefix tailTrace_4279107
  have hstable : (prefixWord ++ tailWord_4279107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279107).length < 2 ^ (prefixWord ++ tailWord_4279107).sum := by decide
  have hdescent : baseEnd_4279107 < baseStart_4279107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279108 : List Nat := [2, 3, 4, 2, 1, 1, 2, 3, 5]
def baseStart_4279108 : Nat := 118140960795 + 4279108 * 2 ^ 59
def prefixEnd_4279108 : Nat := 4983230072969 + 3 ^ 40 * 4279108 * 2
def baseEnd_4279108 : Nat := 244137686277727689330083

theorem tailTrace_4279108 : CollatzResearch.WordTrace tailWord_4279108 prefixEnd_4279108 244137686277727689330083 := by
  unfold tailWord_4279108
  simp only [CollatzResearch.WordTrace]
  refine ⟨78035945290765002154238989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104047927054353336205651985 78035945290765002154238989)
  ·
    refine ⟨29263479484036875807839621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78035945290765002154238989 29263479484036875807839621)
    ·
      refine ⟨5486902403256914213969929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29263479484036875807839621 5486902403256914213969929)
      ·
        refine ⟨4115176802442685660477447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5486902403256914213969929 4115176802442685660477447)
        ·
          refine ⟨6172765203664028490716171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4115176802442685660477447 6172765203664028490716171)
          ·
            refine ⟨9259147805496042736074257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6172765203664028490716171 9259147805496042736074257)
            ·
              refine ⟨6944360854122032052055693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9259147805496042736074257 6944360854122032052055693)
              ·
                refine ⟨2604135320295762019520885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6944360854122032052055693 2604135320295762019520885)
                ·
                  refine ⟨244137686277727689330083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2604135320295762019520885 244137686277727689330083)
                  ·
                    rfl

theorem cell23_4279108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_4279108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279108 prefixEnd_4279108 := by exact prefixLift 4279108
  have htrace : WordTrace (prefixWord ++ tailWord_4279108) baseStart_4279108 baseEnd_4279108 := by
    simpa [prefixWord, tailWord_4279108, baseEnd_4279108] using wordTrace_append hprefix tailTrace_4279108
  have hstable : (prefixWord ++ tailWord_4279108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279108).length < 2 ^ (prefixWord ++ tailWord_4279108).sum := by decide
  have hdescent : baseEnd_4279108 < baseStart_4279108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279120 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 6]
def baseStart_4279120 : Nat := 118140960795 + 4279120 * 2 ^ 59
def prefixEnd_4279120 : Nat := 4983230072969 + 3 ^ 40 * 4279120 * 2
def baseEnd_4279120 : Nat := 2197245338267403157020691

theorem tailTrace_4279120 : CollatzResearch.WordTrace tailWord_4279120 prefixEnd_4279120 2197245338267403157020691 := by
  unfold tailWord_4279120
  simp only [CollatzResearch.WordTrace]
  refine ⟨78036164128743265178957407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104048218838324353571943209 78036164128743265178957407)
  ·
    refine ⟨117054246193114897768436111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78036164128743265178957407 117054246193114897768436111)
    ·
      refine ⟨175581369289672346652654167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117054246193114897768436111 175581369289672346652654167)
      ·
        refine ⟨263372053934508519978981251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175581369289672346652654167 263372053934508519978981251)
        ·
          refine ⟨395058080901762779968471877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263372053934508519978981251 395058080901762779968471877)
          ·
            refine ⟨74073390169080521244088477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 395058080901762779968471877 74073390169080521244088477)
            ·
              refine ⟨27777521313405195466533179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74073390169080521244088477 27777521313405195466533179)
              ·
                refine ⟨41666281970107793199799769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27777521313405195466533179 41666281970107793199799769)
                ·
                  refine ⟨31249711477580844899849827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41666281970107793199799769 31249711477580844899849827)
                  ·
                    refine ⟨46874567216371267349774741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31249711477580844899849827 46874567216371267349774741)
                    ·
                      refine ⟨2197245338267403157020691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46874567216371267349774741 2197245338267403157020691)
                      ·
                        rfl

theorem cell23_4279120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_4279120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279120 prefixEnd_4279120 := by exact prefixLift 4279120
  have htrace : WordTrace (prefixWord ++ tailWord_4279120) baseStart_4279120 baseEnd_4279120 := by
    simpa [prefixWord, tailWord_4279120, baseEnd_4279120] using wordTrace_append hprefix tailTrace_4279120
  have hstable : (prefixWord ++ tailWord_4279120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279120).length < 2 ^ (prefixWord ++ tailWord_4279120).sum := by decide
  have hdescent : baseEnd_4279120 < baseStart_4279120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279261 : List Nat := [1, 4, 3, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_4279261 : Nat := 118140960795 + 4279261 * 2 ^ 59
def prefixEnd_4279261 : Nat := 4983230072969 + 3 ^ 40 * 4279261 * 2
def baseEnd_4279261 : Nat := 2197317739039687105357543

theorem tailTrace_4279261 : CollatzResearch.WordTrace tailWord_4279261 prefixEnd_4279261 2197317739039687105357543 := by
  unfold tailWord_4279261
  simp only [CollatzResearch.WordTrace]
  refine ⟨156077470949975711438797637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104051647299983807625865091 156077470949975711438797637)
  ·
    refine ⟨29264525803120445894774557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156077470949975711438797637 29264525803120445894774557)
    ·
      refine ⟨10974197176170167210540459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29264525803120445894774557 10974197176170167210540459)
      ·
        refine ⟨16461295764255250815810689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10974197176170167210540459 16461295764255250815810689)
        ·
          refine ⟨12345971823191438111858017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16461295764255250815810689 12345971823191438111858017)
          ·
            refine ⟨9259478867393578583893513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12345971823191438111858017 9259478867393578583893513)
            ·
              refine ⟨6944609150545183937920135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9259478867393578583893513 6944609150545183937920135)
              ·
                refine ⟨10416913725817775906880203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6944609150545183937920135 10416913725817775906880203)
                ·
                  refine ⟨15625370588726663860320305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10416913725817775906880203 15625370588726663860320305)
                  ·
                    refine ⟨11719027941544997895240229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15625370588726663860320305 11719027941544997895240229)
                    ·
                      refine ⟨2197317739039687105357543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11719027941544997895240229 2197317739039687105357543)
                      ·
                        rfl

theorem cell23_4279261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_4279261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279261 prefixEnd_4279261 := by exact prefixLift 4279261
  have htrace : WordTrace (prefixWord ++ tailWord_4279261) baseStart_4279261 baseEnd_4279261 := by
    simpa [prefixWord, tailWord_4279261, baseEnd_4279261] using wordTrace_append hprefix tailTrace_4279261
  have hstable : (prefixWord ++ tailWord_4279261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279261).length < 2 ^ (prefixWord ++ tailWord_4279261).sum := by decide
  have hdescent : baseEnd_4279261 < baseStart_4279261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279264 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 8, 1, 3]
def baseStart_4279264 : Nat := 118140960795 + 4279264 * 2 ^ 59
def prefixEnd_4279264 : Nat := 4983230072969 + 3 ^ 40 * 4279264 * 2
def baseEnd_4279264 : Nat := 2197319279481650593620029

theorem tailTrace_4279264 : CollatzResearch.WordTrace tailWord_4279264 prefixEnd_4279264 2197319279481650593620029 := by
  unfold tailWord_4279264
  simp only [CollatzResearch.WordTrace]
  refine ⟨78038790184482421475578423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104051720245976561967437897 78038790184482421475578423)
  ·
    refine ⟨117058185276723632213367635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78038790184482421475578423 117058185276723632213367635)
    ·
      refine ⟨175587277915085448320051453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117058185276723632213367635 175587277915085448320051453)
      ·
        refine ⟨65845229218157043120019295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175587277915085448320051453 65845229218157043120019295)
        ·
          refine ⟨98767843827235564680028943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65845229218157043120019295 98767843827235564680028943)
          ·
            refine ⟨148151765740853347020043415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98767843827235564680028943 148151765740853347020043415)
            ·
              refine ⟨222227648611280020530065123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148151765740853347020043415 222227648611280020530065123)
              ·
                refine ⟨333341472916920030795097685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222227648611280020530065123 333341472916920030795097685)
                ·
                  refine ⟨3906345385745156610880051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 333341472916920030795097685 3906345385745156610880051)
                  ·
                    refine ⟨5859518078617734916320077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3906345385745156610880051 5859518078617734916320077)
                    ·
                      refine ⟨2197319279481650593620029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5859518078617734916320077 2197319279481650593620029)
                      ·
                        rfl

theorem cell23_4279264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_4279264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279264 prefixEnd_4279264 := by exact prefixLift 4279264
  have htrace : WordTrace (prefixWord ++ tailWord_4279264) baseStart_4279264 baseEnd_4279264 := by
    simpa [prefixWord, tailWord_4279264, baseEnd_4279264] using wordTrace_append hprefix tailTrace_4279264
  have hstable : (prefixWord ++ tailWord_4279264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279264).length < 2 ^ (prefixWord ++ tailWord_4279264).sum := by decide
  have hdescent : baseEnd_4279264 < baseStart_4279264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279267 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 2, 7]
def baseStart_4279267 : Nat := 118140960795 + 4279267 * 2 ^ 59
def prefixEnd_4279267 : Nat := 4983230072969 + 3 ^ 40 * 4279267 * 2
def baseEnd_4279267 : Nat := 732440273307871360627505

theorem tailTrace_4279267 : CollatzResearch.WordTrace tailWord_4279267 prefixEnd_4279267 732440273307871360627505 := by
  unfold tailWord_4279267
  simp only [CollatzResearch.WordTrace]
  refine ⟨156077689787953974463516055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104051793191969316309010703 156077689787953974463516055)
  ·
    refine ⟨234116534681930961695274083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156077689787953974463516055 234116534681930961695274083)
    ·
      refine ⟨351174802022896442542911125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234116534681930961695274083 351174802022896442542911125)
      ·
        refine ⟨16461318844823270744198959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 351174802022896442542911125 16461318844823270744198959)
        ·
          refine ⟨24691978267234906116298439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16461318844823270744198959 24691978267234906116298439)
          ·
            refine ⟨37037967400852359174447659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24691978267234906116298439 37037967400852359174447659)
            ·
              refine ⟨55556951101278538761671489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37037967400852359174447659 55556951101278538761671489)
              ·
                refine ⟨41667713325958904071253617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55556951101278538761671489 41667713325958904071253617)
                ·
                  refine ⟨31250784994469178053440213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41667713325958904071253617 31250784994469178053440213)
                  ·
                    refine ⟨732440273307871360627505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31250784994469178053440213 732440273307871360627505)
                    ·
                      rfl

theorem cell23_4279267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 7].length) (baseStart_4279267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279267 prefixEnd_4279267 := by exact prefixLift 4279267
  have htrace : WordTrace (prefixWord ++ tailWord_4279267) baseStart_4279267 baseEnd_4279267 := by
    simpa [prefixWord, tailWord_4279267, baseEnd_4279267] using wordTrace_append hprefix tailTrace_4279267
  have hstable : (prefixWord ++ tailWord_4279267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279267).length < 2 ^ (prefixWord ++ tailWord_4279267).sum := by decide
  have hdescent : baseEnd_4279267 < baseStart_4279267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279282 : List Nat := [3, 2, 1, 5, 2, 1, 2, 1, 1, 1, 4]
def baseStart_4279282 : Nat := 118140960795 + 4279282 * 2 ^ 59
def prefixEnd_4279282 : Nat := 4983230072969 + 3 ^ 40 * 4279282 * 2
def baseEnd_4279282 : Nat := 2197328522133431523194947

theorem tailTrace_4279282 : CollatzResearch.WordTrace tailWord_4279282 prefixEnd_4279282 2197328522133431523194947 := by
  unfold tailWord_4279282
  simp only [CollatzResearch.WordTrace]
  refine ⟨39019559220724908006328025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104052157921933088016874733 39019559220724908006328025)
  ·
    refine ⟨29264669415543681004746019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39019559220724908006328025 29264669415543681004746019)
    ·
      refine ⟨43897004123315521507119029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29264669415543681004746019 43897004123315521507119029)
      ·
        refine ⟨4115344136560830141292409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43897004123315521507119029 4115344136560830141292409)
        ·
          refine ⟨3086508102420622605969307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4115344136560830141292409 3086508102420622605969307)
          ·
            refine ⟨4629762153630933908953961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3086508102420622605969307 4629762153630933908953961)
            ·
              refine ⟨3472321615223200431715471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4629762153630933908953961 3472321615223200431715471)
              ·
                refine ⟨5208482422834800647573207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3472321615223200431715471 5208482422834800647573207)
                ·
                  refine ⟨7812723634252200971359811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5208482422834800647573207 7812723634252200971359811)
                  ·
                    refine ⟨11719085451378301457039717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7812723634252200971359811 11719085451378301457039717)
                    ·
                      refine ⟨2197328522133431523194947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11719085451378301457039717 2197328522133431523194947)
                      ·
                        rfl

theorem cell23_4279282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_4279282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279282 prefixEnd_4279282 := by exact prefixLift 4279282
  have htrace : WordTrace (prefixWord ++ tailWord_4279282) baseStart_4279282 baseEnd_4279282 := by
    simpa [prefixWord, tailWord_4279282, baseEnd_4279282] using wordTrace_append hprefix tailTrace_4279282
  have hstable : (prefixWord ++ tailWord_4279282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279282).length < 2 ^ (prefixWord ++ tailWord_4279282).sum := by decide
  have hdescent : baseEnd_4279282 < baseStart_4279282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279285 : List Nat := [1, 3, 5, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_4279285 : Nat := 118140960795 + 4279285 * 2 ^ 59
def prefixEnd_4279285 : Nat := 4983230072969 + 3 ^ 40 * 4279285 * 2
def baseEnd_4279285 : Nat := 2197330062575395011457433

theorem tailTrace_4279285 : CollatzResearch.WordTrace tailWord_4279285 prefixEnd_4279285 2197330062575395011457433 := by
  unfold tailWord_4279285
  simp only [CollatzResearch.WordTrace]
  refine ⟨156078346301888763537671309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104052230867925842358447539 156078346301888763537671309)
  ·
    refine ⟨58529379863208286326626741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156078346301888763537671309 58529379863208286326626741)
    ·
      refine ⟨5487129362175776843121257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58529379863208286326626741 5487129362175776843121257)
      ·
        refine ⟨4115347021631832632340943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5487129362175776843121257 4115347021631832632340943)
        ·
          refine ⟨6173020532447748948511415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4115347021631832632340943 6173020532447748948511415)
          ·
            refine ⟨9259530798671623422767123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6173020532447748948511415 9259530798671623422767123)
            ·
              refine ⟨13889296198007435134150685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9259530798671623422767123 13889296198007435134150685)
              ·
                refine ⟨5208486074252788175306507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13889296198007435134150685 5208486074252788175306507)
                ·
                  refine ⟨7812729111379182262959761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5208486074252788175306507 7812729111379182262959761)
                  ·
                    refine ⟨5859546833534386697219821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7812729111379182262959761 5859546833534386697219821)
                    ·
                      refine ⟨2197330062575395011457433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5859546833534386697219821 2197330062575395011457433)
                      ·
                        rfl

theorem cell23_4279285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_4279285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279285 prefixEnd_4279285 := by exact prefixLift 4279285
  have htrace : WordTrace (prefixWord ++ tailWord_4279285) baseStart_4279285 baseEnd_4279285 := by
    simpa [prefixWord, tailWord_4279285, baseEnd_4279285] using wordTrace_append hprefix tailTrace_4279285
  have hstable : (prefixWord ++ tailWord_4279285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279285).length < 2 ^ (prefixWord ++ tailWord_4279285).sum := by decide
  have hdescent : baseEnd_4279285 < baseStart_4279285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279321 : List Nat := [1, 2, 1, 2, 1, 1, 7, 1, 1, 4, 2]
def baseStart_4279321 : Nat := 118140960795 + 4279321 * 2 ^ 59
def prefixEnd_4279321 : Nat := 4983230072969 + 3 ^ 40 * 4279321 * 2
def baseEnd_4279321 : Nat := 2197348547878956870607267

theorem tailTrace_4279321 : CollatzResearch.WordTrace tailWord_4279321 prefixEnd_4279321 2197348547878956870607267 := by
  unfold tailWord_4279321
  simp only [CollatzResearch.WordTrace]
  refine ⟨156079659329758341685981817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104053106219838894457321211 156079659329758341685981817)
  ·
    refine ⟨117059744497318756264486363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156079659329758341685981817 117059744497318756264486363)
    ·
      refine ⟨175589616745978134396729545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117059744497318756264486363 175589616745978134396729545)
      ·
        refine ⟨131692212559483600797547159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175589616745978134396729545 131692212559483600797547159)
        ·
          refine ⟨197538318839225401196320739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131692212559483600797547159 197538318839225401196320739)
          ·
            refine ⟨296307478258838101794481109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197538318839225401196320739 296307478258838101794481109)
            ·
              refine ⟨6944706521691518010808151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 296307478258838101794481109 6944706521691518010808151)
              ·
                refine ⟨10417059782537277016212227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6944706521691518010808151 10417059782537277016212227)
                ·
                  refine ⟨15625589673805915524318341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10417059782537277016212227 15625589673805915524318341)
                  ·
                    refine ⟨2929798063838609160809689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15625589673805915524318341 2929798063838609160809689)
                    ·
                      refine ⟨2197348547878956870607267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2929798063838609160809689 2197348547878956870607267)
                      ·
                        rfl

theorem cell23_4279321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 4, 2].length) (baseStart_4279321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279321 prefixEnd_4279321 := by exact prefixLift 4279321
  have htrace : WordTrace (prefixWord ++ tailWord_4279321) baseStart_4279321 baseEnd_4279321 := by
    simpa [prefixWord, tailWord_4279321, baseEnd_4279321] using wordTrace_append hprefix tailTrace_4279321
  have hstable : (prefixWord ++ tailWord_4279321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279321).length < 2 ^ (prefixWord ++ tailWord_4279321).sum := by decide
  have hdescent : baseEnd_4279321 < baseStart_4279321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279325 : List Nat := [1, 4, 2, 2, 3, 1, 2, 2, 1, 3, 2]
def baseStart_4279325 : Nat := 118140960795 + 4279325 * 2 ^ 59
def prefixEnd_4279325 : Nat := 4983230072969 + 3 ^ 40 * 4279325 * 2
def baseEnd_4279325 : Nat := 2197350601801574854957249

theorem tailTrace_4279325 : CollatzResearch.WordTrace tailWord_4279325 prefixEnd_4279325 2197350601801574854957249 := by
  unfold tailWord_4279325
  simp only [CollatzResearch.WordTrace]
  refine ⟨156079805221743850369127429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104053203481162566912751619 156079805221743850369127429)
  ·
    refine ⟨29264963479076971944211393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156079805221743850369127429 29264963479076971944211393)
    ·
      refine ⟨21948722609307728958158545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29264963479076971944211393 21948722609307728958158545)
      ·
        refine ⟨16461541956980796718618909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21948722609307728958158545 16461541956980796718618909)
        ·
          refine ⟨6173078233867798769482091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16461541956980796718618909 6173078233867798769482091)
          ·
            refine ⟨9259617350801698154223137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6173078233867798769482091 9259617350801698154223137)
            ·
              refine ⟨6944713013101273615667353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9259617350801698154223137 6944713013101273615667353)
              ·
                refine ⟨5208534759825955211750515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6944713013101273615667353 5208534759825955211750515)
                ·
                  refine ⟨7812802139738932817625773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5208534759825955211750515 7812802139738932817625773)
                  ·
                    refine ⟨2929800802402099806609665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7812802139738932817625773 2929800802402099806609665)
                    ·
                      refine ⟨2197350601801574854957249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2929800802402099806609665 2197350601801574854957249)
                      ·
                        rfl

theorem cell23_4279325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_4279325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279325 prefixEnd_4279325 := by exact prefixLift 4279325
  have htrace : WordTrace (prefixWord ++ tailWord_4279325) baseStart_4279325 baseEnd_4279325 := by
    simpa [prefixWord, tailWord_4279325, baseEnd_4279325] using wordTrace_append hprefix tailTrace_4279325
  have hstable : (prefixWord ++ tailWord_4279325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279325).length < 2 ^ (prefixWord ++ tailWord_4279325).sum := by decide
  have hdescent : baseEnd_4279325 < baseStart_4279325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279354 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3]
def baseStart_4279354 : Nat := 118140960795 + 4279354 * 2 ^ 59
def prefixEnd_4279354 : Nat := 4983230072969 + 3 ^ 40 * 4279354 * 2
def baseEnd_4279354 : Nat := 2197365492740555241494615

theorem tailTrace_4279354 : CollatzResearch.WordTrace tailWord_4279354 prefixEnd_4279354 2197365492740555241494615 := by
  unfold tailWord_4279354
  simp only [CollatzResearch.WordTrace]
  refine ⟨39020215734659697080483279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104053908625759192214622077 39020215734659697080483279)
  ·
    refine ⟨58530323601989545620724919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39020215734659697080483279 58530323601989545620724919)
    ·
      refine ⟨87795485402984318431087379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58530323601989545620724919 87795485402984318431087379)
      ·
        refine ⟨131693228104476477646631069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87795485402984318431087379 131693228104476477646631069)
        ·
          refine ⟨49384960539178679117486651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131693228104476477646631069 49384960539178679117486651)
          ·
            refine ⟨74077440808768018676229977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49384960539178679117486651 74077440808768018676229977)
            ·
              refine ⟨55558080606576014007172483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74077440808768018676229977 55558080606576014007172483)
              ·
                refine ⟨83337120909864021010758725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55558080606576014007172483 83337120909864021010758725)
                ·
                  refine ⟨15625710170599503939517261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83337120909864021010758725 15625710170599503939517261)
                  ·
                    refine ⟨5859641313974813977318973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15625710170599503939517261 5859641313974813977318973)
                    ·
                      refine ⟨2197365492740555241494615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5859641313974813977318973 2197365492740555241494615)
                      ·
                        rfl

theorem cell23_4279354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_4279354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279354 prefixEnd_4279354 := by exact prefixLift 4279354
  have htrace : WordTrace (prefixWord ++ tailWord_4279354) baseStart_4279354 baseEnd_4279354 := by
    simpa [prefixWord, tailWord_4279354, baseEnd_4279354] using wordTrace_append hprefix tailTrace_4279354
  have hstable : (prefixWord ++ tailWord_4279354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279354).length < 2 ^ (prefixWord ++ tailWord_4279354).sum := by decide
  have hdescent : baseEnd_4279354 < baseStart_4279354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279374 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 4, 5]
def baseStart_4279374 : Nat := 118140960795 + 4279374 * 2 ^ 59
def prefixEnd_4279374 : Nat := 4983230072969 + 3 ^ 40 * 4279374 * 2
def baseEnd_4279374 : Nat := 732458587451215054414841

theorem tailTrace_4279374 : CollatzResearch.WordTrace tailWord_4279374 prefixEnd_4279374 732458587451215054414841 := by
  unfold tailWord_4279374
  simp only [CollatzResearch.WordTrace]
  refine ⟨19510199049820791467207647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104054394932377554491774117 19510199049820791467207647)
  ·
    refine ⟨29265298574731187200811471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19510199049820791467207647 29265298574731187200811471)
    ·
      refine ⟨43897947862096780801217207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29265298574731187200811471 43897947862096780801217207)
      ·
        refine ⟨65846921793145171201825811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43897947862096780801217207 65846921793145171201825811)
        ·
          refine ⟨98770382689717756802738717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65846921793145171201825811 98770382689717756802738717)
          ·
            refine ⟨37038893508644158801027019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98770382689717756802738717 37038893508644158801027019)
            ·
              refine ⟨55558340262966238201540529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37038893508644158801027019 55558340262966238201540529)
              ·
                refine ⟨41668755197224678651155397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55558340262966238201540529 41668755197224678651155397)
                ·
                  refine ⟨7812891599479627247091637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41668755197224678651155397 7812891599479627247091637)
                  ·
                    refine ⟨732458587451215054414841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7812891599479627247091637 732458587451215054414841)
                    ·
                      rfl

theorem cell23_4279374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_4279374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279374 prefixEnd_4279374 := by exact prefixLift 4279374
  have htrace : WordTrace (prefixWord ++ tailWord_4279374) baseStart_4279374 baseEnd_4279374 := by
    simpa [prefixWord, tailWord_4279374, baseEnd_4279374] using wordTrace_append hprefix tailTrace_4279374
  have hstable : (prefixWord ++ tailWord_4279374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279374).length < 2 ^ (prefixWord ++ tailWord_4279374).sum := by decide
  have hdescent : baseEnd_4279374 < baseStart_4279374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279421 : List Nat := [1, 4, 1, 1, 3, 1, 2, 3, 3, 4]
def baseStart_4279421 : Nat := 118140960795 + 4279421 * 2 ^ 59
def prefixEnd_4279421 : Nat := 4983230072969 + 3 ^ 40 * 4279421 * 2
def baseEnd_4279421 : Nat := 732466631981468826452269

theorem tailTrace_4279421 : CollatzResearch.WordTrace tailWord_4279421 prefixEnd_4279421 732466631981468826452269 := by
  unfold tailWord_4279421
  simp only [CollatzResearch.WordTrace]
  refine ⟨156083306629396058764622117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104055537752930705843081411 156083306629396058764622117)
  ·
    refine ⟨29265619993011761018366647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156083306629396058764622117 29265619993011761018366647)
    ·
      refine ⟨43898429989517641527549971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29265619993011761018366647 43898429989517641527549971)
      ·
        refine ⟨65847644984276462291324957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43898429989517641527549971 65847644984276462291324957)
        ·
          refine ⟨24692866869103673359246859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65847644984276462291324957 24692866869103673359246859)
          ·
            refine ⟨37039300303655510038870289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24692866869103673359246859 37039300303655510038870289)
            ·
              refine ⟨27779475227741632529152717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37039300303655510038870289 27779475227741632529152717)
              ·
                refine ⟨10417303210403112198432269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27779475227741632529152717 10417303210403112198432269)
                ·
                  refine ⟨3906488703901167074412101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10417303210403112198432269 3906488703901167074412101)
                  ·
                    refine ⟨732466631981468826452269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3906488703901167074412101 732466631981468826452269)
                    ·
                      rfl

theorem cell23_4279421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_4279421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279421 prefixEnd_4279421 := by exact prefixLift 4279421
  have htrace : WordTrace (prefixWord ++ tailWord_4279421) baseStart_4279421 baseEnd_4279421 := by
    simpa [prefixWord, tailWord_4279421, baseEnd_4279421] using wordTrace_append hprefix tailTrace_4279421
  have hstable : (prefixWord ++ tailWord_4279421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279421).length < 2 ^ (prefixWord ++ tailWord_4279421).sum := by decide
  have hdescent : baseEnd_4279421 < baseStart_4279421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279422 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_4279422 : Nat := 118140960795 + 4279422 * 2 ^ 59
def prefixEnd_4279422 : Nat := 4983230072969 + 3 ^ 40 * 4279422 * 2
def baseEnd_4279422 : Nat := 2197400409425060975444303

theorem tailTrace_4279422 : CollatzResearch.WordTrace tailWord_4279422 prefixEnd_4279422 2197400409425060975444303 := by
  unfold tailWord_4279422
  simp only [CollatzResearch.WordTrace]
  refine ⟨19510417887799054491926065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104055562068261623956939013 19510417887799054491926065)
  ·
    refine ⟨14632813415849290868944549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19510417887799054491926065 14632813415849290868944549)
    ·
      refine ⟨2743652515471742037927103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14632813415849290868944549 2743652515471742037927103)
      ·
        refine ⟨4115478773207613056890655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2743652515471742037927103 4115478773207613056890655)
        ·
          refine ⟨6173218159811419585335983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4115478773207613056890655 6173218159811419585335983)
          ·
            refine ⟨9259827239717129378003975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6173218159811419585335983 9259827239717129378003975)
            ·
              refine ⟨13889740859575694067005963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9259827239717129378003975 13889740859575694067005963)
              ·
                refine ⟨20834611289363541100508945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13889740859575694067005963 20834611289363541100508945)
                ·
                  refine ⟨15625958467022655825381709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20834611289363541100508945 15625958467022655825381709)
                  ·
                    refine ⟨5859734425133495934518141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15625958467022655825381709 5859734425133495934518141)
                    ·
                      refine ⟨2197400409425060975444303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5859734425133495934518141 2197400409425060975444303)
                      ·
                        rfl

theorem cell23_4279422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_4279422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279422 prefixEnd_4279422 := by exact prefixLift 4279422
  have htrace : WordTrace (prefixWord ++ tailWord_4279422) baseStart_4279422 baseEnd_4279422 := by
    simpa [prefixWord, tailWord_4279422, baseEnd_4279422] using wordTrace_append hprefix tailTrace_4279422
  have hstable : (prefixWord ++ tailWord_4279422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279422).length < 2 ^ (prefixWord ++ tailWord_4279422).sum := by decide
  have hdescent : baseEnd_4279422 < baseStart_4279422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279428 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 2, 4, 2]
def baseStart_4279428 : Nat := 118140960795 + 4279428 * 2 ^ 59
def prefixEnd_4279428 : Nat := 4983230072969 + 3 ^ 40 * 4279428 * 2
def baseEnd_4279428 : Nat := 2197403490308987951969275

theorem tailTrace_4279428 : CollatzResearch.WordTrace tailWord_4279428 prefixEnd_4279428 2197403490308987951969275 := by
  unfold tailWord_4279428
  simp only [CollatzResearch.WordTrace]
  refine ⟨78041780970185349480063469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104055707960247132640084625 78041780970185349480063469)
  ·
    refine ⟨29265667863819506055023801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78041780970185349480063469 29265667863819506055023801)
    ·
      refine ⟨21949250897864629541267851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29265667863819506055023801 21949250897864629541267851)
      ·
        refine ⟨32923876346796944311901777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21949250897864629541267851 32923876346796944311901777)
        ·
          refine ⟨24692907260097708233926333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32923876346796944311901777 24692907260097708233926333)
          ·
            refine ⟨9259840222536640587722375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24692907260097708233926333 9259840222536640587722375)
            ·
              refine ⟨13889760333804960881583563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9259840222536640587722375 13889760333804960881583563)
              ·
                refine ⟨20834640500707441322375345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13889760333804960881583563 20834640500707441322375345)
                ·
                  refine ⟨15625980375530580991781509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20834640500707441322375345 15625980375530580991781509)
                  ·
                    refine ⟨2929871320411983935959033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15625980375530580991781509 2929871320411983935959033)
                    ·
                      refine ⟨2197403490308987951969275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2929871320411983935959033 2197403490308987951969275)
                      ·
                        rfl

theorem cell23_4279428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_4279428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279428 prefixEnd_4279428 := by exact prefixLift 4279428
  have htrace : WordTrace (prefixWord ++ tailWord_4279428) baseStart_4279428 baseEnd_4279428 := by
    simpa [prefixWord, tailWord_4279428, baseEnd_4279428] using wordTrace_append hprefix tailTrace_4279428
  have hstable : (prefixWord ++ tailWord_4279428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279428).length < 2 ^ (prefixWord ++ tailWord_4279428).sum := by decide
  have hdescent : baseEnd_4279428 < baseStart_4279428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279438 : List Nat := [4, 1, 1, 3, 2, 2, 1, 2, 3, 4]
def baseStart_4279438 : Nat := 118140960795 + 4279438 * 2 ^ 59
def prefixEnd_4279438 : Nat := 4983230072969 + 3 ^ 40 * 4279438 * 2
def baseEnd_4279438 : Nat := 732469541705177637614743

theorem tailTrace_4279438 : CollatzResearch.WordTrace tailWord_4279438 prefixEnd_4279438 732469541705177637614743 := by
  unfold tailWord_4279438
  simp only [CollatzResearch.WordTrace]
  refine ⟨19510490833791808833498871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104055951113556313778660645 19510490833791808833498871)
  ·
    refine ⟨29265736250687713250248307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19510490833791808833498871 29265736250687713250248307)
    ·
      refine ⟨43898604376031569875372461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29265736250687713250248307 43898604376031569875372461)
      ·
        refine ⟨16461976641011838703264673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43898604376031569875372461 16461976641011838703264673)
        ·
          refine ⟨12346482480758879027448505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16461976641011838703264673 12346482480758879027448505)
          ·
            refine ⟨9259861860569159270586379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12346482480758879027448505 9259861860569159270586379)
            ·
              refine ⟨13889792790853738905879569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9259861860569159270586379 13889792790853738905879569)
              ·
                refine ⟨10417344593140304179409677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13889792790853738905879569 10417344593140304179409677)
                ·
                  refine ⟨3906504222427614067278629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10417344593140304179409677 3906504222427614067278629)
                  ·
                    refine ⟨732469541705177637614743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3906504222427614067278629 732469541705177637614743)
                    ·
                      rfl

theorem cell23_4279438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_4279438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279438 prefixEnd_4279438 := by exact prefixLift 4279438
  have htrace : WordTrace (prefixWord ++ tailWord_4279438) baseStart_4279438 baseEnd_4279438 := by
    simpa [prefixWord, tailWord_4279438, baseEnd_4279438] using wordTrace_append hprefix tailTrace_4279438
  have hstable : (prefixWord ++ tailWord_4279438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279438).length < 2 ^ (prefixWord ++ tailWord_4279438).sum := by decide
  have hdescent : baseEnd_4279438 < baseStart_4279438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279448 : List Nat := [2, 1, 2, 4, 2, 1, 3, 1, 2, 2, 3]
def baseStart_4279448 : Nat := 118140960795 + 4279448 * 2 ^ 59
def prefixEnd_4279448 : Nat := 4983230072969 + 3 ^ 40 * 4279448 * 2
def baseEnd_4279448 : Nat := 2197413759922077873719183

theorem tailTrace_4279448 : CollatzResearch.WordTrace tailWord_4279448 prefixEnd_4279448 2197413759922077873719183 := by
  unfold tailWord_4279448
  simp only [CollatzResearch.WordTrace]
  refine ⟨78042145700149121187927499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104056194266865494917236665 78042145700149121187927499)
  ·
    refine ⟨117063218550223681781891249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78042145700149121187927499 117063218550223681781891249)
    ·
      refine ⟨87797413912667761336418437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117063218550223681781891249 87797413912667761336418437)
      ·
        refine ⟨16462015108625205250578457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87797413912667761336418437 16462015108625205250578457)
        ·
          refine ⟨12346511331468903937933843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16462015108625205250578457 12346511331468903937933843)
          ·
            refine ⟨18519766997203355906900765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12346511331468903937933843 18519766997203355906900765)
            ·
              refine ⟨6944912623951258465087787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18519766997203355906900765 6944912623951258465087787)
              ·
                refine ⟨10417368935926887697631681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6944912623951258465087787 10417368935926887697631681)
                ·
                  refine ⟨7813026701945165773223761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10417368935926887697631681 7813026701945165773223761)
                  ·
                    refine ⟨5859770026458874329917821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7813026701945165773223761 5859770026458874329917821)
                    ·
                      refine ⟨2197413759922077873719183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5859770026458874329917821 2197413759922077873719183)
                      ·
                        rfl

theorem cell23_4279448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_4279448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279448 prefixEnd_4279448 := by exact prefixLift 4279448
  have htrace : WordTrace (prefixWord ++ tailWord_4279448) baseStart_4279448 baseEnd_4279448 := by
    simpa [prefixWord, tailWord_4279448, baseEnd_4279448] using wordTrace_append hprefix tailTrace_4279448
  have hstable : (prefixWord ++ tailWord_4279448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279448).length < 2 ^ (prefixWord ++ tailWord_4279448).sum := by decide
  have hdescent : baseEnd_4279448 < baseStart_4279448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279498 : List Nat := [3, 1, 2, 1, 3, 3, 2, 2, 1, 5]
def baseStart_4279498 : Nat := 118140960795 + 4279498 * 2 ^ 59
def prefixEnd_4279498 : Nat := 4983230072969 + 3 ^ 40 * 4279498 * 2
def baseEnd_4279498 : Nat := 732479811318267559364651

theorem tailTrace_4279498 : CollatzResearch.WordTrace tailWord_4279498 prefixEnd_4279498 732479811318267559364651 := by
  unfold tailWord_4279498
  simp only [CollatzResearch.WordTrace]
  refine ⟨39021528762529275228793787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104057410033411400610116765 39021528762529275228793787)
  ·
    refine ⟨58532293143793912843190681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39021528762529275228793787 58532293143793912843190681)
    ·
      refine ⟨43899219857845434632393011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58532293143793912843190681 43899219857845434632393011)
      ·
        refine ⟨65848829786768151948589517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43899219857845434632393011 65848829786768151948589517)
        ·
          refine ⟨24693311170038056980721069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65848829786768151948589517 24693311170038056980721069)
          ·
            refine ⟨9259991688764271367770401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24693311170038056980721069 9259991688764271367770401)
            ·
              refine ⟨6944993766573203525827801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9259991688764271367770401 6944993766573203525827801)
              ·
                refine ⟨5208745324929902644370851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6944993766573203525827801 5208745324929902644370851)
                ·
                  refine ⟨7813117987394853966556277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5208745324929902644370851 7813117987394853966556277)
                  ·
                    refine ⟨732479811318267559364651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7813117987394853966556277 732479811318267559364651)
                    ·
                      rfl

theorem cell23_4279498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_4279498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279498 prefixEnd_4279498 := by exact prefixLift 4279498
  have htrace : WordTrace (prefixWord ++ tailWord_4279498) baseStart_4279498 baseEnd_4279498 := by
    simpa [prefixWord, tailWord_4279498, baseEnd_4279498] using wordTrace_append hprefix tailTrace_4279498
  have hstable : (prefixWord ++ tailWord_4279498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279498).length < 2 ^ (prefixWord ++ tailWord_4279498).sum := by decide
  have hdescent : baseEnd_4279498 < baseStart_4279498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279511 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 4, 4]
def baseStart_4279511 : Nat := 118140960795 + 4279511 * 2 ^ 59
def prefixEnd_4279511 : Nat := 4983230072969 + 3 ^ 40 * 4279511 * 2
def baseEnd_4279511 : Nat := 732482036401103709077131

theorem tailTrace_4279511 : CollatzResearch.WordTrace tailWord_4279511 prefixEnd_4279511 732482036401103709077131 := by
  unfold tailWord_4279511
  simp only [CollatzResearch.WordTrace]
  refine ⟨156086589199070004135398387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104057726132713336090265591 156086589199070004135398387)
  ·
    refine ⟨234129883798605006203097581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156086589199070004135398387 234129883798605006203097581)
    ·
      refine ⟨87798706424476877326161593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234129883798605006203097581 87798706424476877326161593)
      ·
        refine ⟨65849029818357657994621195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87798706424476877326161593 65849029818357657994621195)
        ·
          refine ⟨98773544727536486991931793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65849029818357657994621195 98773544727536486991931793)
          ·
            refine ⟨74080158545652365243948845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98773544727536486991931793 74080158545652365243948845)
            ·
              refine ⟨27780059454619636966480817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74080158545652365243948845 27780059454619636966480817)
              ·
                refine ⟨20835044590964727724860613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27780059454619636966480817 20835044590964727724860613)
                ·
                  refine ⟨3906570860805886448411365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20835044590964727724860613 3906570860805886448411365)
                  ·
                    refine ⟨732482036401103709077131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3906570860805886448411365 732482036401103709077131)
                    ·
                      rfl

theorem cell23_4279511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 4].length) (baseStart_4279511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279511 prefixEnd_4279511 := by exact prefixLift 4279511
  have htrace : WordTrace (prefixWord ++ tailWord_4279511) baseStart_4279511 baseEnd_4279511 := by
    simpa [prefixWord, tailWord_4279511, baseEnd_4279511] using wordTrace_append hprefix tailTrace_4279511
  have hstable : (prefixWord ++ tailWord_4279511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279511).length < 2 ^ (prefixWord ++ tailWord_4279511).sum := by decide
  have hdescent : baseEnd_4279511 < baseStart_4279511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279521 : List Nat := [1, 2, 3, 1, 3, 2, 1, 3, 1, 1, 5]
def baseStart_4279521 : Nat := 118140960795 + 4279521 * 2 ^ 59
def prefixEnd_4279521 : Nat := 4983230072969 + 3 ^ 40 * 4279521 * 2
def baseEnd_4279521 : Nat := 2197451244009856088106347

theorem tailTrace_4279521 : CollatzResearch.WordTrace tailWord_4279521 prefixEnd_4279521 2197451244009856088106347 := by
  unfold tailWord_4279521
  simp only [CollatzResearch.WordTrace]
  refine ⟨156086953929033775843262417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104057969286022517228841611 156086953929033775843262417)
  ·
    refine ⟨117065215446775331882446813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156086953929033775843262417 117065215446775331882446813)
    ·
      refine ⟨43899455792540749455917555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117065215446775331882446813 43899455792540749455917555)
      ·
        refine ⟨65849183688811124183876333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43899455792540749455917555 65849183688811124183876333)
        ·
          refine ⟨24693443883304171568953625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65849183688811124183876333 24693443883304171568953625)
          ·
            refine ⟨18520082912478128676715219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24693443883304171568953625 18520082912478128676715219)
            ·
              refine ⟨27780124368717193015072829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18520082912478128676715219 27780124368717193015072829)
              ·
                refine ⟨10417546638268947380652311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27780124368717193015072829 10417546638268947380652311)
                ·
                  refine ⟨15626319957403421070978467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10417546638268947380652311 15626319957403421070978467)
                  ·
                    refine ⟨23439479936105131606467701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15626319957403421070978467 23439479936105131606467701)
                    ·
                      refine ⟨2197451244009856088106347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23439479936105131606467701 2197451244009856088106347)
                      ·
                        rfl

theorem cell23_4279521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_4279521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279521 prefixEnd_4279521 := by exact prefixLift 4279521
  have htrace : WordTrace (prefixWord ++ tailWord_4279521) baseStart_4279521 baseEnd_4279521 := by
    simpa [prefixWord, tailWord_4279521, baseEnd_4279521] using wordTrace_append hprefix tailTrace_4279521
  have hstable : (prefixWord ++ tailWord_4279521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279521).length < 2 ^ (prefixWord ++ tailWord_4279521).sum := by decide
  have hdescent : baseEnd_4279521 < baseStart_4279521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279524 : List Nat := [2, 3, 1, 1, 1, 2, 13]
def baseStart_4279524 : Nat := 118140960795 + 4279524 * 2 ^ 59
def prefixEnd_4279524 : Nat := 4983230072969 + 3 ^ 40 * 4279524 * 2
def baseEnd_4279524 : Nat := 27129046721627402177393

theorem tailTrace_4279524 : CollatzResearch.WordTrace tailWord_4279524 prefixEnd_4279524 27129046721627402177393 := by
  unfold tailWord_4279524
  simp only [CollatzResearch.WordTrace]
  refine ⟨78043531674011453677810813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104058042232015271570414417 78043531674011453677810813)
  ·
    refine ⟨29266324377754295129179055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78043531674011453677810813 29266324377754295129179055)
    ·
      refine ⟨43899486566631442693768583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29266324377754295129179055 43899486566631442693768583)
      ·
        refine ⟨65849229849947164040652875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43899486566631442693768583 65849229849947164040652875)
        ·
          refine ⟨98773844774920746060979313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65849229849947164040652875 98773844774920746060979313)
          ·
            refine ⟨74080383581190559545734485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98773844774920746060979313 74080383581190559545734485)
            ·
              refine ⟨27129046721627402177393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 74080383581190559545734485 27129046721627402177393)
              ·
                rfl

theorem cell23_4279524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 13].length) (baseStart_4279524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279524 prefixEnd_4279524 := by exact prefixLift 4279524
  have htrace : WordTrace (prefixWord ++ tailWord_4279524) baseStart_4279524 baseEnd_4279524 := by
    simpa [prefixWord, tailWord_4279524, baseEnd_4279524] using wordTrace_append hprefix tailTrace_4279524
  have hstable : (prefixWord ++ tailWord_4279524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279524).length < 2 ^ (prefixWord ++ tailWord_4279524).sum := by decide
  have hdescent : baseEnd_4279524 < baseStart_4279524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279528 : List Nat := [2, 1, 4, 1, 2, 1, 2, 4, 2, 4]
def baseStart_4279528 : Nat := 118140960795 + 4279528 * 2 ^ 59
def prefixEnd_4279528 : Nat := 4983230072969 + 3 ^ 40 * 4279528 * 2
def baseEnd_4279528 : Nat := 732484946124812520239605

theorem tailTrace_4279528 : CollatzResearch.WordTrace tailWord_4279528 prefixEnd_4279528 732484946124812520239605 := by
  unfold tailWord_4279528
  simp only [CollatzResearch.WordTrace]
  refine ⟨78043604620004208019383619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104058139493338944025844825 78043604620004208019383619)
  ·
    refine ⟨117065406930006312029075429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78043604620004208019383619 117065406930006312029075429)
    ·
      refine ⟨21949763799376183505451643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117065406930006312029075429 21949763799376183505451643)
      ·
        refine ⟨32924645699064275258177465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21949763799376183505451643 32924645699064275258177465)
        ·
          refine ⟨24693484274298206443633099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32924645699064275258177465 24693484274298206443633099)
          ·
            refine ⟨37040226411447309665449649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24693484274298206443633099 37040226411447309665449649)
            ·
              refine ⟨27780169808585482249087237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37040226411447309665449649 27780169808585482249087237)
              ·
                refine ⟨5208781839109777921703857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27780169808585482249087237 5208781839109777921703857)
                ·
                  refine ⟨3906586379332333441277893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5208781839109777921703857 3906586379332333441277893)
                  ·
                    refine ⟨732484946124812520239605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3906586379332333441277893 732484946124812520239605)
                    ·
                      rfl

theorem cell23_4279528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_4279528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279528 prefixEnd_4279528 := by exact prefixLift 4279528
  have htrace : WordTrace (prefixWord ++ tailWord_4279528) baseStart_4279528 baseEnd_4279528 := by
    simpa [prefixWord, tailWord_4279528, baseEnd_4279528] using wordTrace_append hprefix tailTrace_4279528
  have hstable : (prefixWord ++ tailWord_4279528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279528).length < 2 ^ (prefixWord ++ tailWord_4279528).sum := by decide
  have hdescent : baseEnd_4279528 < baseStart_4279528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279555 : List Nat := [1, 1, 1, 3, 2, 6, 1, 2, 1, 2, 3]
def baseStart_4279555 : Nat := 118140960795 + 4279555 * 2 ^ 59
def prefixEnd_4279555 : Nat := 4983230072969 + 3 ^ 40 * 4279555 * 2
def baseEnd_4279555 : Nat := 2197468702352108955081191

theorem tailTrace_4279555 : CollatzResearch.WordTrace tailWord_4279555 prefixEnd_4279555 2197468702352108955081191 := by
  unfold tailWord_4279555
  simp only [CollatzResearch.WordTrace]
  refine ⟨156088194010910599650000119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104058796007273733100000079 156088194010910599650000119)
  ·
    refine ⟨234132291016365899475000179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156088194010910599650000119 234132291016365899475000179)
    ·
      refine ⟨351198436524548849212500269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234132291016365899475000179 351198436524548849212500269)
      ·
        refine ⟨131699413696705818454687601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 351198436524548849212500269 131699413696705818454687601)
        ·
          refine ⟨98774560272529363841015701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131699413696705818454687601 98774560272529363841015701)
          ·
            refine ⟨4630057512774813930047611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 98774560272529363841015701 4630057512774813930047611)
            ·
              refine ⟨6945086269162220895071417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4630057512774813930047611 6945086269162220895071417)
              ·
                refine ⟨5208814701871665671303563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6945086269162220895071417 5208814701871665671303563)
                ·
                  refine ⟨7813222052807498506955345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5208814701871665671303563 7813222052807498506955345)
                  ·
                    refine ⟨5859916539605623880216509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7813222052807498506955345 5859916539605623880216509)
                    ·
                      refine ⟨2197468702352108955081191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5859916539605623880216509 2197468702352108955081191)
                      ·
                        rfl

theorem cell23_4279555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 2, 3].length) (baseStart_4279555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279555 prefixEnd_4279555 := by exact prefixLift 4279555
  have htrace : WordTrace (prefixWord ++ tailWord_4279555) baseStart_4279555 baseEnd_4279555 := by
    simpa [prefixWord, tailWord_4279555, baseEnd_4279555] using wordTrace_append hprefix tailTrace_4279555
  have hstable : (prefixWord ++ tailWord_4279555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279555).length < 2 ^ (prefixWord ++ tailWord_4279555).sum := by decide
  have hdescent : baseEnd_4279555 < baseStart_4279555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279601 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 1, 8]
def baseStart_4279601 : Nat := 118140960795 + 4279601 * 2 ^ 59
def prefixEnd_4279601 : Nat := 4983230072969 + 3 ^ 40 * 4279601 * 2
def baseEnd_4279601 : Nat := 732497440820738591701993

theorem tailTrace_4279601 : CollatzResearch.WordTrace tailWord_4279601 prefixEnd_4279601 732497440820738591701993 := by
  unfold tailWord_4279601
  simp only [CollatzResearch.WordTrace]
  refine ⟨156089871768743949506174657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104059914512495966337449771 156089871768743949506174657)
  ·
    refine ⟨117067403826557962129630993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156089871768743949506174657 117067403826557962129630993)
    ·
      refine ⟨87800552869918471597223245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117067403826557962129630993 87800552869918471597223245)
      ·
        refine ⟨32925207326219426848958717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87800552869918471597223245 32925207326219426848958717)
        ·
          refine ⟨12346952747332285068359519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32925207326219426848958717 12346952747332285068359519)
          ·
            refine ⟨18520429120998427602539279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12346952747332285068359519 18520429120998427602539279)
            ·
              refine ⟨27780643681497641403808919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18520429120998427602539279 27780643681497641403808919)
              ·
                refine ⟨41670965522246462105713379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27780643681497641403808919 41670965522246462105713379)
                ·
                  refine ⟨62506448283369693158570069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41670965522246462105713379 62506448283369693158570069)
                  ·
                    refine ⟨732497440820738591701993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62506448283369693158570069 732497440820738591701993)
                    ·
                      rfl

theorem cell23_4279601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_4279601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279601 prefixEnd_4279601 := by exact prefixLift 4279601
  have htrace : WordTrace (prefixWord ++ tailWord_4279601) baseStart_4279601 baseEnd_4279601 := by
    simpa [prefixWord, tailWord_4279601, baseEnd_4279601] using wordTrace_append hprefix tailTrace_4279601
  have hstable : (prefixWord ++ tailWord_4279601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279601).length < 2 ^ (prefixWord ++ tailWord_4279601).sum := by decide
  have hdescent : baseEnd_4279601 < baseStart_4279601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279642 : List Nat := [3, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2]
def baseStart_4279642 : Nat := 118140960795 + 4279642 * 2 ^ 59
def prefixEnd_4279642 : Nat := 4983230072969 + 3 ^ 40 * 4279642 * 2
def baseEnd_4279642 : Nat := 2197513375169050114693291

theorem tailTrace_4279642 : CollatzResearch.WordTrace tailWord_4279642 prefixEnd_4279642 2197513375169050114693291 := by
  unfold tailWord_4279642
  simp only [CollatzResearch.WordTrace]
  refine ⟨39022841790398853377104295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104060911441063609005611453 39022841790398853377104295)
  ·
    refine ⟨58534262685598280065656443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39022841790398853377104295 58534262685598280065656443)
    ·
      refine ⟨87801394028397420098484665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58534262685598280065656443 87801394028397420098484665)
      ·
        refine ⟨65851045521298065073863499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87801394028397420098484665 65851045521298065073863499)
        ·
          refine ⟨98776568281947097610795249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65851045521298065073863499 98776568281947097610795249)
          ·
            refine ⟨74082426211460323208096437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98776568281947097610795249 74082426211460323208096437)
            ·
              refine ⟨6945227457324405300759041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74082426211460323208096437 6945227457324405300759041)
              ·
                refine ⟨5208920592993303975569281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6945227457324405300759041 5208920592993303975569281)
                ·
                  refine ⟨3906690444744977981676961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5208920592993303975569281 3906690444744977981676961)
                  ·
                    refine ⟨2930017833558733486257721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3906690444744977981676961 2930017833558733486257721)
                    ·
                      refine ⟨2197513375169050114693291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2930017833558733486257721 2197513375169050114693291)
                      ·
                        rfl

theorem cell23_4279642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_4279642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279642 prefixEnd_4279642 := by exact prefixLift 4279642
  have htrace : WordTrace (prefixWord ++ tailWord_4279642) baseStart_4279642 baseEnd_4279642 := by
    simpa [prefixWord, tailWord_4279642, baseEnd_4279642] using wordTrace_append hprefix tailTrace_4279642
  have hstable : (prefixWord ++ tailWord_4279642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279642).length < 2 ^ (prefixWord ++ tailWord_4279642).sum := by decide
  have hdescent : baseEnd_4279642 < baseStart_4279642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279648 : List Nat := [2, 1, 1, 3, 4, 2, 2, 1, 7]
def baseStart_4279648 : Nat := 118140960795 + 4279648 * 2 ^ 59
def prefixEnd_4279648 : Nat := 4983230072969 + 3 ^ 40 * 4279648 * 2
def baseEnd_4279648 : Nat := 244168495116997454579807

theorem tailTrace_4279648 : CollatzResearch.WordTrace tailWord_4279648 prefixEnd_4279648 244168495116997454579807 := by
  unfold tailWord_4279648
  simp only [CollatzResearch.WordTrace]
  refine ⟨78045792999786838266567799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104061057333049117688757065 78045792999786838266567799)
  ·
    refine ⟨117068689499680257399851699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78045792999786838266567799 117068689499680257399851699)
    ·
      refine ⟨175603034249520386099777549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117068689499680257399851699 175603034249520386099777549)
      ·
        refine ⟨65851137843570144787416581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175603034249520386099777549 65851137843570144787416581)
        ·
          refine ⟨12347088345669402147640609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65851137843570144787416581 12347088345669402147640609)
          ·
            refine ⟨9260316259252051610730457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12347088345669402147640609 9260316259252051610730457)
            ·
              refine ⟨6945237194439038708047843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9260316259252051610730457 6945237194439038708047843)
              ·
                refine ⟨10417855791658558062071765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6945237194439038708047843 10417855791658558062071765)
                ·
                  refine ⟨244168495116997454579807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10417855791658558062071765 244168495116997454579807)
                  ·
                    rfl

theorem cell23_4279648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 7].length) (baseStart_4279648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279648 prefixEnd_4279648 := by exact prefixLift 4279648
  have htrace : WordTrace (prefixWord ++ tailWord_4279648) baseStart_4279648 baseEnd_4279648 := by
    simpa [prefixWord, tailWord_4279648, baseEnd_4279648] using wordTrace_append hprefix tailTrace_4279648
  have hstable : (prefixWord ++ tailWord_4279648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279648).length < 2 ^ (prefixWord ++ tailWord_4279648).sum := by decide
  have hdescent : baseEnd_4279648 < baseStart_4279648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279710 : List Nat := [4, 3, 1, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_4279710 : Nat := 118140960795 + 4279710 * 2 ^ 59
def prefixEnd_4279710 : Nat := 4983230072969 + 3 ^ 40 * 4279710 * 2
def baseEnd_4279710 : Nat := 2197548291853555848642979

theorem tailTrace_4279710 : CollatzResearch.WordTrace tailWord_4279710 prefixEnd_4279710 2197548291853555848642979 := by
  unfold tailWord_4279710
  simp only [CollatzResearch.WordTrace]
  refine ⟨19511730915668632640236573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104062564883566040747928389 19511730915668632640236573)
  ·
    refine ⟨7316899093375737240088715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19511730915668632640236573 7316899093375737240088715)
    ·
      refine ⟨10975348640063605860133073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7316899093375737240088715 10975348640063605860133073)
      ·
        refine ⟨8231511480047704395099805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10975348640063605860133073 8231511480047704395099805)
        ·
          refine ⟨3086816805017889148162427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8231511480047704395099805 3086816805017889148162427)
          ·
            refine ⟨4630225207526833722243641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3086816805017889148162427 4630225207526833722243641)
            ·
              refine ⟨3472668905645125291682731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4630225207526833722243641 3472668905645125291682731)
              ·
                refine ⟨5209003358467687937524097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3472668905645125291682731 5209003358467687937524097)
                ·
                  refine ⟨3906752518850765953143073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5209003358467687937524097 3906752518850765953143073)
                  ·
                    refine ⟨2930064389138074464857305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3906752518850765953143073 2930064389138074464857305)
                    ·
                      refine ⟨2197548291853555848642979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2930064389138074464857305 2197548291853555848642979)
                      ·
                        rfl

theorem cell23_4279710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_4279710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279710 prefixEnd_4279710 := by exact prefixLift 4279710
  have htrace : WordTrace (prefixWord ++ tailWord_4279710) baseStart_4279710 baseEnd_4279710 := by
    simpa [prefixWord, tailWord_4279710, baseEnd_4279710] using wordTrace_append hprefix tailTrace_4279710
  have hstable : (prefixWord ++ tailWord_4279710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279710).length < 2 ^ (prefixWord ++ tailWord_4279710).sum := by decide
  have hdescent : baseEnd_4279710 < baseStart_4279710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279735 : List Nat := [1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 3]
def baseStart_4279735 : Nat := 118140960795 + 4279735 * 2 ^ 59
def prefixEnd_4279735 : Nat := 4983230072969 + 3 ^ 40 * 4279735 * 2
def baseEnd_4279735 : Nat := 2197561128869918250830363

theorem tailTrace_4279735 : CollatzResearch.WordTrace tailWord_4279735 prefixEnd_4279735 2197561128869918250830363 := by
  unfold tailWord_4279735
  simp only [CollatzResearch.WordTrace]
  refine ⟨156094759150258490391552659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104063172766838993594368439 156094759150258490391552659)
  ·
    refine ⟨234142138725387735587328989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156094759150258490391552659 234142138725387735587328989)
    ·
      refine ⟨87803302022020400845248371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234142138725387735587328989 87803302022020400845248371)
      ·
        refine ⟨131704953033030601267872557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87803302022020400845248371 131704953033030601267872557)
        ·
          refine ⟨49389357387386475475452209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131704953033030601267872557 49389357387386475475452209)
          ·
            refine ⟨37042018040539856606589157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49389357387386475475452209 37042018040539856606589157)
            ·
              refine ⟨6945378382601223113735467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37042018040539856606589157 6945378382601223113735467)
              ·
                refine ⟨10418067573901834670603201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6945378382601223113735467 10418067573901834670603201)
                ·
                  refine ⟨7813550680426376002952401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10418067573901834670603201 7813550680426376002952401)
                  ·
                    refine ⟨5860163010319782002214301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7813550680426376002952401 5860163010319782002214301)
                    ·
                      refine ⟨2197561128869918250830363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5860163010319782002214301 2197561128869918250830363)
                      ·
                        rfl

theorem cell23_4279735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_4279735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279735 prefixEnd_4279735 := by exact prefixLift 4279735
  have htrace : WordTrace (prefixWord ++ tailWord_4279735) baseStart_4279735 baseEnd_4279735 := by
    simpa [prefixWord, tailWord_4279735, baseEnd_4279735] using wordTrace_append hprefix tailTrace_4279735
  have hstable : (prefixWord ++ tailWord_4279735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279735).length < 2 ^ (prefixWord ++ tailWord_4279735).sum := by decide
  have hdescent : baseEnd_4279735 < baseStart_4279735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279742 : List Nat := [4, 2, 1, 1, 1, 1, 1, 7, 1, 4]
def baseStart_4279742 : Nat := 118140960795 + 4279742 * 2 ^ 59
def prefixEnd_4279742 : Nat := 4983230072969 + 3 ^ 40 * 4279742 * 2
def baseEnd_4279742 : Nat := 732521574411499907814277

theorem tailTrace_4279742 : CollatzResearch.WordTrace tailWord_4279742 prefixEnd_4279742 732521574411499907814277 := by
  unfold tailWord_4279742
  simp only [CollatzResearch.WordTrace]
  refine ⟨19511876807654141323382185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104063342974155420391371653 19511876807654141323382185)
  ·
    refine ⟨14633907605740605992536639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19511876807654141323382185 14633907605740605992536639)
    ·
      refine ⟨21950861408610908988804959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14633907605740605992536639 21950861408610908988804959)
      ·
        refine ⟨32926292112916363483207439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21950861408610908988804959 32926292112916363483207439)
        ·
          refine ⟨49389438169374545224811159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32926292112916363483207439 49389438169374545224811159)
          ·
            refine ⟨74084157254061817837216739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49389438169374545224811159 74084157254061817837216739)
            ·
              refine ⟨111126235881092726755825109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74084157254061817837216739 111126235881092726755825109)
              ·
                refine ⟨2604521153463110783339651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 111126235881092726755825109 2604521153463110783339651)
                ·
                  refine ⟨3906781730194666175009477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2604521153463110783339651 3906781730194666175009477)
                  ·
                    refine ⟨732521574411499907814277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3906781730194666175009477 732521574411499907814277)
                    ·
                      rfl

theorem cell23_4279742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_4279742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279742 prefixEnd_4279742 := by exact prefixLift 4279742
  have htrace : WordTrace (prefixWord ++ tailWord_4279742) baseStart_4279742 baseEnd_4279742 := by
    simpa [prefixWord, tailWord_4279742, baseEnd_4279742] using wordTrace_append hprefix tailTrace_4279742
  have hstable : (prefixWord ++ tailWord_4279742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279742).length < 2 ^ (prefixWord ++ tailWord_4279742).sum := by decide
  have hdescent : baseEnd_4279742 < baseStart_4279742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279768 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 3, 5]
def baseStart_4279768 : Nat := 118140960795 + 4279768 * 2 ^ 59
def prefixEnd_4279768 : Nat := 4983230072969 + 3 ^ 40 * 4279768 * 2
def baseEnd_4279768 : Nat := 732526024577172207239237

theorem tailTrace_4279768 : CollatzResearch.WordTrace tailWord_4279768 prefixEnd_4279768 732526024577172207239237 := by
  unfold tailWord_4279768
  simp only [CollatzResearch.WordTrace]
  refine ⟨78047981379569468513751979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104063975172759291351669305 78047981379569468513751979)
  ·
    refine ⟨117071972069354202770627969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78047981379569468513751979 117071972069354202770627969)
    ·
      refine ⟨87803979052015652077970977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117071972069354202770627969 87803979052015652077970977)
      ·
        refine ⟨65852984289011739058478233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87803979052015652077970977 65852984289011739058478233)
        ·
          refine ⟨49389738216758804293858675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65852984289011739058478233 49389738216758804293858675)
          ·
            refine ⟨74084607325138206440788013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49389738216758804293858675 74084607325138206440788013)
            ·
              refine ⟨27781727746926827415295505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74084607325138206440788013 27781727746926827415295505)
              ·
                refine ⟨20836295810195120561471629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27781727746926827415295505 20836295810195120561471629)
                ·
                  refine ⟨7813610928823170210551861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20836295810195120561471629 7813610928823170210551861)
                  ·
                    refine ⟨732526024577172207239237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7813610928823170210551861 732526024577172207239237)
                    ·
                      rfl

theorem cell23_4279768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_4279768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279768 prefixEnd_4279768 := by exact prefixLift 4279768
  have htrace : WordTrace (prefixWord ++ tailWord_4279768) baseStart_4279768 baseEnd_4279768 := by
    simpa [prefixWord, tailWord_4279768, baseEnd_4279768] using wordTrace_append hprefix tailTrace_4279768
  have hstable : (prefixWord ++ tailWord_4279768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279768).length < 2 ^ (prefixWord ++ tailWord_4279768).sum := by decide
  have hdescent : baseEnd_4279768 < baseStart_4279768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279775 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 1, 5, 2]
def baseStart_4279775 : Nat := 118140960795 + 4279775 * 2 ^ 59
def prefixEnd_4279775 : Nat := 4983230072969 + 3 ^ 40 * 4279775 * 2
def baseEnd_4279775 : Nat := 2197581668096098094330179

theorem tailTrace_4279775 : CollatzResearch.WordTrace tailWord_4279775 prefixEnd_4279775 2197581668096098094330179 := by
  unfold tailWord_4279775
  simp only [CollatzResearch.WordTrace]
  refine ⟨156096218070113577223008779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104064145380075718148672519 156096218070113577223008779)
  ·
    refine ⟨234144327105170365834513169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156096218070113577223008779 234144327105170365834513169)
    ·
      refine ⟨175608245328877774375884877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234144327105170365834513169 175608245328877774375884877)
      ·
        refine ⟨65853091998329165390956829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175608245328877774375884877 65853091998329165390956829)
        ·
          refine ⟨24694909499373437021608811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65853091998329165390956829 24694909499373437021608811)
          ·
            refine ⟨37042364249060155532413217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24694909499373437021608811 37042364249060155532413217)
            ·
              refine ⟨27781773186795116649309913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37042364249060155532413217 27781773186795116649309913)
              ·
                refine ⟨20836329890096337486982435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27781773186795116649309913 20836329890096337486982435)
                ·
                  refine ⟨31254494835144506230473653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20836329890096337486982435 31254494835144506230473653)
                  ·
                    refine ⟨2930108890794797459106905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31254494835144506230473653 2930108890794797459106905)
                    ·
                      refine ⟨2197581668096098094330179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2930108890794797459106905 2197581668096098094330179)
                      ·
                        rfl

theorem cell23_4279775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_4279775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279775 prefixEnd_4279775 := by exact prefixLift 4279775
  have htrace : WordTrace (prefixWord ++ tailWord_4279775) baseStart_4279775 baseEnd_4279775 := by
    simpa [prefixWord, tailWord_4279775, baseEnd_4279775] using wordTrace_append hprefix tailTrace_4279775
  have hstable : (prefixWord ++ tailWord_4279775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279775).length < 2 ^ (prefixWord ++ tailWord_4279775).sum := by decide
  have hdescent : baseEnd_4279775 < baseStart_4279775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279792 : List Nat := [2, 1, 1, 1, 3, 4, 3, 1, 2, 3, 2]
def baseStart_4279792 : Nat := 118140960795 + 4279792 * 2 ^ 59
def prefixEnd_4279792 : Nat := 4983230072969 + 3 ^ 40 * 4279792 * 2
def baseEnd_4279792 : Nat := 2197590397267224527817601

theorem tailTrace_4279792 : CollatzResearch.WordTrace tailWord_4279792 prefixEnd_4279792 2197590397267224527817601 := by
  unfold tailWord_4279792
  simp only [CollatzResearch.WordTrace]
  refine ⟨78048419055525994563188815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104064558740701326084251753 78048419055525994563188815)
  ·
    refine ⟨117072628583288991844783223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78048419055525994563188815 117072628583288991844783223)
    ·
      refine ⟨175608942874933487767174835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117072628583288991844783223 175608942874933487767174835)
      ·
        refine ⟨263413414312400231650762253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175608942874933487767174835 263413414312400231650762253)
        ·
          refine ⟨98780030367150086869035845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 263413414312400231650762253 98780030367150086869035845)
          ·
            refine ⟨18521255693840641287944221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98780030367150086869035845 18521255693840641287944221)
            ·
              refine ⟨6945470885190240482979083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18521255693840641287944221 6945470885190240482979083)
              ·
                refine ⟨10418206327785360724468625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6945470885190240482979083 10418206327785360724468625)
                ·
                  refine ⟨7813654745839020543351469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10418206327785360724468625 7813654745839020543351469)
                  ·
                    refine ⟨2930120529689632703756801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7813654745839020543351469 2930120529689632703756801)
                    ·
                      refine ⟨2197590397267224527817601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2930120529689632703756801 2197590397267224527817601)
                      ·
                        rfl

theorem cell23_4279792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 2, 3, 2].length) (baseStart_4279792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279792 prefixEnd_4279792 := by exact prefixLift 4279792
  have htrace : WordTrace (prefixWord ++ tailWord_4279792) baseStart_4279792 baseEnd_4279792 := by
    simpa [prefixWord, tailWord_4279792, baseEnd_4279792] using wordTrace_append hprefix tailTrace_4279792
  have hstable : (prefixWord ++ tailWord_4279792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279792).length < 2 ^ (prefixWord ++ tailWord_4279792).sum := by decide
  have hdescent : baseEnd_4279792 < baseStart_4279792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279806 : List Nat := [4, 2, 2, 3, 2, 1, 1, 2, 6]
def baseStart_4279806 : Nat := 118140960795 + 4279806 * 2 ^ 59
def prefixEnd_4279806 : Nat := 4983230072969 + 3 ^ 40 * 4279806 * 2
def baseEnd_4279806 : Nat := 244177509555154163671393

theorem tailTrace_4279806 : CollatzResearch.WordTrace tailWord_4279806 prefixEnd_4279806 244177509555154163671393 := by
  unfold tailWord_4279806
  simp only [CollatzResearch.WordTrace]
  refine ⟨19512168591625158689673409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104064899155334179678258181 19512168591625158689673409)
  ·
    refine ⟨14634126443718869017255057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19512168591625158689673409 14634126443718869017255057)
    ·
      refine ⟨10975594832789151762941293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14634126443718869017255057 10975594832789151762941293)
      ·
        refine ⟨4115848062295931911102985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10975594832789151762941293 4115848062295931911102985)
        ·
          refine ⟨3086886046721948933327239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4115848062295931911102985 3086886046721948933327239)
          ·
            refine ⟨4630329070082923399990859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3086886046721948933327239 4630329070082923399990859)
            ·
              refine ⟨6945493605124385099986289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4630329070082923399990859 6945493605124385099986289)
              ·
                refine ⟨5209120203843288824989717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6945493605124385099986289 5209120203843288824989717)
                ·
                  refine ⟨244177509555154163671393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5209120203843288824989717 244177509555154163671393)
                  ·
                    rfl

theorem cell23_4279806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_4279806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279806 prefixEnd_4279806 := by exact prefixLift 4279806
  have htrace : WordTrace (prefixWord ++ tailWord_4279806) baseStart_4279806 baseEnd_4279806 := by
    simpa [prefixWord, tailWord_4279806, baseEnd_4279806] using wordTrace_append hprefix tailTrace_4279806
  have hstable : (prefixWord ++ tailWord_4279806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279806).length < 2 ^ (prefixWord ++ tailWord_4279806).sum := by decide
  have hdescent : baseEnd_4279806 < baseStart_4279806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279832 : List Nat := [2, 1, 2, 3, 4, 2, 1, 1, 1, 6]
def baseStart_4279832 : Nat := 118140960795 + 4279832 * 2 ^ 59
def prefixEnd_4279832 : Nat := 4983230072969 + 3 ^ 40 * 4279832 * 2
def baseEnd_4279832 : Nat := 732536978831134790439139

theorem tailTrace_4279832 : CollatzResearch.WordTrace tailWord_4279832 prefixEnd_4279832 732536978831134790439139 := by
  unfold tailWord_4279832
  simp only [CollatzResearch.WordTrace]
  refine ⟨78049148515453537978916875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104065531353938050638555833 78049148515453537978916875)
  ·
    refine ⟨117073722773180306968375313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78049148515453537978916875 117073722773180306968375313)
    ·
      refine ⟨87805292079885230226281485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117073722773180306968375313 87805292079885230226281485)
      ·
        refine ⟨32926984529956961334855557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87805292079885230226281485 32926984529956961334855557)
        ·
          refine ⟨6173809599366930250285417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32926984529956961334855557 6173809599366930250285417)
          ·
            refine ⟨4630357199525197687714063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6173809599366930250285417 4630357199525197687714063)
            ·
              refine ⟨6945535799287796531571095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4630357199525197687714063 6945535799287796531571095)
              ·
                refine ⟨10418303698931694797356643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6945535799287796531571095 10418303698931694797356643)
                ·
                  refine ⟨15627455548397542196034965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10418303698931694797356643 15627455548397542196034965)
                  ·
                    refine ⟨732536978831134790439139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15627455548397542196034965 732536978831134790439139)
                    ·
                      rfl

theorem cell23_4279832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 1, 6].length) (baseStart_4279832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279832 prefixEnd_4279832 := by exact prefixLift 4279832
  have htrace : WordTrace (prefixWord ++ tailWord_4279832) baseStart_4279832 baseEnd_4279832 := by
    simpa [prefixWord, tailWord_4279832, baseEnd_4279832] using wordTrace_append hprefix tailTrace_4279832
  have hstable : (prefixWord ++ tailWord_4279832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279832).length < 2 ^ (prefixWord ++ tailWord_4279832).sum := by decide
  have hdescent : baseEnd_4279832 < baseStart_4279832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279842 : List Nat := [3, 3, 1, 1, 1, 1, 3, 4, 1, 2, 3]
def baseStart_4279842 : Nat := 118140960795 + 4279842 * 2 ^ 59
def prefixEnd_4279842 : Nat := 4983230072969 + 3 ^ 40 * 4279842 * 2
def baseEnd_4279842 : Nat := 2197616071299949332192371

theorem tailTrace_4279842 : CollatzResearch.WordTrace tailWord_4279842 prefixEnd_4279842 2197616071299949332192371 := by
  unfold tailWord_4279842
  simp only [CollatzResearch.WordTrace]
  refine ⟨39024665440217711916424445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104065774507247231777131853 39024665440217711916424445)
  ·
    refine ⟨14634249540081641968659167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39024665440217711916424445 14634249540081641968659167)
    ·
      refine ⟨21951374310122462952988751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14634249540081641968659167 21951374310122462952988751)
      ·
        refine ⟨32927061465183694429483127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21951374310122462952988751 32927061465183694429483127)
        ·
          refine ⟨49390592197775541644224691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32927061465183694429483127 49390592197775541644224691)
          ·
            refine ⟨74085888296663312466337037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49390592197775541644224691 74085888296663312466337037)
            ·
              refine ⟨27782208111248742174876389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74085888296663312466337037 27782208111248742174876389)
              ·
                refine ⟨5209164020859139157789323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27782208111248742174876389 5209164020859139157789323)
                ·
                  refine ⟨7813746031288708736683985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5209164020859139157789323 7813746031288708736683985)
                  ·
                    refine ⟨5860309523466531552512989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7813746031288708736683985 5860309523466531552512989)
                    ·
                      refine ⟨2197616071299949332192371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5860309523466531552512989 2197616071299949332192371)
                      ·
                        rfl

theorem cell23_4279842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_4279842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279842 prefixEnd_4279842 := by exact prefixLift 4279842
  have htrace : WordTrace (prefixWord ++ tailWord_4279842) baseStart_4279842 baseEnd_4279842 := by
    simpa [prefixWord, tailWord_4279842, baseEnd_4279842] using wordTrace_append hprefix tailTrace_4279842
  have hstable : (prefixWord ++ tailWord_4279842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279842).length < 2 ^ (prefixWord ++ tailWord_4279842).sum := by decide
  have hdescent : baseEnd_4279842 < baseStart_4279842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279858 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 1, 9]
def baseStart_4279858 : Nat := 118140960795 + 4279858 * 2 ^ 59
def prefixEnd_4279858 : Nat := 4983230072969 + 3 ^ 40 * 4279858 * 2
def baseEnd_4279858 : Nat := 732541428996807089864099

theorem tailTrace_4279858 : CollatzResearch.WordTrace tailWord_4279858 prefixEnd_4279858 732541428996807089864099 := by
  unfold tailWord_4279858
  simp only [CollatzResearch.WordTrace]
  refine ⟨39024811332203220599570057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104066163552541921598853485 39024811332203220599570057)
  ·
    refine ⟨29268608499152415449677543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39024811332203220599570057 29268608499152415449677543)
    ·
      refine ⟨43902912748728623174516315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29268608499152415449677543 43902912748728623174516315)
      ·
        refine ⟨65854369123092934761774473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43902912748728623174516315 65854369123092934761774473)
        ·
          refine ⟨49390776842319701071330855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65854369123092934761774473 49390776842319701071330855)
          ·
            refine ⟨74086165263479551606996283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49390776842319701071330855 74086165263479551606996283)
            ·
              refine ⟨111129247895219327410494425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74086165263479551606996283 111129247895219327410494425)
              ·
                refine ⟨83346935921414495557870819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111129247895219327410494425 83346935921414495557870819)
                ·
                  refine ⟨125020403882121743336806229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83346935921414495557870819 125020403882121743336806229)
                  ·
                    refine ⟨732541428996807089864099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 125020403882121743336806229 732541428996807089864099)
                    ·
                      rfl

theorem cell23_4279858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_4279858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279858 prefixEnd_4279858 := by exact prefixLift 4279858
  have htrace : WordTrace (prefixWord ++ tailWord_4279858) baseStart_4279858 baseEnd_4279858 := by
    simpa [prefixWord, tailWord_4279858, baseEnd_4279858] using wordTrace_append hprefix tailTrace_4279858
  have hstable : (prefixWord ++ tailWord_4279858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279858).length < 2 ^ (prefixWord ++ tailWord_4279858).sum := by decide
  have hdescent : baseEnd_4279858 < baseStart_4279858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279862 : List Nat := [5, 1, 2, 1, 3, 2, 9]
def baseStart_4279862 : Nat := 118140960795 + 4279862 * 2 ^ 59
def prefixEnd_4279862 : Nat := 4983230072969 + 3 ^ 40 * 4279862 * 2
def baseEnd_4279862 : Nat := 27131189393988138937559

theorem tailTrace_4279862 : CollatzResearch.WordTrace tailWord_4279862 prefixEnd_4279862 27131189393988138937559 := by
  unfold tailWord_4279862
  simp only [CollatzResearch.WordTrace]
  refine ⟨9756211951299899442589115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104066260813865594054283893 9756211951299899442589115)
  ·
    refine ⟨14634317926949849163883673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9756211951299899442589115 14634317926949849163883673)
    ·
      refine ⟨10975738445212386872912755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14634317926949849163883673 10975738445212386872912755)
      ·
        refine ⟨16463607667818580309369133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10975738445212386872912755 16463607667818580309369133)
        ·
          refine ⟨6173852875431967616013425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16463607667818580309369133 6173852875431967616013425)
          ·
            refine ⟨4630389656573975712010069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6173852875431967616013425 4630389656573975712010069)
            ·
              refine ⟨27131189393988138937559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4630389656573975712010069 27131189393988138937559)
              ·
                rfl

theorem cell23_4279862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 9].length) (baseStart_4279862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279862 prefixEnd_4279862 := by exact prefixLift 4279862
  have htrace : WordTrace (prefixWord ++ tailWord_4279862) baseStart_4279862 baseEnd_4279862 := by
    simpa [prefixWord, tailWord_4279862, baseEnd_4279862] using wordTrace_append hprefix tailTrace_4279862
  have hstable : (prefixWord ++ tailWord_4279862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279862).length < 2 ^ (prefixWord ++ tailWord_4279862).sum := by decide
  have hdescent : baseEnd_4279862 < baseStart_4279862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279872 : List Nat := [2, 1, 1, 2, 2, 2, 1, 6, 2, 1, 3]
def baseStart_4279872 : Nat := 118140960795 + 4279872 * 2 ^ 59
def prefixEnd_4279872 : Nat := 4983230072969 + 3 ^ 40 * 4279872 * 2
def baseEnd_4279872 : Nat := 2197631475719584214817233

theorem tailTrace_4279872 : CollatzResearch.WordTrace tailWord_4279872 prefixEnd_4279872 2197631475719584214817233 := by
  unfold tailWord_4279872
  simp only [CollatzResearch.WordTrace]
  refine ⟨78049877975381081394644935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104066503967174775192859913 78049877975381081394644935)
  ·
    refine ⟨117074816963071622091967403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78049877975381081394644935 117074816963071622091967403)
    ·
      refine ⟨175612225444607433137951105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117074816963071622091967403 175612225444607433137951105)
      ·
        refine ⟨131709169083455574853463329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175612225444607433137951105 131709169083455574853463329)
        ·
          refine ⟨98781876812591681140097497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131709169083455574853463329 98781876812591681140097497)
          ·
            refine ⟨74086407609443760855073123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98781876812591681140097497 74086407609443760855073123)
            ·
              refine ⟨111129611414165641282609685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74086407609443760855073123 111129611414165641282609685)
              ·
                refine ⟨5209200535039014435122329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 111129611414165641282609685 5209200535039014435122329)
                ·
                  refine ⟨3906900401279260826341747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5209200535039014435122329 3906900401279260826341747)
                  ·
                    refine ⟨5860350601918891239512621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3906900401279260826341747 5860350601918891239512621)
                    ·
                      refine ⟨2197631475719584214817233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5860350601918891239512621 2197631475719584214817233)
                      ·
                        rfl

theorem cell23_4279872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 2, 1, 3].length) (baseStart_4279872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279872 prefixEnd_4279872 := by exact prefixLift 4279872
  have htrace : WordTrace (prefixWord ++ tailWord_4279872) baseStart_4279872 baseEnd_4279872 := by
    simpa [prefixWord, tailWord_4279872, baseEnd_4279872] using wordTrace_append hprefix tailTrace_4279872
  have hstable : (prefixWord ++ tailWord_4279872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279872).length < 2 ^ (prefixWord ++ tailWord_4279872).sum := by decide
  have hdescent : baseEnd_4279872 < baseStart_4279872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279873 : List Nat := [1, 2, 5, 1, 1, 1, 5, 2, 1, 2, 2]
def baseStart_4279873 : Nat := 118140960795 + 4279873 * 2 ^ 59
def prefixEnd_4279873 : Nat := 4983230072969 + 3 ^ 40 * 4279873 * 2
def baseEnd_4279873 : Nat := 2197631989200238710904729

theorem tailTrace_4279873 : CollatzResearch.WordTrace tailWord_4279873 prefixEnd_4279873 2197631989200238710904729 := by
  unfold tailWord_4279873
  simp only [CollatzResearch.WordTrace]
  refine ⟨156099792423758539960076273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104066528282505693306717515 156099792423758539960076273)
  ·
    refine ⟨117074844317818904970057205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156099792423758539960076273 117074844317818904970057205)
    ·
      refine ⟨10975766654795522340942863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117074844317818904970057205 10975766654795522340942863)
      ·
        refine ⟨16463649982193283511414295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10975766654795522340942863 16463649982193283511414295)
        ·
          refine ⟨24695474973289925267121443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16463649982193283511414295 24695474973289925267121443)
          ·
            refine ⟨37043212459934887900682165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24695474973289925267121443 37043212459934887900682165)
            ·
              refine ⟨3472801168118895740688953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37043212459934887900682165 3472801168118895740688953)
              ·
                refine ⟨2604600876089171805516715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3472801168118895740688953 2604600876089171805516715)
                ·
                  refine ⟨3906901314133757708275073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2604600876089171805516715 3906901314133757708275073)
                  ·
                    refine ⟨2930175985600318281206305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3906901314133757708275073 2930175985600318281206305)
                    ·
                      refine ⟨2197631989200238710904729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2930175985600318281206305 2197631989200238710904729)
                      ·
                        rfl

theorem cell23_4279873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_4279873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279873 prefixEnd_4279873 := by exact prefixLift 4279873
  have htrace : WordTrace (prefixWord ++ tailWord_4279873) baseStart_4279873 baseEnd_4279873 := by
    simpa [prefixWord, tailWord_4279873, baseEnd_4279873] using wordTrace_append hprefix tailTrace_4279873
  have hstable : (prefixWord ++ tailWord_4279873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279873).length < 2 ^ (prefixWord ++ tailWord_4279873).sum := by decide
  have hdescent : baseEnd_4279873 < baseStart_4279873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279882 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 3, 3, 2]
def baseStart_4279882 : Nat := 118140960795 + 4279882 * 2 ^ 59
def prefixEnd_4279882 : Nat := 4983230072969 + 3 ^ 40 * 4279882 * 2
def baseEnd_4279882 : Nat := 2197636610526129175692187

theorem tailTrace_4279882 : CollatzResearch.WordTrace tailWord_4279882 prefixEnd_4279882 2197636610526129175692187 := by
  unfold tailWord_4279882
  simp only [CollatzResearch.WordTrace]
  refine ⟨39025030170181483624288475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104066747120483956331435933 39025030170181483624288475)
  ·
    refine ⟨58537545255272225436432713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39025030170181483624288475 58537545255272225436432713)
    ·
      refine ⟨43903158941454169077324535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58537545255272225436432713 43903158941454169077324535)
      ·
        refine ⟨65854738412181253615986803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43903158941454169077324535 65854738412181253615986803)
        ·
          refine ⟨98782107618271880423980205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65854738412181253615986803 98782107618271880423980205)
          ·
            refine ⟨37043290356851955158992577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98782107618271880423980205 37043290356851955158992577)
            ·
              refine ⟨27782467767638966369244433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37043290356851955158992577 27782467767638966369244433)
              ·
                refine ⟨20836850825729224776933325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27782467767638966369244433 20836850825729224776933325)
                ·
                  refine ⟨7813819059648459291349997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20836850825729224776933325 7813819059648459291349997)
                  ·
                    refine ⟨2930182147368172234256249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7813819059648459291349997 2930182147368172234256249)
                    ·
                      refine ⟨2197636610526129175692187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2930182147368172234256249 2197636610526129175692187)
                      ·
                        rfl

theorem cell23_4279882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_4279882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279882 prefixEnd_4279882 := by exact prefixLift 4279882
  have htrace : WordTrace (prefixWord ++ tailWord_4279882) baseStart_4279882 baseEnd_4279882 := by
    simpa [prefixWord, tailWord_4279882, baseEnd_4279882] using wordTrace_append hprefix tailTrace_4279882
  have hstable : (prefixWord ++ tailWord_4279882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279882).length < 2 ^ (prefixWord ++ tailWord_4279882).sum := by decide
  have hdescent : baseEnd_4279882 < baseStart_4279882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279888 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 1, 8]
def baseStart_4279888 : Nat := 118140960795 + 4279888 * 2 ^ 59
def prefixEnd_4279888 : Nat := 4983230072969 + 3 ^ 40 * 4279888 * 2
def baseEnd_4279888 : Nat := 732546563803352050739053

theorem tailTrace_4279888 : CollatzResearch.WordTrace tailWord_4279888 prefixEnd_4279888 732546563803352050739053 := by
  unfold tailWord_4279888
  simp only [CollatzResearch.WordTrace]
  refine ⟨78050169759352098760936159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104066893012469465014581545 78050169759352098760936159)
  ·
    refine ⟨117075254639028148141404239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78050169759352098760936159 117075254639028148141404239)
    ·
      refine ⟨175612881958542222212106359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117075254639028148141404239 175612881958542222212106359)
      ·
        refine ⟨263419322937813333318159539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175612881958542222212106359 263419322937813333318159539)
        ·
          refine ⟨395128984406719999977239309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263419322937813333318159539 395128984406719999977239309)
          ·
            refine ⟨148173369152519999991464741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 395128984406719999977239309 148173369152519999991464741)
            ·
              refine ⟨27782506716097499998399639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148173369152519999991464741 27782506716097499998399639)
              ·
                refine ⟨41673760074146249997599459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27782506716097499998399639 41673760074146249997599459)
                ·
                  refine ⟨62510640111219374996399189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41673760074146249997599459 62510640111219374996399189)
                  ·
                    refine ⟨732546563803352050739053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62510640111219374996399189 732546563803352050739053)
                    ·
                      rfl

theorem cell23_4279888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 1, 8].length) (baseStart_4279888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279888 prefixEnd_4279888 := by exact prefixLift 4279888
  have htrace : WordTrace (prefixWord ++ tailWord_4279888) baseStart_4279888 baseEnd_4279888 := by
    simpa [prefixWord, tailWord_4279888, baseEnd_4279888] using wordTrace_append hprefix tailTrace_4279888
  have hstable : (prefixWord ++ tailWord_4279888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279888).length < 2 ^ (prefixWord ++ tailWord_4279888).sum := by decide
  have hdescent : baseEnd_4279888 < baseStart_4279888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279945 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 1, 5, 3]
def baseStart_4279945 : Nat := 118140960795 + 4279945 * 2 ^ 59
def prefixEnd_4279945 : Nat := 4983230072969 + 3 ^ 40 * 4279945 * 2
def baseEnd_4279945 : Nat := 2197668959807362429204397

theorem tailTrace_4279945 : CollatzResearch.WordTrace tailWord_4279945 prefixEnd_4279945 2197668959807362429204397 := by
  unfold tailWord_4279945
  simp only [CollatzResearch.WordTrace]
  refine ⟨156102418479497696256697289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104068278986331797504464859 156102418479497696256697289)
  ·
    refine ⟨117076813859623272192522967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156102418479497696256697289 117076813859623272192522967)
    ·
      refine ⟨175615220789434908288784451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117076813859623272192522967 175615220789434908288784451)
      ·
        refine ⟨263422831184152362433176677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175615220789434908288784451 263422831184152362433176677)
        ·
          refine ⟨49391780847028567956220627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 263422831184152362433176677 49391780847028567956220627)
          ·
            refine ⟨74087671270542851934330941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49391780847028567956220627 74087671270542851934330941)
            ·
              refine ⟨27782876726453569475374103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74087671270542851934330941 27782876726453569475374103)
              ·
                refine ⟨41674315089680354213061155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27782876726453569475374103 41674315089680354213061155)
                ·
                  refine ⟨62511472634520531319591733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41674315089680354213061155 62511472634520531319591733)
                  ·
                    refine ⟨5860450559486299811211725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62511472634520531319591733 5860450559486299811211725)
                    ·
                      refine ⟨2197668959807362429204397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5860450559486299811211725 2197668959807362429204397)
                      ·
                        rfl

theorem cell23_4279945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 5, 3].length) (baseStart_4279945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279945 prefixEnd_4279945 := by exact prefixLift 4279945
  have htrace : WordTrace (prefixWord ++ tailWord_4279945) baseStart_4279945 baseEnd_4279945 := by
    simpa [prefixWord, tailWord_4279945, baseEnd_4279945] using wordTrace_append hprefix tailTrace_4279945
  have hstable : (prefixWord ++ tailWord_4279945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279945).length < 2 ^ (prefixWord ++ tailWord_4279945).sum := by decide
  have hdescent : baseEnd_4279945 < baseStart_4279945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279946 : List Nat := [3, 1, 2, 3, 2, 1, 2, 3, 2, 2, 2]
def baseStart_4279946 : Nat := 118140960795 + 4279946 * 2 ^ 59
def prefixEnd_4279946 : Nat := 4983230072969 + 3 ^ 40 * 4279946 * 2
def baseEnd_4279946 : Nat := 2197669473288016925291893

theorem tailTrace_4279946 : CollatzResearch.WordTrace tailWord_4279946 prefixEnd_4279946 2197669473288016925291893 := by
  unfold tailWord_4279946
  simp only [CollatzResearch.WordTrace]
  refine ⟨39025613738123518356870923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104068303301662715618322461 39025613738123518356870923)
  ·
    refine ⟨58538420607185277535306385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39025613738123518356870923 58538420607185277535306385)
    ·
      refine ⟨43903815455388958151479789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58538420607185277535306385 43903815455388958151479789)
      ·
        refine ⟨16463930795770859306804921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43903815455388958151479789 16463930795770859306804921)
        ·
          refine ⟨12347948096828144480103691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16463930795770859306804921 12347948096828144480103691)
          ·
            refine ⟨18521922145242216720155537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12347948096828144480103691 18521922145242216720155537)
            ·
              refine ⟨13891441608931662540116653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18521922145242216720155537 13891441608931662540116653)
              ·
                refine ⟨5209290603349373452543745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13891441608931662540116653 5209290603349373452543745)
                ·
                  refine ⟨3906967952512030089407809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5209290603349373452543745 3906967952512030089407809)
                  ·
                    refine ⟨2930225964384022567055857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3906967952512030089407809 2930225964384022567055857)
                    ·
                      refine ⟨2197669473288016925291893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2930225964384022567055857 2197669473288016925291893)
                      ·
                        rfl

theorem cell23_4279946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_4279946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279946 prefixEnd_4279946 := by exact prefixLift 4279946
  have htrace : WordTrace (prefixWord ++ tailWord_4279946) baseStart_4279946 baseEnd_4279946 := by
    simpa [prefixWord, tailWord_4279946, baseEnd_4279946] using wordTrace_append hprefix tailTrace_4279946
  have hstable : (prefixWord ++ tailWord_4279946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279946).length < 2 ^ (prefixWord ++ tailWord_4279946).sum := by decide
  have hdescent : baseEnd_4279946 < baseStart_4279946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4279969 : List Nat := [1, 2, 3, 3, 2, 2, 2, 3, 5]
def baseStart_4279969 : Nat := 118140960795 + 4279969 * 2 ^ 59
def prefixEnd_4279969 : Nat := 4983230072969 + 3 ^ 40 * 4279969 * 2
def baseEnd_4279969 : Nat := 244186809260341148367143

theorem tailTrace_4279969 : CollatzResearch.WordTrace tailWord_4279969 prefixEnd_4279969 244186809260341148367143 := by
  unfold tailWord_4279969
  simp only [CollatzResearch.WordTrace]
  refine ⟨156103293831410748355570961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104068862554273832237047307 156103293831410748355570961)
  ·
    refine ⟨117077470373558061266678221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156103293831410748355570961 117077470373558061266678221)
    ·
      refine ⟨43904051390084272975004333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117077470373558061266678221 43904051390084272975004333)
      ·
        refine ⟨16464019271281602365626625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43904051390084272975004333 16464019271281602365626625)
        ·
          refine ⟨12348014453461201774219969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16464019271281602365626625 12348014453461201774219969)
          ·
            refine ⟨9261010840095901330664977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12348014453461201774219969 9261010840095901330664977)
            ·
              refine ⟨6945758130071925997998733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9261010840095901330664977 6945758130071925997998733)
              ·
                refine ⟨2604659298776972249249525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6945758130071925997998733 2604659298776972249249525)
                ·
                  refine ⟨244186809260341148367143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2604659298776972249249525 244186809260341148367143)
                  ·
                    rfl

theorem cell23_4279969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 5].length) (baseStart_4279969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4279969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4279969 prefixEnd_4279969 := by exact prefixLift 4279969
  have htrace : WordTrace (prefixWord ++ tailWord_4279969) baseStart_4279969 baseEnd_4279969 := by
    simpa [prefixWord, tailWord_4279969, baseEnd_4279969] using wordTrace_append hprefix tailTrace_4279969
  have hstable : (prefixWord ++ tailWord_4279969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4279969).length < 2 ^ (prefixWord ++ tailWord_4279969).sum := by decide
  have hdescent : baseEnd_4279969 < baseStart_4279969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4279969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280025 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 8]
def baseStart_4280025 : Nat := 118140960795 + 4280025 * 2 ^ 59
def prefixEnd_4280025 : Nat := 4983230072969 + 3 ^ 40 * 4280025 * 2
def baseEnd_4280025 : Nat := 244190004251080235133781

theorem tailTrace_4280025 : CollatzResearch.WordTrace tailWord_4280025 prefixEnd_4280025 244190004251080235133781 := by
  unfold tailWord_4280025
  simp only [CollatzResearch.WordTrace]
  refine ⟨156105336319207869919609529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104070224212805246613073019 156105336319207869919609529)
  ·
    refine ⟨117079002239405902439707147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156105336319207869919609529 117079002239405902439707147)
    ·
      refine ⟨175618503359108853659560721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117079002239405902439707147 175618503359108853659560721)
      ·
        refine ⟨131713877519331640244670541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175618503359108853659560721 131713877519331640244670541)
        ·
          refine ⟨49392704069749365091751453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131713877519331640244670541 49392704069749365091751453)
          ·
            refine ⟨18522264026156011909406795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49392704069749365091751453 18522264026156011909406795)
            ·
              refine ⟨27783396039234017864110193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18522264026156011909406795 27783396039234017864110193)
              ·
                refine ⟨20837547029425513398082645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27783396039234017864110193 20837547029425513398082645)
                ·
                  refine ⟨244190004251080235133781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20837547029425513398082645 244190004251080235133781)
                  ·
                    rfl

theorem cell23_4280025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 8].length) (baseStart_4280025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280025 prefixEnd_4280025 := by exact prefixLift 4280025
  have htrace : WordTrace (prefixWord ++ tailWord_4280025) baseStart_4280025 baseEnd_4280025 := by
    simpa [prefixWord, tailWord_4280025, baseEnd_4280025] using wordTrace_append hprefix tailTrace_4280025
  have hstable : (prefixWord ++ tailWord_4280025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280025).length < 2 ^ (prefixWord ++ tailWord_4280025).sum := by decide
  have hdescent : baseEnd_4280025 < baseStart_4280025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280072 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 3, 5]
def baseStart_4280072 : Nat := 118140960795 + 4280072 * 2 ^ 59
def prefixEnd_4280072 : Nat := 4983230072969 + 3 ^ 40 * 4280072 * 2
def baseEnd_4280072 : Nat := 732578057283494477438771

theorem tailTrace_4280072 : CollatzResearch.WordTrace tailWord_4280072 prefixEnd_4280072 732578057283494477438771 := by
  unfold tailWord_4280072
  simp only [CollatzResearch.WordTrace]
  refine ⟨78053525275018798473285235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104071367033358397964380313 78053525275018798473285235)
  ·
    refine ⟨117080287912528197709927853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78053525275018798473285235 117080287912528197709927853)
    ·
      refine ⟨43905107967198074141222945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117080287912528197709927853 43905107967198074141222945)
      ·
        refine ⟨32928830975398555605917209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43905107967198074141222945 32928830975398555605917209)
        ·
          refine ⟨24696623231548916704437907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32928830975398555605917209 24696623231548916704437907)
          ·
            refine ⟨37044934847323375056656861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24696623231548916704437907 37044934847323375056656861)
            ·
              refine ⟨13891850567746265646246323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37044934847323375056656861 13891850567746265646246323)
              ·
                refine ⟨20837775851619398469369485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13891850567746265646246323 20837775851619398469369485)
                ·
                  refine ⟨7814165944357274426013557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20837775851619398469369485 7814165944357274426013557)
                  ·
                    refine ⟨732578057283494477438771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7814165944357274426013557 732578057283494477438771)
                    ·
                      rfl

theorem cell23_4280072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_4280072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280072 prefixEnd_4280072 := by exact prefixLift 4280072
  have htrace : WordTrace (prefixWord ++ tailWord_4280072) baseStart_4280072 baseEnd_4280072 := by
    simpa [prefixWord, tailWord_4280072, baseEnd_4280072] using wordTrace_append hprefix tailTrace_4280072
  have hstable : (prefixWord ++ tailWord_4280072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280072).length < 2 ^ (prefixWord ++ tailWord_4280072).sum := by decide
  have hdescent : baseEnd_4280072 < baseStart_4280072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280146 : List Nat := [3, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3]
def baseStart_4280146 : Nat := 118140960795 + 4280146 * 2 ^ 59
def prefixEnd_4280146 : Nat := 4983230072969 + 3 ^ 40 * 4280146 * 2
def baseEnd_4280146 : Nat := 2197772169418916142790973

theorem tailTrace_4280146 : CollatzResearch.WordTrace tailWord_4280146 prefixEnd_4280146 2197772169418916142790973 := by
  unfold tailWord_4280146
  simp only [CollatzResearch.WordTrace]
  refine ⟨39027437387942376896191073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104073166367846338389842861 39027437387942376896191073)
  ·
    refine ⟨29270578040956782672143305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39027437387942376896191073 29270578040956782672143305)
    ·
      refine ⟨21952933530717587004107479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29270578040956782672143305 21952933530717587004107479)
      ·
        refine ⟨32929400296076380506161219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21952933530717587004107479 32929400296076380506161219)
        ·
          refine ⟨49394100444114570759241829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32929400296076380506161219 49394100444114570759241829)
          ·
            refine ⟨9261393833271482017357843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49394100444114570759241829 9261393833271482017357843)
            ·
              refine ⟨13892090749907223026036765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9261393833271482017357843 13892090749907223026036765)
              ·
                refine ⟨5209534031215208634763787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13892090749907223026036765 5209534031215208634763787)
                ·
                  refine ⟨7814301046822812952145681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5209534031215208634763787 7814301046822812952145681)
                  ·
                    refine ⟨5860725785117109714109261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7814301046822812952145681 5860725785117109714109261)
                    ·
                      refine ⟨2197772169418916142790973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5860725785117109714109261 2197772169418916142790973)
                      ·
                        rfl

theorem cell23_4280146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_4280146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280146 prefixEnd_4280146 := by exact prefixLift 4280146
  have htrace : WordTrace (prefixWord ++ tailWord_4280146) baseStart_4280146 baseEnd_4280146 := by
    simpa [prefixWord, tailWord_4280146, baseEnd_4280146] using wordTrace_append hprefix tailTrace_4280146
  have hstable : (prefixWord ++ tailWord_4280146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280146).length < 2 ^ (prefixWord ++ tailWord_4280146).sum := by decide
  have hdescent : baseEnd_4280146 < baseStart_4280146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280169 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 5, 3, 2]
def baseStart_4280169 : Nat := 118140960795 + 4280169 * 2 ^ 59
def prefixEnd_4280169 : Nat := 4983230072969 + 3 ^ 40 * 4280169 * 2
def baseEnd_4280169 : Nat := 2197783979473969552803367

theorem tailTrace_4280169 : CollatzResearch.WordTrace tailWord_4280169 prefixEnd_4280169 2197783979473969552803367 := by
  unfold tailWord_4280169
  simp only [CollatzResearch.WordTrace]
  refine ⟨156110588430686182512851561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104073725620457455008567707 156110588430686182512851561)
  ·
    refine ⟨117082941323014636884638671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156110588430686182512851561 117082941323014636884638671)
    ·
      refine ⟨175624411984521955326958007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117082941323014636884638671 175624411984521955326958007)
      ·
        refine ⟨263436617976782932990437011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175624411984521955326958007 263436617976782932990437011)
        ·
          refine ⟨395154926965174399485655517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263436617976782932990437011 395154926965174399485655517)
          ·
            refine ⟨148183097611940399807120819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 395154926965174399485655517 148183097611940399807120819)
            ·
              refine ⟨222274646417910599710681229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148183097611940399807120819 222274646417910599710681229)
              ·
                refine ⟨83352992406716474891505461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222274646417910599710681229 83352992406716474891505461)
                ·
                  refine ⟨7814343038129669521078637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83352992406716474891505461 7814343038129669521078637)
                  ·
                    refine ⟨2930378639298626070404489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7814343038129669521078637 2930378639298626070404489)
                    ·
                      refine ⟨2197783979473969552803367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2930378639298626070404489 2197783979473969552803367)
                      ·
                        rfl

theorem cell23_4280169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 3, 2].length) (baseStart_4280169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280169 prefixEnd_4280169 := by exact prefixLift 4280169
  have htrace : WordTrace (prefixWord ++ tailWord_4280169) baseStart_4280169 baseEnd_4280169 := by
    simpa [prefixWord, tailWord_4280169, baseEnd_4280169] using wordTrace_append hprefix tailTrace_4280169
  have hstable : (prefixWord ++ tailWord_4280169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280169).length < 2 ^ (prefixWord ++ tailWord_4280169).sum := by decide
  have hdescent : baseEnd_4280169 < baseStart_4280169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280170 : List Nat := [3, 1, 3, 4, 1, 1, 3, 1, 2, 4]
def baseStart_4280170 : Nat := 118140960795 + 4280170 * 2 ^ 59
def prefixEnd_4280170 : Nat := 4983230072969 + 3 ^ 40 * 4280170 * 2
def baseEnd_4280170 : Nat := 732594830984874682963621

theorem tailTrace_4280170 : CollatzResearch.WordTrace tailWord_4280170 prefixEnd_4280170 732594830984874682963621 := by
  unfold tailWord_4280170
  simp only [CollatzResearch.WordTrace]
  refine ⟨39027656225920639920909491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104073749935788373122425309 39027656225920639920909491)
  ·
    refine ⟨58541484338880959881364237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39027656225920639920909491 58541484338880959881364237)
    ·
      refine ⟨21953056627080359955511589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58541484338880959881364237 21953056627080359955511589)
      ·
        refine ⟨4116198117577567491658423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21953056627080359955511589 4116198117577567491658423)
        ·
          refine ⟨6174297176366351237487635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4116198117577567491658423 6174297176366351237487635)
          ·
            refine ⟨9261445764549526856231453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6174297176366351237487635 9261445764549526856231453)
            ·
              refine ⟨3473042161706072571086795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9261445764549526856231453 3473042161706072571086795)
              ·
                refine ⟨5209563242559108856630193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3473042161706072571086795 5209563242559108856630193)
                ·
                  refine ⟨3907172431919331642472645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5209563242559108856630193 3907172431919331642472645)
                  ·
                    refine ⟨732594830984874682963621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3907172431919331642472645 732594830984874682963621)
                    ·
                      rfl

theorem cell23_4280170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_4280170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280170 prefixEnd_4280170 := by exact prefixLift 4280170
  have htrace : WordTrace (prefixWord ++ tailWord_4280170) baseStart_4280170 baseEnd_4280170 := by
    simpa [prefixWord, tailWord_4280170, baseEnd_4280170] using wordTrace_append hprefix tailTrace_4280170
  have hstable : (prefixWord ++ tailWord_4280170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280170).length < 2 ^ (prefixWord ++ tailWord_4280170).sum := by decide
  have hdescent : baseEnd_4280170 < baseStart_4280170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280186 : List Nat := [3, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2]
def baseStart_4280186 : Nat := 118140960795 + 4280186 * 2 ^ 59
def prefixEnd_4280186 : Nat := 4983230072969 + 3 ^ 40 * 4280186 * 2
def baseEnd_4280186 : Nat := 2197792708645095986290789

theorem tailTrace_4280186 : CollatzResearch.WordTrace tailWord_4280186 prefixEnd_4280186 2197792708645095986290789 := by
  unfold tailWord_4280186
  simp only [CollatzResearch.WordTrace]
  refine ⟨39027802117906148604055103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104074138981083062944146941 39027802117906148604055103)
  ·
    refine ⟨58541703176859222906082655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39027802117906148604055103 58541703176859222906082655)
    ·
      refine ⟨87812554765288834359123983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58541703176859222906082655 87812554765288834359123983)
      ·
        refine ⟨131718832147933251538685975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87812554765288834359123983 131718832147933251538685975)
        ·
          refine ⟨197578248221899877308028963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131718832147933251538685975 197578248221899877308028963)
          ·
            refine ⟨296367372332849815962043445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197578248221899877308028963 296367372332849815962043445)
            ·
              refine ⟨27784441156204670246441573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 296367372332849815962043445 27784441156204670246441573)
              ·
                refine ⟨5209582716788375671207795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27784441156204670246441573 5209582716788375671207795)
                ·
                  refine ⟨7814374075182563506811693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5209582716788375671207795 7814374075182563506811693)
                  ·
                    refine ⟨2930390278193461315054385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7814374075182563506811693 2930390278193461315054385)
                    ·
                      refine ⟨2197792708645095986290789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2930390278193461315054385 2197792708645095986290789)
                      ·
                        rfl

theorem cell23_4280186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2].length) (baseStart_4280186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280186 prefixEnd_4280186 := by exact prefixLift 4280186
  have htrace : WordTrace (prefixWord ++ tailWord_4280186) baseStart_4280186 baseEnd_4280186 := by
    simpa [prefixWord, tailWord_4280186, baseEnd_4280186] using wordTrace_append hprefix tailTrace_4280186
  have hstable : (prefixWord ++ tailWord_4280186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280186).length < 2 ^ (prefixWord ++ tailWord_4280186).sum := by decide
  have hdescent : baseEnd_4280186 < baseStart_4280186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280242 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_4280242 : Nat := 118140960795 + 4280242 * 2 ^ 59
def prefixEnd_4280242 : Nat := 4983230072969 + 3 ^ 40 * 4280242 * 2
def baseEnd_4280242 : Nat := 2197821463561747767190531

theorem tailTrace_4280242 : CollatzResearch.WordTrace tailWord_4280242 prefixEnd_4280242 2197821463561747767190531 := by
  unfold tailWord_4280242
  simp only [CollatzResearch.WordTrace]
  refine ⟨39028312739855428995064745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104075500639614477320172653 39028312739855428995064745)
  ·
    refine ⟨29271234554891571746298559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39028312739855428995064745 29271234554891571746298559)
    ·
      refine ⟨43906851832337357619447839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29271234554891571746298559 43906851832337357619447839)
      ·
        refine ⟨65860277748506036429171759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43906851832337357619447839 65860277748506036429171759)
        ·
          refine ⟨98790416622759054643757639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65860277748506036429171759 98790416622759054643757639)
          ·
            refine ⟨148185624934138581965636459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98790416622759054643757639 148185624934138581965636459)
            ·
              refine ⟨222278437401207872948454689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148185624934138581965636459 222278437401207872948454689)
              ·
                refine ⟨166708828050905904711341017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222278437401207872948454689 166708828050905904711341017)
                ·
                  refine ⟨125031621038179428533505763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166708828050905904711341017 125031621038179428533505763)
                  ·
                    refine ⟨187547431557269142800258645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 125031621038179428533505763 187547431557269142800258645)
                    ·
                      refine ⟨2197821463561747767190531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 187547431557269142800258645 2197821463561747767190531)
                      ·
                        rfl

theorem cell23_4280242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_4280242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280242 prefixEnd_4280242 := by exact prefixLift 4280242
  have htrace : WordTrace (prefixWord ++ tailWord_4280242) baseStart_4280242 baseEnd_4280242 := by
    simpa [prefixWord, tailWord_4280242, baseEnd_4280242] using wordTrace_append hprefix tailTrace_4280242
  have hstable : (prefixWord ++ tailWord_4280242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280242).length < 2 ^ (prefixWord ++ tailWord_4280242).sum := by decide
  have hdescent : baseEnd_4280242 < baseStart_4280242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280259 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 3, 7, 2]
def baseStart_4280259 : Nat := 118140960795 + 4280259 * 2 ^ 59
def prefixEnd_4280259 : Nat := 4983230072969 + 3 ^ 40 * 4280259 * 2
def baseEnd_4280259 : Nat := 2197830192732874200677953

theorem tailTrace_4280259 : CollatzResearch.WordTrace tailWord_4280259 prefixEnd_4280259 2197830192732874200677953 := by
  unfold tailWord_4280259
  simp only [CollatzResearch.WordTrace]
  refine ⟨156113871000360127883627831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104075914000240085255751887 156113871000360127883627831)
  ·
    refine ⟨234170806500540191825441747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156113871000360127883627831 234170806500540191825441747)
    ·
      refine ⟨351256209750810287738162621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234170806500540191825441747 351256209750810287738162621)
      ·
        refine ⟨131721078656553857901810983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 351256209750810287738162621 131721078656553857901810983)
        ·
          refine ⟨197581617984830786852716475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131721078656553857901810983 197581617984830786852716475)
          ·
            refine ⟨296372426977246180279074713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197581617984830786852716475 296372426977246180279074713)
            ·
              refine ⟨222279320232934635209306035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296372426977246180279074713 222279320232934635209306035)
              ·
                refine ⟨333418980349401952813959053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222279320232934635209306035 333418980349401952813959053)
                ·
                  refine ⟨125032117631025732305234645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 333418980349401952813959053 125032117631025732305234645)
                  ·
                    refine ⟨2930440256977165600903937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 125032117631025732305234645 2930440256977165600903937)
                    ·
                      refine ⟨2197830192732874200677953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2930440256977165600903937 2197830192732874200677953)
                      ·
                        rfl

theorem cell23_4280259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 7, 2].length) (baseStart_4280259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280259 prefixEnd_4280259 := by exact prefixLift 4280259
  have htrace : WordTrace (prefixWord ++ tailWord_4280259) baseStart_4280259 baseEnd_4280259 := by
    simpa [prefixWord, tailWord_4280259, baseEnd_4280259] using wordTrace_append hprefix tailTrace_4280259
  have hstable : (prefixWord ++ tailWord_4280259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280259).length < 2 ^ (prefixWord ++ tailWord_4280259).sum := by decide
  have hdescent : baseEnd_4280259 < baseStart_4280259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280276 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 1, 7, 2]
def baseStart_4280276 : Nat := 118140960795 + 4280276 * 2 ^ 59
def prefixEnd_4280276 : Nat := 4983230072969 + 3 ^ 40 * 4280276 * 2
def baseEnd_4280276 : Nat := 2197838921904000634165375

theorem tailTrace_4280276 : CollatzResearch.WordTrace tailWord_4280276 prefixEnd_4280276 2197838921904000634165375 := by
  unfold tailWord_4280276
  simp only [CollatzResearch.WordTrace]
  refine ⟨78057245520649269893498341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104076327360865693191331121 78057245520649269893498341)
  ·
    refine ⟨14635733535121738105030939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78057245520649269893498341 14635733535121738105030939)
    ·
      refine ⟨21953600302682607157546409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14635733535121738105030939 21953600302682607157546409)
      ·
        refine ⟨16465200227011955368159807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21953600302682607157546409 16465200227011955368159807)
        ·
          refine ⟨24697800340517933052239711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16465200227011955368159807 24697800340517933052239711)
          ·
            refine ⟨37046700510776899578359567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24697800340517933052239711 37046700510776899578359567)
            ·
              refine ⟨55570050766165349367539351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37046700510776899578359567 55570050766165349367539351)
              ·
                refine ⟨83355076149248024051309027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55570050766165349367539351 83355076149248024051309027)
                ·
                  refine ⟨125032614223872036076963541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83355076149248024051309027 125032614223872036076963541)
                  ·
                    refine ⟨2930451895872000845553833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 125032614223872036076963541 2930451895872000845553833)
                    ·
                      refine ⟨2197838921904000634165375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2930451895872000845553833 2197838921904000634165375)
                      ·
                        rfl

theorem cell23_4280276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_4280276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280276 prefixEnd_4280276 := by exact prefixLift 4280276
  have htrace : WordTrace (prefixWord ++ tailWord_4280276) baseStart_4280276 baseEnd_4280276 := by
    simpa [prefixWord, tailWord_4280276, baseEnd_4280276] using wordTrace_append hprefix tailTrace_4280276
  have hstable : (prefixWord ++ tailWord_4280276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280276).length < 2 ^ (prefixWord ++ tailWord_4280276).sum := by decide
  have hdescent : baseEnd_4280276 < baseStart_4280276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280289 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 4, 1, 4]
def baseStart_4280289 : Nat := 118140960795 + 4280289 * 2 ^ 59
def prefixEnd_4280289 : Nat := 4983230072969 + 3 ^ 40 * 4280289 * 2
def baseEnd_4280289 : Nat := 2197845597152509083302815

theorem tailTrace_4280289 : CollatzResearch.WordTrace tailWord_4280289 prefixEnd_4280289 2197845597152509083302815 := by
  unfold tailWord_4280289
  simp only [CollatzResearch.WordTrace]
  refine ⟨156114965190251443007219921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104076643460167628671479947 156114965190251443007219921)
  ·
    refine ⟨117086223892688582255414941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156114965190251443007219921 117086223892688582255414941)
    ·
      refine ⟨43907333959758218345780603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117086223892688582255414941 43907333959758218345780603)
      ·
        refine ⟨65861000939637327518670905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43907333959758218345780603 65861000939637327518670905)
        ·
          refine ⟨49395750704727995639003179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65861000939637327518670905 49395750704727995639003179)
          ·
            refine ⟨74093626057091993458504769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49395750704727995639003179 74093626057091993458504769)
            ·
              refine ⟨55570219542818995093878577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74093626057091993458504769 55570219542818995093878577)
              ·
                refine ⟨41677664657114246320408933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55570219542818995093878577 41677664657114246320408933)
                ·
                  refine ⟨7814562123208921185076675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41677664657114246320408933 7814562123208921185076675)
                  ·
                    refine ⟨11721843184813381777615013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7814562123208921185076675 11721843184813381777615013)
                    ·
                      refine ⟨2197845597152509083302815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11721843184813381777615013 2197845597152509083302815)
                      ·
                        rfl

theorem cell23_4280289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_4280289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280289 prefixEnd_4280289 := by exact prefixLift 4280289
  have htrace : WordTrace (prefixWord ++ tailWord_4280289) baseStart_4280289 baseEnd_4280289 := by
    simpa [prefixWord, tailWord_4280289, baseEnd_4280289] using wordTrace_append hprefix tailTrace_4280289
  have hstable : (prefixWord ++ tailWord_4280289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280289).length < 2 ^ (prefixWord ++ tailWord_4280289).sum := by decide
  have hdescent : baseEnd_4280289 < baseStart_4280289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280409 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 1, 1, 6]
def baseStart_4280409 : Nat := 118140960795 + 4280409 * 2 ^ 59
def prefixEnd_4280409 : Nat := 4983230072969 + 3 ^ 40 * 4280409 * 2
def baseEnd_4280409 : Nat := 2197907214831048613802263

theorem tailTrace_4280409 : CollatzResearch.WordTrace tailWord_4280409 prefixEnd_4280409 2197907214831048613802263 := by
  unfold tailWord_4280409
  simp only [CollatzResearch.WordTrace]
  refine ⟨156119341949816703501588281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104079561299877802334392187 156119341949816703501588281)
  ·
    refine ⟨117089506462362527626191211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156119341949816703501588281 117089506462362527626191211)
    ·
      refine ⟨175634259693543791439286817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117089506462362527626191211 175634259693543791439286817)
      ·
        refine ⟨131725694770157843579465113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175634259693543791439286817 131725694770157843579465113)
        ·
          refine ⟨98794271077618382684598835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131725694770157843579465113 98794271077618382684598835)
          ·
            refine ⟨148191406616427574026898253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98794271077618382684598835 148191406616427574026898253)
            ·
              refine ⟨55571777481160340260086845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148191406616427574026898253 55571777481160340260086845)
              ·
                refine ⟨20839416555435127597532567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55571777481160340260086845 20839416555435127597532567)
                ·
                  refine ⟨31259124833152691396298851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20839416555435127597532567 31259124833152691396298851)
                  ·
                    refine ⟨46888687249729037094448277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31259124833152691396298851 46888687249729037094448277)
                    ·
                      refine ⟨2197907214831048613802263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46888687249729037094448277 2197907214831048613802263)
                      ·
                        rfl

theorem cell23_4280409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_4280409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280409 prefixEnd_4280409 := by exact prefixLift 4280409
  have htrace : WordTrace (prefixWord ++ tailWord_4280409) baseStart_4280409 baseEnd_4280409 := by
    simpa [prefixWord, tailWord_4280409, baseEnd_4280409] using wordTrace_append hprefix tailTrace_4280409
  have hstable : (prefixWord ++ tailWord_4280409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280409).length < 2 ^ (prefixWord ++ tailWord_4280409).sum := by decide
  have hdescent : baseEnd_4280409 < baseStart_4280409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280419 : List Nat := [1, 1, 1, 5, 1, 1, 4, 9]
def baseStart_4280419 : Nat := 118140960795 + 4280419 * 2 ^ 59
def prefixEnd_4280419 : Nat := 4983230072969 + 3 ^ 40 * 4280419 * 2
def baseEnd_4280419 : Nat := 81404161097688650913971

theorem tailTrace_4280419 : CollatzResearch.WordTrace tailWord_4280419 prefixEnd_4280419 81404161097688650913971 := by
  unfold tailWord_4280419
  simp only [CollatzResearch.WordTrace]
  refine ⟨156119706679780475209452311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104079804453186983472968207 156119706679780475209452311)
  ·
    refine ⟨234179560019670712814178467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156119706679780475209452311 234179560019670712814178467)
    ·
      refine ⟨351269340029506069221267701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234179560019670712814178467 351269340029506069221267701)
      ·
        refine ⟨32931500627766193989493847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 351269340029506069221267701 32931500627766193989493847)
        ·
          refine ⟨49397250941649290984240771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32931500627766193989493847 49397250941649290984240771)
          ·
            refine ⟨74095876412473936476361157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49397250941649290984240771 74095876412473936476361157)
            ·
              refine ⟨13892976827338863089317717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74095876412473936476361157 13892976827338863089317717)
              ·
                refine ⟨81404161097688650913971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13892976827338863089317717 81404161097688650913971)
                ·
                  rfl

theorem cell23_4280419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 9].length) (baseStart_4280419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280419 prefixEnd_4280419 := by exact prefixLift 4280419
  have htrace : WordTrace (prefixWord ++ tailWord_4280419) baseStart_4280419 baseEnd_4280419 := by
    simpa [prefixWord, tailWord_4280419, baseEnd_4280419] using wordTrace_append hprefix tailTrace_4280419
  have hstable : (prefixWord ++ tailWord_4280419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280419).length < 2 ^ (prefixWord ++ tailWord_4280419).sum := by decide
  have hdescent : baseEnd_4280419 < baseStart_4280419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280430 : List Nat := [4, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4]
def baseStart_4280430 : Nat := 118140960795 + 4280430 * 2 ^ 59
def prefixEnd_4280430 : Nat := 4983230072969 + 3 ^ 40 * 4280430 * 2
def baseEnd_4280430 : Nat := 2197917997924793031639667

theorem tailTrace_4280430 : CollatzResearch.WordTrace tailWord_4280430 prefixEnd_4280430 2197917997924793031639667 := by
  unfold tailWord_4280430
  simp only [CollatzResearch.WordTrace]
  refine ⟨19515013485342578011012843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104080071921827082725401829 19515013485342578011012843)
  ·
    refine ⟨29272520228013867016519265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19515013485342578011012843 29272520228013867016519265)
    ·
      refine ⟨21954390171010400262389449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29272520228013867016519265 21954390171010400262389449)
      ·
        refine ⟨16465792628257800196792087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21954390171010400262389449 16465792628257800196792087)
        ·
          refine ⟨24698688942386700295188131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16465792628257800196792087 24698688942386700295188131)
          ·
            refine ⟨37048033413580050442782197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24698688942386700295188131 37048033413580050442782197)
            ·
              refine ⟨3473253132523129729010831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37048033413580050442782197 3473253132523129729010831)
              ·
                refine ⟨5209879698784694593516247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3473253132523129729010831 5209879698784694593516247)
                ·
                  refine ⟨7814819548177041890274371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5209879698784694593516247 7814819548177041890274371)
                  ·
                    refine ⟨11722229322265562835411557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7814819548177041890274371 11722229322265562835411557)
                    ·
                      refine ⟨2197917997924793031639667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11722229322265562835411557 2197917997924793031639667)
                      ·
                        rfl

theorem cell23_4280430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_4280430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280430 prefixEnd_4280430 := by exact prefixLift 4280430
  have htrace : WordTrace (prefixWord ++ tailWord_4280430) baseStart_4280430 baseEnd_4280430 := by
    simpa [prefixWord, tailWord_4280430, baseEnd_4280430] using wordTrace_append hprefix tailTrace_4280430
  have hstable : (prefixWord ++ tailWord_4280430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280430).length < 2 ^ (prefixWord ++ tailWord_4280430).sum := by decide
  have hdescent : baseEnd_4280430 < baseStart_4280430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280459 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 5]
def baseStart_4280459 : Nat := 118140960795 + 4280459 * 2 ^ 59
def prefixEnd_4280459 : Nat := 4983230072969 + 3 ^ 40 * 4280459 * 2
def baseEnd_4280459 : Nat := 2197932888863773418177033

theorem tailTrace_4280459 : CollatzResearch.WordTrace tailWord_4280459 prefixEnd_4280459 2197932888863773418177033 := by
  unfold tailWord_4280459
  simp only [CollatzResearch.WordTrace]
  refine ⟨156121165599635562040908431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104080777066423708027272287 156121165599635562040908431)
  ·
    refine ⟨234181748399453343061362647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156121165599635562040908431 234181748399453343061362647)
    ·
      refine ⟨351272622599180014592043971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234181748399453343061362647 351272622599180014592043971)
      ·
        refine ⟨526908933898770021888065957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351272622599180014592043971 526908933898770021888065957)
        ·
          refine ⟨98795425106019379104012367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 526908933898770021888065957 98795425106019379104012367)
          ·
            refine ⟨148193137659029068656018551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98795425106019379104012367 148193137659029068656018551)
            ·
              refine ⟨222289706488543602984027827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148193137659029068656018551 222289706488543602984027827)
              ·
                refine ⟨333434559732815404476041741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222289706488543602984027827 333434559732815404476041741)
                ·
                  refine ⟨125037959899805776678515653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 333434559732815404476041741 125037959899805776678515653)
                  ·
                    refine ⟨23444617481213583127221685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 125037959899805776678515653 23444617481213583127221685)
                    ·
                      refine ⟨2197932888863773418177033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23444617481213583127221685 2197932888863773418177033)
                      ·
                        rfl

theorem cell23_4280459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 5].length) (baseStart_4280459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280459 prefixEnd_4280459 := by exact prefixLift 4280459
  have htrace : WordTrace (prefixWord ++ tailWord_4280459) baseStart_4280459 baseEnd_4280459 := by
    simpa [prefixWord, tailWord_4280459, baseEnd_4280459] using wordTrace_append hprefix tailTrace_4280459
  have hstable : (prefixWord ++ tailWord_4280459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280459).length < 2 ^ (prefixWord ++ tailWord_4280459).sum := by decide
  have hdescent : baseEnd_4280459 < baseStart_4280459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280466 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 2, 7]
def baseStart_4280466 : Nat := 118140960795 + 4280466 * 2 ^ 59
def prefixEnd_4280466 : Nat := 4983230072969 + 3 ^ 40 * 4280466 * 2
def baseEnd_4280466 : Nat := 732645494409451630263167

theorem tailTrace_4280466 : CollatzResearch.WordTrace tailWord_4280466 prefixEnd_4280466 732645494409451630263167 := by
  unfold tailWord_4280466
  simp only [CollatzResearch.WordTrace]
  refine ⟨39030355227652550559103313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104080947273740134824275501 39030355227652550559103313)
  ·
    refine ⟨29272766420739412919327485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39030355227652550559103313 29272766420739412919327485)
    ·
      refine ⟨10977287407777279844747807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29272766420739412919327485 10977287407777279844747807)
      ·
        refine ⟨16465931111665919767121711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10977287407777279844747807 16465931111665919767121711)
        ·
          refine ⟨24698896667498879650682567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16465931111665919767121711 24698896667498879650682567)
          ·
            refine ⟨37048345001248319476023851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24698896667498879650682567 37048345001248319476023851)
            ·
              refine ⟨55572517501872479214035777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37048345001248319476023851 55572517501872479214035777)
              ·
                refine ⟨41679388126404359410526833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55572517501872479214035777 41679388126404359410526833)
                ·
                  refine ⟨31259541094803269557895125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41679388126404359410526833 31259541094803269557895125)
                  ·
                    refine ⟨732645494409451630263167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31259541094803269557895125 732645494409451630263167)
                    ·
                      rfl

theorem cell23_4280466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_4280466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280466 prefixEnd_4280466 := by exact prefixLift 4280466
  have htrace : WordTrace (prefixWord ++ tailWord_4280466) baseStart_4280466 baseEnd_4280466 := by
    simpa [prefixWord, tailWord_4280466, baseEnd_4280466] using wordTrace_append hprefix tailTrace_4280466
  have hstable : (prefixWord ++ tailWord_4280466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280466).length < 2 ^ (prefixWord ++ tailWord_4280466).sum := by decide
  have hdescent : baseEnd_4280466 < baseStart_4280466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280476 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_4280476 : Nat := 118140960795 + 4280476 * 2 ^ 59
def prefixEnd_4280476 : Nat := 4983230072969 + 3 ^ 40 * 4280476 * 2
def baseEnd_4280476 : Nat := 2197941618034899851664455

theorem tailTrace_4280476 : CollatzResearch.WordTrace tailWord_4280476 prefixEnd_4280476 2197941618034899851664455 := by
  unfold tailWord_4280476
  simp only [CollatzResearch.WordTrace]
  refine ⟨78060892820286986972138641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104081190427049315962851521 78060892820286986972138641)
  ·
    refine ⟨58545669615215240229103981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78060892820286986972138641 58545669615215240229103981)
    ·
      refine ⟨21954626105705715085913993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58545669615215240229103981 21954626105705715085913993)
      ·
        refine ⟨16465969579279286314435495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21954626105705715085913993 16465969579279286314435495)
        ·
          refine ⟨24698954368918929471653243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16465969579279286314435495 24698954368918929471653243)
          ·
            refine ⟨37048431553378394207479865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24698954368918929471653243 37048431553378394207479865)
            ·
              refine ⟨27786323665033795655609899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37048431553378394207479865 27786323665033795655609899)
              ·
                refine ⟨41679485497550693483414849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27786323665033795655609899 41679485497550693483414849)
                ·
                  refine ⟨31259614123163020112561137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41679485497550693483414849 31259614123163020112561137)
                  ·
                    refine ⟨23444710592372265084420853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31259614123163020112561137 23444710592372265084420853)
                    ·
                      refine ⟨2197941618034899851664455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23444710592372265084420853 2197941618034899851664455)
                      ·
                        rfl

theorem cell23_4280476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_4280476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280476 prefixEnd_4280476 := by exact prefixLift 4280476
  have htrace : WordTrace (prefixWord ++ tailWord_4280476) baseStart_4280476 baseEnd_4280476 := by
    simpa [prefixWord, tailWord_4280476, baseEnd_4280476] using wordTrace_append hprefix tailTrace_4280476
  have hstable : (prefixWord ++ tailWord_4280476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280476).length < 2 ^ (prefixWord ++ tailWord_4280476).sum := by decide
  have hdescent : baseEnd_4280476 < baseStart_4280476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280484 : List Nat := [2, 3, 1, 2, 5, 1, 2, 1, 1, 2, 3]
def baseStart_4280484 : Nat := 118140960795 + 4280484 * 2 ^ 59
def prefixEnd_4280484 : Nat := 4983230072969 + 3 ^ 40 * 4280484 * 2
def baseEnd_4280484 : Nat := 2197945725880135820364419

theorem tailTrace_4280484 : CollatzResearch.WordTrace tailWord_4280484 prefixEnd_4280484 2197945725880135820364419 := by
  unfold tailWord_4280484
  simp only [CollatzResearch.WordTrace]
  refine ⟨78061038712272495655284253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104081384949696660873712337 78061038712272495655284253)
  ·
    refine ⟨29272889517102185870731595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78061038712272495655284253 29272889517102185870731595)
    ·
      refine ⟨43909334275653278806097393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29272889517102185870731595 43909334275653278806097393)
      ·
        refine ⟨32932000706739959104573045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43909334275653278806097393 32932000706739959104573045)
        ·
          refine ⟨3087375066256871166053723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32932000706739959104573045 3087375066256871166053723)
          ·
            refine ⟨4631062599385306749080585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3087375066256871166053723 4631062599385306749080585)
            ·
              refine ⟨3473296949538980061810439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4631062599385306749080585 3473296949538980061810439)
              ·
                refine ⟨5209945424308470092715659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3473296949538980061810439 5209945424308470092715659)
                ·
                  refine ⟨7814918136462705139073489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5209945424308470092715659 7814918136462705139073489)
                  ·
                    refine ⟨5861188602347028854305117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7814918136462705139073489 5861188602347028854305117)
                    ·
                      refine ⟨2197945725880135820364419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5861188602347028854305117 2197945725880135820364419)
                      ·
                        rfl

theorem cell23_4280484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_4280484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280484 prefixEnd_4280484 := by exact prefixLift 4280484
  have htrace : WordTrace (prefixWord ++ tailWord_4280484) baseStart_4280484 baseEnd_4280484 := by
    simpa [prefixWord, tailWord_4280484, baseEnd_4280484] using wordTrace_append hprefix tailTrace_4280484
  have hstable : (prefixWord ++ tailWord_4280484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280484).length < 2 ^ (prefixWord ++ tailWord_4280484).sum := by decide
  have hdescent : baseEnd_4280484 < baseStart_4280484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280506 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3]
def baseStart_4280506 : Nat := 118140960795 + 4280506 * 2 ^ 59
def prefixEnd_4280506 : Nat := 4983230072969 + 3 ^ 40 * 4280506 * 2
def baseEnd_4280506 : Nat := 2197957022454534734289317

theorem tailTrace_4280506 : CollatzResearch.WordTrace tailWord_4280506 prefixEnd_4280506 2197957022454534734289317 := by
  unfold tailWord_4280506
  simp only [CollatzResearch.WordTrace]
  refine ⟨39030719957616322266967343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104081919886976859378579581 39030719957616322266967343)
  ·
    refine ⟨58546079936424483400451015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39030719957616322266967343 58546079936424483400451015)
    ·
      refine ⟨87819119904636725100676523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58546079936424483400451015 87819119904636725100676523)
      ·
        refine ⟨131728679856955087651014785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87819119904636725100676523 131728679856955087651014785)
        ·
          refine ⟨98796509892716315738261089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131728679856955087651014785 98796509892716315738261089)
          ·
            refine ⟨74097382419537236803695817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98796509892716315738261089 74097382419537236803695817)
            ·
              refine ⟨55573036814652927602771863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74097382419537236803695817 55573036814652927602771863)
              ·
                refine ⟨83359555221979391404157795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55573036814652927602771863 83359555221979391404157795)
                ·
                  refine ⟨125039332832969087106236693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83359555221979391404157795 125039332832969087106236693)
                  ·
                    refine ⟨5861218726545425958104845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 125039332832969087106236693 5861218726545425958104845)
                    ·
                      refine ⟨2197957022454534734289317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5861218726545425958104845 2197957022454534734289317)
                      ·
                        rfl

theorem cell23_4280506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_4280506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280506 prefixEnd_4280506 := by exact prefixLift 4280506
  have htrace : WordTrace (prefixWord ++ tailWord_4280506) baseStart_4280506 baseEnd_4280506 := by
    simpa [prefixWord, tailWord_4280506, baseEnd_4280506] using wordTrace_append hprefix tailTrace_4280506
  have hstable : (prefixWord ++ tailWord_4280506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280506).length < 2 ^ (prefixWord ++ tailWord_4280506).sum := by decide
  have hdescent : baseEnd_4280506 < baseStart_4280506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280514 : List Nat := [3, 5, 1, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_4280514 : Nat := 118140960795 + 4280514 * 2 ^ 59
def prefixEnd_4280514 : Nat := 4983230072969 + 3 ^ 40 * 4280514 * 2
def baseEnd_4280514 : Nat := 2197961130299770702989281

theorem tailTrace_4280514 : CollatzResearch.WordTrace tailWord_4280514 prefixEnd_4280514 2197961130299770702989281 := by
  unfold tailWord_4280514
  simp only [CollatzResearch.WordTrace]
  refine ⟨39030792903609076608540149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104082114409624204289440397 39030792903609076608540149)
  ·
    refine ⟨3659136834713350932050639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39030792903609076608540149 3659136834713350932050639)
    ·
      refine ⟨5488705252070026398075959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3659136834713350932050639 5488705252070026398075959)
      ·
        refine ⟨8233057878105039597113939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5488705252070026398075959 8233057878105039597113939)
        ·
          refine ⟨12349586817157559395670909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8233057878105039597113939 12349586817157559395670909)
          ·
            refine ⟨4631095056434084773376591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12349586817157559395670909 4631095056434084773376591)
            ·
              refine ⟨6946642584651127160064887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4631095056434084773376591 6946642584651127160064887)
              ·
                refine ⟨10419963876976690740097331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6946642584651127160064887 10419963876976690740097331)
                ·
                  refine ⟨15629945815465036110145997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10419963876976690740097331 15629945815465036110145997)
                  ·
                    refine ⟨5861229680799388541304749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15629945815465036110145997 5861229680799388541304749)
                    ·
                      refine ⟨2197961130299770702989281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5861229680799388541304749 2197961130299770702989281)
                      ·
                        rfl

theorem cell23_4280514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_4280514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280514 prefixEnd_4280514 := by exact prefixLift 4280514
  have htrace : WordTrace (prefixWord ++ tailWord_4280514) baseStart_4280514 baseEnd_4280514 := by
    simpa [prefixWord, tailWord_4280514, baseEnd_4280514] using wordTrace_append hprefix tailTrace_4280514
  have hstable : (prefixWord ++ tailWord_4280514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280514).length < 2 ^ (prefixWord ++ tailWord_4280514).sum := by decide
  have hdescent : baseEnd_4280514 < baseStart_4280514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280524 : List Nat := [2, 2, 1, 6, 1, 1, 2, 2, 1, 3, 2]
def baseStart_4280524 : Nat := 118140960795 + 4280524 * 2 ^ 59
def prefixEnd_4280524 : Nat := 4983230072969 + 3 ^ 40 * 4280524 * 2
def baseEnd_4280524 : Nat := 2197966265106315663864235

theorem tailTrace_4280524 : CollatzResearch.WordTrace tailWord_4280524 prefixEnd_4280524 2197966265106315663864235 := by
  unfold tailWord_4280524
  simp only [CollatzResearch.WordTrace]
  refine ⟨78061768172200039071012313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104082357562933385428016417 78061768172200039071012313)
  ·
    refine ⟨58546326129150029303259235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78061768172200039071012313 58546326129150029303259235)
    ·
      refine ⟨87819489193725043954888853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58546326129150029303259235 87819489193725043954888853)
      ·
        refine ⟨4116538555955861435385415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 87819489193725043954888853 4116538555955861435385415)
        ·
          refine ⟨6174807833933792153078123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4116538555955861435385415 6174807833933792153078123)
          ·
            refine ⟨9262211750900688229617185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6174807833933792153078123 9262211750900688229617185)
            ·
              refine ⟨6946658813175516172212889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9262211750900688229617185 6946658813175516172212889)
              ·
                refine ⟨5209994109881637129159667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6946658813175516172212889 5209994109881637129159667)
                ·
                  refine ⟨7814991164822455693739501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5209994109881637129159667 7814991164822455693739501)
                  ·
                    refine ⟨2930621686808420885152313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7814991164822455693739501 2930621686808420885152313)
                    ·
                      refine ⟨2197966265106315663864235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2930621686808420885152313 2197966265106315663864235)
                      ·
                        rfl

theorem cell23_4280524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_4280524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280524 prefixEnd_4280524 := by exact prefixLift 4280524
  have htrace : WordTrace (prefixWord ++ tailWord_4280524) baseStart_4280524 baseEnd_4280524 := by
    simpa [prefixWord, tailWord_4280524, baseEnd_4280524] using wordTrace_append hprefix tailTrace_4280524
  have hstable : (prefixWord ++ tailWord_4280524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280524).length < 2 ^ (prefixWord ++ tailWord_4280524).sum := by decide
  have hdescent : baseEnd_4280524 < baseStart_4280524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280563 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 2, 5, 2]
def baseStart_4280563 : Nat := 118140960795 + 4280563 * 2 ^ 59
def prefixEnd_4280563 : Nat := 4983230072969 + 3 ^ 40 * 4280563 * 2
def baseEnd_4280563 : Nat := 2197986290851841011276555

theorem tailTrace_4280563 : CollatzResearch.WordTrace tailWord_4280563 prefixEnd_4280563 2197986290851841011276555 := by
  unfold tailWord_4280563
  simp only [CollatzResearch.WordTrace]
  refine ⟨156124958791258787802694343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104083305860839191868462895 156124958791258787802694343)
  ·
    refine ⟨234187438186888181704041515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156124958791258787802694343 234187438186888181704041515)
    ·
      refine ⟨351281157280332272556062273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234187438186888181704041515 351281157280332272556062273)
      ·
        refine ⟨263460867960249204417046705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351281157280332272556062273 263460867960249204417046705)
        ·
          refine ⟨197595650970186903312785029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263460867960249204417046705 197595650970186903312785029)
          ·
            refine ⟨37049184556910044371147193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 197595650970186903312785029 37049184556910044371147193)
            ·
              refine ⟨27786888417682533278360395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37049184556910044371147193 27786888417682533278360395)
              ·
                refine ⟨41680332626523799917540593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27786888417682533278360395 41680332626523799917540593)
                ·
                  refine ⟨31260249469892849938155445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41680332626523799917540593 31260249469892849938155445)
                  ·
                    refine ⟨2930648387802454681702073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31260249469892849938155445 2930648387802454681702073)
                    ·
                      refine ⟨2197986290851841011276555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2930648387802454681702073 2197986290851841011276555)
                      ·
                        rfl

theorem cell23_4280563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 5, 2].length) (baseStart_4280563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280563 prefixEnd_4280563 := by exact prefixLift 4280563
  have htrace : WordTrace (prefixWord ++ tailWord_4280563) baseStart_4280563 baseEnd_4280563 := by
    simpa [prefixWord, tailWord_4280563, baseEnd_4280563] using wordTrace_append hprefix tailTrace_4280563
  have hstable : (prefixWord ++ tailWord_4280563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280563).length < 2 ^ (prefixWord ++ tailWord_4280563).sum := by decide
  have hdescent : baseEnd_4280563 < baseStart_4280563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280576 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 4]
def baseStart_4280576 : Nat := 118140960795 + 4280576 * 2 ^ 59
def prefixEnd_4280576 : Nat := 4983230072969 + 3 ^ 40 * 4280576 * 2
def baseEnd_4280576 : Nat := 2197992966100349460413995

theorem tailTrace_4280576 : CollatzResearch.WordTrace tailWord_4280576 prefixEnd_4280576 2197992966100349460413995 := by
  unfold tailWord_4280576
  simp only [CollatzResearch.WordTrace]
  refine ⟨78062716470105845511458791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104083621960141127348611721 78062716470105845511458791)
  ·
    refine ⟨117094074705158768267188187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78062716470105845511458791 117094074705158768267188187)
    ·
      refine ⟨175641112057738152400782281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117094074705158768267188187 175641112057738152400782281)
      ·
        refine ⟨131730834043303614300586711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175641112057738152400782281 131730834043303614300586711)
        ·
          refine ⟨197596251064955421450880067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131730834043303614300586711 197596251064955421450880067)
          ·
            refine ⟨296394376597433132176320101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197596251064955421450880067 296394376597433132176320101)
            ·
              refine ⟨55573945612018712283060019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 296394376597433132176320101 55573945612018712283060019)
              ·
                refine ⟨83360918418028068424590029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55573945612018712283060019 83360918418028068424590029)
                ·
                  refine ⟨31260344406760525659221261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83360918418028068424590029 31260344406760525659221261)
                  ·
                    refine ⟨11722629152535197122207973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31260344406760525659221261 11722629152535197122207973)
                    ·
                      refine ⟨2197992966100349460413995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11722629152535197122207973 2197992966100349460413995)
                      ·
                        rfl

theorem cell23_4280576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_4280576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280576 prefixEnd_4280576 := by exact prefixLift 4280576
  have htrace : WordTrace (prefixWord ++ tailWord_4280576) baseStart_4280576 baseEnd_4280576 := by
    simpa [prefixWord, tailWord_4280576, baseEnd_4280576] using wordTrace_append hprefix tailTrace_4280576
  have hstable : (prefixWord ++ tailWord_4280576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280576).length < 2 ^ (prefixWord ++ tailWord_4280576).sum := by decide
  have hdescent : baseEnd_4280576 < baseStart_4280576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280586 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 2, 8]
def baseStart_4280586 : Nat := 118140960795 + 4280586 * 2 ^ 59
def prefixEnd_4280586 : Nat := 4983230072969 + 3 ^ 40 * 4280586 * 2
def baseEnd_4280586 : Nat := 732666033635631473762983

theorem tailTrace_4280586 : CollatzResearch.WordTrace tailWord_4280586 prefixEnd_4280586 732666033635631473762983 := by
  unfold tailWord_4280586
  simp only [CollatzResearch.WordTrace]
  refine ⟨39031449417543865682695403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104083865113450308487187741 39031449417543865682695403)
  ·
    refine ⟨58547174126315798524043105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39031449417543865682695403 58547174126315798524043105)
    ·
      refine ⟨43910380594736848893032329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58547174126315798524043105 43910380594736848893032329)
      ·
        refine ⟨32932785446052636669774247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43910380594736848893032329 32932785446052636669774247)
        ·
          refine ⟨49399178169078955004661371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32932785446052636669774247 49399178169078955004661371)
          ·
            refine ⟨74098767253618432506992057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49399178169078955004661371 74098767253618432506992057)
            ·
              refine ⟨55574075440213824380244043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74098767253618432506992057 55574075440213824380244043)
              ·
                refine ⟨83361113160320736570366065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55574075440213824380244043 83361113160320736570366065)
                ·
                  refine ⟨62520834870240552427774549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83361113160320736570366065 62520834870240552427774549)
                  ·
                    refine ⟨732666033635631473762983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62520834870240552427774549 732666033635631473762983)
                    ·
                      rfl

theorem cell23_4280586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_4280586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280586 prefixEnd_4280586 := by exact prefixLift 4280586
  have htrace : WordTrace (prefixWord ++ tailWord_4280586) baseStart_4280586 baseEnd_4280586 := by
    simpa [prefixWord, tailWord_4280586, baseEnd_4280586] using wordTrace_append hprefix tailTrace_4280586
  have hstable : (prefixWord ++ tailWord_4280586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280586).length < 2 ^ (prefixWord ++ tailWord_4280586).sum := by decide
  have hdescent : baseEnd_4280586 < baseStart_4280586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280593 : List Nat := [1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 4]
def baseStart_4280593 : Nat := 118140960795 + 4280593 * 2 ^ 59
def prefixEnd_4280593 : Nat := 4983230072969 + 3 ^ 40 * 4280593 * 2
def baseEnd_4280593 : Nat := 2198001695271475893901417

theorem tailTrace_4280593 : CollatzResearch.WordTrace tailWord_4280593 prefixEnd_4280593 2198001695271475893901417 := by
  unfold tailWord_4280593
  simp only [CollatzResearch.WordTrace]
  refine ⟨156126052981150102926286433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104084035320766735284190955 156126052981150102926286433)
  ·
    refine ⟨117094539735862577194714825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156126052981150102926286433 117094539735862577194714825)
    ·
      refine ⟨87820904801896932896036119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117094539735862577194714825 87820904801896932896036119)
      ·
        refine ⟨131731357202845399344054179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87820904801896932896036119 131731357202845399344054179)
        ·
          refine ⟨197597035804268099016081269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131731357202845399344054179 197597035804268099016081269)
          ·
            refine ⟨18524722106650134282757619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 197597035804268099016081269 18524722106650134282757619)
            ·
              refine ⟨27787083159975201424136429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18524722106650134282757619 27787083159975201424136429)
              ·
                refine ⟨10420156184990700534051161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27787083159975201424136429 10420156184990700534051161)
                ·
                  refine ⟨7815117138743025400538371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10420156184990700534051161 7815117138743025400538371)
                  ·
                    refine ⟨11722675708114538100807557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7815117138743025400538371 11722675708114538100807557)
                    ·
                      refine ⟨2198001695271475893901417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11722675708114538100807557 2198001695271475893901417)
                      ·
                        rfl

theorem cell23_4280593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_4280593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280593 prefixEnd_4280593 := by exact prefixLift 4280593
  have htrace : WordTrace (prefixWord ++ tailWord_4280593) baseStart_4280593 baseEnd_4280593 := by
    simpa [prefixWord, tailWord_4280593, baseEnd_4280593] using wordTrace_append hprefix tailTrace_4280593
  have hstable : (prefixWord ++ tailWord_4280593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280593).length < 2 ^ (prefixWord ++ tailWord_4280593).sum := by decide
  have hdescent : baseEnd_4280593 < baseStart_4280593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280610 : List Nat := [3, 3, 1, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_4280610 : Nat := 118140960795 + 4280610 * 2 ^ 59
def prefixEnd_4280610 : Nat := 4983230072969 + 3 ^ 40 * 4280610 * 2
def baseEnd_4280610 : Nat := 2198010424442602327388839

theorem tailTrace_4280610 : CollatzResearch.WordTrace tailWord_4280610 prefixEnd_4280610 2198010424442602327388839 := by
  unfold tailWord_4280610
  simp only [CollatzResearch.WordTrace]
  refine ⟨39031668255522128707413821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104084448681392343219770189 39031668255522128707413821)
  ·
    refine ⟨14636875595820798265280183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39031668255522128707413821 14636875595820798265280183)
    ·
      refine ⟨21955313393731197397920275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14636875595820798265280183 21955313393731197397920275)
      ·
        refine ⟨32932970090596796096880413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21955313393731197397920275 32932970090596796096880413)
        ·
          refine ⟨12349863783973798536330155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32932970090596796096880413 12349863783973798536330155)
          ·
            refine ⟨18524795675960697804495233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12349863783973798536330155 18524795675960697804495233)
            ·
              refine ⟨13893596756970523353371425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18524795675960697804495233 13893596756970523353371425)
              ·
                refine ⟨10420197567727892515028569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13893596756970523353371425 10420197567727892515028569)
                ·
                  refine ⟨7815148175795919386271427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10420197567727892515028569 7815148175795919386271427)
                  ·
                    refine ⟨11722722263693879079407141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7815148175795919386271427 11722722263693879079407141)
                    ·
                      refine ⟨2198010424442602327388839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11722722263693879079407141 2198010424442602327388839)
                      ·
                        rfl

theorem cell23_4280610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_4280610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280610 prefixEnd_4280610 := by exact prefixLift 4280610
  have htrace : WordTrace (prefixWord ++ tailWord_4280610) baseStart_4280610 baseEnd_4280610 := by
    simpa [prefixWord, tailWord_4280610, baseEnd_4280610] using wordTrace_append hprefix tailTrace_4280610
  have hstable : (prefixWord ++ tailWord_4280610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280610).length < 2 ^ (prefixWord ++ tailWord_4280610).sum := by decide
  have hdescent : baseEnd_4280610 < baseStart_4280610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280644 : List Nat := [2, 3, 4, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_4280644 : Nat := 118140960795 + 4280644 * 2 ^ 59
def prefixEnd_4280644 : Nat := 4983230072969 + 3 ^ 40 * 4280644 * 2
def baseEnd_4280644 : Nat := 2198027882784855194363683

theorem tailTrace_4280644 : CollatzResearch.WordTrace tailWord_4280644 prefixEnd_4280644 2198027882784855194363683 := by
  unfold tailWord_4280644
  simp only [CollatzResearch.WordTrace]
  refine ⟨78063956551982669318196493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104085275402643559090928657 78063956551982669318196493)
  ·
    refine ⟨29273983706993500994323685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78063956551982669318196493 29273983706993500994323685)
    ·
      refine ⟨5488871945061281436435691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29273983706993500994323685 5488871945061281436435691)
      ·
        refine ⟨8233307917591922154653537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5488871945061281436435691 8233307917591922154653537)
        ·
          refine ⟨6174980938193941615990153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8233307917591922154653537 6174980938193941615990153)
          ·
            refine ⟨4631235703645456211992615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6174980938193941615990153 4631235703645456211992615)
            ·
              refine ⟨6946853555468184317988923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4631235703645456211992615 6946853555468184317988923)
              ·
                refine ⟨10420280333202276476983385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6946853555468184317988923 10420280333202276476983385)
                ·
                  refine ⟨7815210249901707357737539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10420280333202276476983385 7815210249901707357737539)
                  ·
                    refine ⟨11722815374852561036606309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7815210249901707357737539 11722815374852561036606309)
                    ·
                      refine ⟨2198027882784855194363683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11722815374852561036606309 2198027882784855194363683)
                      ·
                        rfl

theorem cell23_4280644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_4280644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280644 prefixEnd_4280644 := by exact prefixLift 4280644
  have htrace : WordTrace (prefixWord ++ tailWord_4280644) baseStart_4280644 baseEnd_4280644 := by
    simpa [prefixWord, tailWord_4280644, baseEnd_4280644] using wordTrace_append hprefix tailTrace_4280644
  have hstable : (prefixWord ++ tailWord_4280644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280644).length < 2 ^ (prefixWord ++ tailWord_4280644).sum := by decide
  have hdescent : baseEnd_4280644 < baseStart_4280644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280677 : List Nat := [1, 3, 1, 3, 1, 4, 2, 1, 3, 1, 3]
def baseStart_4280677 : Nat := 118140960795 + 4280677 * 2 ^ 59
def prefixEnd_4280677 : Nat := 4983230072969 + 3 ^ 40 * 4280677 * 2
def baseEnd_4280677 : Nat := 2198044827646453565251031

theorem tailTrace_4280677 : CollatzResearch.WordTrace tailWord_4280677 prefixEnd_4280677 2198044827646453565251031 := by
  unfold tailWord_4280677
  simp only [CollatzResearch.WordTrace]
  refine ⟨156129116712845785272344285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104086077808563856848229523 156129116712845785272344285)
  ·
    refine ⟨58548418767317169477129107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156129116712845785272344285 58548418767317169477129107)
    ·
      refine ⟨87822628150975754215693661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58548418767317169477129107 87822628150975754215693661)
      ·
        refine ⟨32933485556615907830885123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87822628150975754215693661 32933485556615907830885123)
        ·
          refine ⟨49400228334923861746327685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32933485556615907830885123 49400228334923861746327685)
          ·
            refine ⟨9262542812798224077436441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49400228334923861746327685 9262542812798224077436441)
            ·
              refine ⟨6946907109598668058077331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9262542812798224077436441 6946907109598668058077331)
              ·
                refine ⟨10420360664398002087115997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6946907109598668058077331 10420360664398002087115997)
                ·
                  refine ⟨3907635249149250782668499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10420360664398002087115997 3907635249149250782668499)
                  ·
                    refine ⟨5861452873723876174002749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3907635249149250782668499 5861452873723876174002749)
                    ·
                      refine ⟨2198044827646453565251031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5861452873723876174002749 2198044827646453565251031)
                      ·
                        rfl

theorem cell23_4280677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_4280677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280677 prefixEnd_4280677 := by exact prefixLift 4280677
  have htrace : WordTrace (prefixWord ++ tailWord_4280677) baseStart_4280677 baseEnd_4280677 := by
    simpa [prefixWord, tailWord_4280677, baseEnd_4280677] using wordTrace_append hprefix tailTrace_4280677
  have hstable : (prefixWord ++ tailWord_4280677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280677).length < 2 ^ (prefixWord ++ tailWord_4280677).sum := by decide
  have hdescent : baseEnd_4280677 < baseStart_4280677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280744 : List Nat := [2, 1, 6, 1, 1, 2, 1, 3, 2, 4]
def baseStart_4280744 : Nat := 118140960795 + 4280744 * 2 ^ 59
def prefixEnd_4280744 : Nat := 4983230072969 + 3 ^ 40 * 4280744 * 2
def baseEnd_4280744 : Nat := 732693076950101601037741

theorem tailTrace_4280744 : CollatzResearch.WordTrace tailWord_4280744 prefixEnd_4280744 732693076950101601037741 := by
  unfold tailWord_4280744
  simp only [CollatzResearch.WordTrace]
  refine ⟨78065780201801527857516643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104087706935735370476688857 78065780201801527857516643)
  ·
    refine ⟨117098670302702291786274965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78065780201801527857516643 117098670302702291786274965)
    ·
      refine ⟨5489000170439169927481639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 117098670302702291786274965 5489000170439169927481639)
      ·
        refine ⟨8233500255658754891222459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5489000170439169927481639 8233500255658754891222459)
        ·
          refine ⟨12350250383488132336833689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8233500255658754891222459 12350250383488132336833689)
          ·
            refine ⟨9262687787616099252625267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12350250383488132336833689 9262687787616099252625267)
            ·
              refine ⟨13894031681424148878937901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9262687787616099252625267 13894031681424148878937901)
              ·
                refine ⟨5210261880534055829601713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13894031681424148878937901 5210261880534055829601713)
                ·
                  refine ⟨3907696410400541872201285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5210261880534055829601713 3907696410400541872201285)
                  ·
                    refine ⟨732693076950101601037741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3907696410400541872201285 732693076950101601037741)
                    ·
                      rfl

theorem cell23_4280744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_4280744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280744 prefixEnd_4280744 := by exact prefixLift 4280744
  have htrace : WordTrace (prefixWord ++ tailWord_4280744) baseStart_4280744 baseEnd_4280744 := by
    simpa [prefixWord, tailWord_4280744, baseEnd_4280744] using wordTrace_append hprefix tailTrace_4280744
  have hstable : (prefixWord ++ tailWord_4280744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280744).length < 2 ^ (prefixWord ++ tailWord_4280744).sum := by decide
  have hdescent : baseEnd_4280744 < baseStart_4280744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280773 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 6, 3, 4]
def baseStart_4280773 : Nat := 118140960795 + 4280773 * 2 ^ 59
def prefixEnd_4280773 : Nat := 4983230072969 + 3 ^ 40 * 4280773 * 2
def baseEnd_4280773 : Nat := 2198094121789285189650589

theorem tailTrace_4280773 : CollatzResearch.WordTrace tailWord_4280773 prefixEnd_4280773 2198094121789285189650589 := by
  unfold tailWord_4280773
  simp only [CollatzResearch.WordTrace]
  refine ⟨156132618120497993667838973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104088412080331995778559315 156132618120497993667838973)
  ·
    refine ⟨58549731795186747625439615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156132618120497993667838973 58549731795186747625439615)
    ·
      refine ⟨87824597692780121438159423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58549731795186747625439615 87824597692780121438159423)
      ·
        refine ⟨131736896539170182157239135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87824597692780121438159423 131736896539170182157239135)
        ·
          refine ⟨197605344808755273235858703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131736896539170182157239135 197605344808755273235858703)
          ·
            refine ⟨296408017213132909853788055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197605344808755273235858703 296408017213132909853788055)
            ·
              refine ⟨444612025819699364780682083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296408017213132909853788055 444612025819699364780682083)
              ·
                refine ⟨666918038729549047171023125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444612025819699364780682083 666918038729549047171023125)
                ·
                  refine ⟨31261783065447611586141709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 666918038729549047171023125 31261783065447611586141709)
                  ·
                    refine ⟨11723168649542854344803141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31261783065447611586141709 11723168649542854344803141)
                    ·
                      refine ⟨2198094121789285189650589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11723168649542854344803141 2198094121789285189650589)
                      ·
                        rfl

theorem cell23_4280773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_4280773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280773 prefixEnd_4280773 := by exact prefixLift 4280773
  have htrace : WordTrace (prefixWord ++ tailWord_4280773) baseStart_4280773 baseEnd_4280773 := by
    simpa [prefixWord, tailWord_4280773, baseEnd_4280773] using wordTrace_append hprefix tailTrace_4280773
  have hstable : (prefixWord ++ tailWord_4280773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280773).length < 2 ^ (prefixWord ++ tailWord_4280773).sum := by decide
  have hdescent : baseEnd_4280773 < baseStart_4280773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280777 : List Nat := [1, 2, 1, 1, 2, 1, 4, 5, 1, 3, 2]
def baseStart_4280777 : Nat := 118140960795 + 4280777 * 2 ^ 59
def prefixEnd_4280777 : Nat := 4983230072969 + 3 ^ 40 * 4280777 * 2
def baseEnd_4280777 : Nat := 2198096175711903174000571

theorem tailTrace_4280777 : CollatzResearch.WordTrace tailWord_4280777 prefixEnd_4280777 2198096175711903174000571 := by
  unfold tailWord_4280777
  simp only [CollatzResearch.WordTrace]
  refine ⟨156132764012483502350984585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104088509341655668233989723 156132764012483502350984585)
  ·
    refine ⟨117099573009362626763238439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156132764012483502350984585 117099573009362626763238439)
    ·
      refine ⟨175649359514043940144857659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117099573009362626763238439 175649359514043940144857659)
      ·
        refine ⟨263474039271065910217286489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175649359514043940144857659 263474039271065910217286489)
        ·
          refine ⟨197605529453299432662964867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263474039271065910217286489 197605529453299432662964867)
          ·
            refine ⟨296408294179949148994447301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197605529453299432662964867 296408294179949148994447301)
            ·
              refine ⟨55576555158740465436458869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 296408294179949148994447301 55576555158740465436458869)
              ·
                refine ⟨5210302046131918634668019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55576555158740465436458869 5210302046131918634668019)
                ·
                  refine ⟨7815453069197877952002029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5210302046131918634668019 7815453069197877952002029)
                  ·
                    refine ⟨2930794900949204232000761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7815453069197877952002029 2930794900949204232000761)
                    ·
                      refine ⟨2198096175711903174000571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2930794900949204232000761 2198096175711903174000571)
                      ·
                        rfl

theorem cell23_4280777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 3, 2].length) (baseStart_4280777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280777 prefixEnd_4280777 := by exact prefixLift 4280777
  have htrace : WordTrace (prefixWord ++ tailWord_4280777) baseStart_4280777 baseEnd_4280777 := by
    simpa [prefixWord, tailWord_4280777, baseEnd_4280777] using wordTrace_append hprefix tailTrace_4280777
  have hstable : (prefixWord ++ tailWord_4280777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280777).length < 2 ^ (prefixWord ++ tailWord_4280777).sum := by decide
  have hdescent : baseEnd_4280777 < baseStart_4280777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280783 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 2, 6]
def baseStart_4280783 : Nat := 118140960795 + 4280783 * 2 ^ 59
def prefixEnd_4280783 : Nat := 4983230072969 + 3 ^ 40 * 4280783 * 2
def baseEnd_4280783 : Nat := 732699752198610050175181

theorem tailTrace_4280783 : CollatzResearch.WordTrace tailWord_4280783 prefixEnd_4280783 732699752198610050175181 := by
  unfold tailWord_4280783
  simp only [CollatzResearch.WordTrace]
  refine ⟨156132982850461765375703003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104088655233641176917135335 156132982850461765375703003)
  ·
    refine ⟨234199474275692648063554505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156132982850461765375703003 234199474275692648063554505)
    ·
      refine ⟨175649605706769486047665879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234199474275692648063554505 175649605706769486047665879)
      ·
        refine ⟨263474408560154229071498819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175649605706769486047665879 263474408560154229071498819)
        ·
          refine ⟨395211612840231343607248229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263474408560154229071498819 395211612840231343607248229)
          ·
            refine ⟨74102177407543376926359043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 395211612840231343607248229 74102177407543376926359043)
            ·
              refine ⟨111153266111315065389538565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74102177407543376926359043 111153266111315065389538565)
              ·
                refine ⟨20841237395871574760538481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111153266111315065389538565 20841237395871574760538481)
                ·
                  refine ⟨15630928046903681070403861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20841237395871574760538481 15630928046903681070403861)
                  ·
                    refine ⟨732699752198610050175181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15630928046903681070403861 732699752198610050175181)
                    ·
                      rfl

theorem cell23_4280783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 6].length) (baseStart_4280783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280783 prefixEnd_4280783 := by exact prefixLift 4280783
  have htrace : WordTrace (prefixWord ++ tailWord_4280783) baseStart_4280783 baseEnd_4280783 := by
    simpa [prefixWord, tailWord_4280783, baseEnd_4280783] using wordTrace_append hprefix tailTrace_4280783
  have hstable : (prefixWord ++ tailWord_4280783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280783).length < 2 ^ (prefixWord ++ tailWord_4280783).sum := by decide
  have hdescent : baseEnd_4280783 < baseStart_4280783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280860 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 1, 7]
def baseStart_4280860 : Nat := 118140960795 + 4280860 * 2 ^ 59
def prefixEnd_4280860 : Nat := 4983230072969 + 3 ^ 40 * 4280860 * 2
def baseEnd_4280860 : Nat := 732712931535408783087563

theorem tailTrace_4280860 : CollatzResearch.WordTrace tailWord_4280860 prefixEnd_4280860 732712931535408783087563 := by
  unfold tailWord_4280860
  simp only [CollatzResearch.WordTrace]
  refine ⟨78067895635591403763128017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104090527514121871684170689 78067895635591403763128017)
  ·
    refine ⟨58550921726693552822346013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78067895635591403763128017 58550921726693552822346013)
    ·
      refine ⟨21956595647510082308379755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58550921726693552822346013 21956595647510082308379755)
      ·
        refine ⟨32934893471265123462569633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21956595647510082308379755 32934893471265123462569633)
        ·
          refine ⟨24701170103448842596927225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32934893471265123462569633 24701170103448842596927225)
          ·
            refine ⟨18525877577586631947695419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24701170103448842596927225 18525877577586631947695419)
            ·
              refine ⟨27788816366379947921543129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18525877577586631947695419 27788816366379947921543129)
              ·
                refine ⟨20841612274784960941157347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27788816366379947921543129 20841612274784960941157347)
                ·
                  refine ⟨31262418412177441411736021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20841612274784960941157347 31262418412177441411736021)
                  ·
                    refine ⟨732712931535408783087563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31262418412177441411736021 732712931535408783087563)
                    ·
                      rfl

theorem cell23_4280860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_4280860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280860 prefixEnd_4280860 := by exact prefixLift 4280860
  have htrace : WordTrace (prefixWord ++ tailWord_4280860) baseStart_4280860 baseEnd_4280860 := by
    simpa [prefixWord, tailWord_4280860, baseEnd_4280860] using wordTrace_append hprefix tailTrace_4280860
  have hstable : (prefixWord ++ tailWord_4280860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280860).length < 2 ^ (prefixWord ++ tailWord_4280860).sum := by decide
  have hdescent : baseEnd_4280860 < baseStart_4280860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280880 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 4]
def baseStart_4280880 : Nat := 118140960795 + 4280880 * 2 ^ 59
def prefixEnd_4280880 : Nat := 4983230072969 + 3 ^ 40 * 4280880 * 2
def baseEnd_4280880 : Nat := 2198149064219316271012597

theorem tailTrace_4280880 : CollatzResearch.WordTrace tailWord_4280880 prefixEnd_4280880 2198149064219316271012597 := by
  unfold tailWord_4280880
  simp only [CollatzResearch.WordTrace]
  refine ⟨78068260365555175470992047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104091013820740233961322729 78068260365555175470992047)
  ·
    refine ⟨117102390548332763206488071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78068260365555175470992047 117102390548332763206488071)
    ·
      refine ⟨175653585822499144809732107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117102390548332763206488071 175653585822499144809732107)
      ·
        refine ⟨263480378733748717214598161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175653585822499144809732107 263480378733748717214598161)
        ·
          refine ⟨197610284050311537910948621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263480378733748717214598161 197610284050311537910948621)
          ·
            refine ⟨74103856518866826716605733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197610284050311537910948621 74103856518866826716605733)
            ·
              refine ⟨13894473097287530009363575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74103856518866826716605733 13894473097287530009363575)
              ·
                refine ⟨20841709645931295014045363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13894473097287530009363575 20841709645931295014045363)
                ·
                  refine ⟨31262564468896942521068045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20841709645931295014045363 31262564468896942521068045)
                  ·
                    refine ⟨11723461675836353445400517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31262564468896942521068045 11723461675836353445400517)
                    ·
                      refine ⟨2198149064219316271012597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11723461675836353445400517 2198149064219316271012597)
                      ·
                        rfl

theorem cell23_4280880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 4].length) (baseStart_4280880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280880 prefixEnd_4280880 := by exact prefixLift 4280880
  have htrace : WordTrace (prefixWord ++ tailWord_4280880) baseStart_4280880 baseEnd_4280880 := by
    simpa [prefixWord, tailWord_4280880, baseEnd_4280880] using wordTrace_append hprefix tailTrace_4280880
  have hstable : (prefixWord ++ tailWord_4280880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280880).length < 2 ^ (prefixWord ++ tailWord_4280880).sum := by decide
  have hdescent : baseEnd_4280880 < baseStart_4280880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280897 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_4280897 : Nat := 118140960795 + 4280897 * 2 ^ 59
def prefixEnd_4280897 : Nat := 4983230072969 + 3 ^ 40 * 4280897 * 2
def baseEnd_4280897 : Nat := 2198157793390442704500019

theorem tailTrace_4280897 : CollatzResearch.WordTrace tailWord_4280897 prefixEnd_4280897 2198157793390442704500019 := by
  unfold tailWord_4280897
  simp only [CollatzResearch.WordTrace]
  refine ⟨156137140772048762845352945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104091427181365841896901963 156137140772048762845352945)
  ·
    refine ⟨117102855579036572134014709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156137140772048762845352945 117102855579036572134014709)
    ·
      refine ⟨10978392710534678637563879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117102855579036572134014709 10978392710534678637563879)
      ·
        refine ⟨16467589065802017956345819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10978392710534678637563879 16467589065802017956345819)
        ·
          refine ⟨24701383598703026934518729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16467589065802017956345819 24701383598703026934518729)
          ·
            refine ⟨18526037699027270200889047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24701383598703026934518729 18526037699027270200889047)
            ·
              refine ⟨27789056548540905301333571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18526037699027270200889047 27789056548540905301333571)
              ·
                refine ⟨41683584822811357952000357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27789056548540905301333571 41683584822811357952000357)
                ·
                  refine ⟨7815672154277129616000067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41683584822811357952000357 7815672154277129616000067)
                  ·
                    refine ⟨11723508231415694424000101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7815672154277129616000067 11723508231415694424000101)
                    ·
                      refine ⟨2198157793390442704500019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11723508231415694424000101 2198157793390442704500019)
                      ·
                        rfl

theorem cell23_4280897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_4280897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280897 prefixEnd_4280897 := by exact prefixLift 4280897
  have htrace : WordTrace (prefixWord ++ tailWord_4280897) baseStart_4280897 baseEnd_4280897 := by
    simpa [prefixWord, tailWord_4280897, baseEnd_4280897] using wordTrace_append hprefix tailTrace_4280897
  have hstable : (prefixWord ++ tailWord_4280897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280897).length < 2 ^ (prefixWord ++ tailWord_4280897).sum := by decide
  have hdescent : baseEnd_4280897 < baseStart_4280897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280907 : List Nat := [1, 1, 1, 1, 3, 1, 7, 1, 3, 4]
def baseStart_4280907 : Nat := 118140960795 + 4280907 * 2 ^ 59
def prefixEnd_4280907 : Nat := 4983230072969 + 3 ^ 40 * 4280907 * 2
def baseEnd_4280907 : Nat := 732720976065662555124991

theorem tailTrace_4280907 : CollatzResearch.WordTrace tailWord_4280907 prefixEnd_4280907 732720976065662555124991 := by
  unfold tailWord_4280907
  simp only [CollatzResearch.WordTrace]
  refine ⟨156137505502012534553216975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104091670334675023035477983 156137505502012534553216975)
  ·
    refine ⟨234206258253018801829825463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156137505502012534553216975 234206258253018801829825463)
    ·
      refine ⟨351309387379528202744738195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234206258253018801829825463 351309387379528202744738195)
      ·
        refine ⟨526964081069292304117107293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351309387379528202744738195 526964081069292304117107293)
        ·
          refine ⟨197611530400984614043915235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 526964081069292304117107293 197611530400984614043915235)
          ·
            refine ⟨296417295601476921065872853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197611530400984614043915235 296417295601476921065872853)
            ·
              refine ⟨6947280365659615337481395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 296417295601476921065872853 6947280365659615337481395)
              ·
                refine ⟨10420920548489423006222093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6947280365659615337481395 10420920548489423006222093)
                ·
                  refine ⟨3907845205683533627333285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10420920548489423006222093 3907845205683533627333285)
                  ·
                    refine ⟨732720976065662555124991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3907845205683533627333285 732720976065662555124991)
                    ·
                      rfl

theorem cell23_4280907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 4].length) (baseStart_4280907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280907 prefixEnd_4280907 := by exact prefixLift 4280907
  have htrace : WordTrace (prefixWord ++ tailWord_4280907) baseStart_4280907 baseEnd_4280907 := by
    simpa [prefixWord, tailWord_4280907, baseEnd_4280907] using wordTrace_append hprefix tailTrace_4280907
  have hstable : (prefixWord ++ tailWord_4280907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280907).length < 2 ^ (prefixWord ++ tailWord_4280907).sum := by decide
  have hdescent : baseEnd_4280907 < baseStart_4280907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280910 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_4280910 : Nat := 118140960795 + 4280910 * 2 ^ 59
def prefixEnd_4280910 : Nat := 4983230072969 + 3 ^ 40 * 4280910 * 2
def baseEnd_4280910 : Nat := 2198164468638951153637459

theorem tailTrace_4280910 : CollatzResearch.WordTrace tailWord_4280910 prefixEnd_4280910 2198164468638951153637459 := by
  unfold tailWord_4280910
  simp only [CollatzResearch.WordTrace]
  refine ⟨19517201865125208258197023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104091743280667777377050789 19517201865125208258197023)
  ·
    refine ⟨29275802797687812387295535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19517201865125208258197023 29275802797687812387295535)
    ·
      refine ⟨43913704196531718580943303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29275802797687812387295535 43913704196531718580943303)
      ·
        refine ⟨65870556294797577871414955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43913704196531718580943303 65870556294797577871414955)
        ·
          refine ⟨98805834442196366807122433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65870556294797577871414955 98805834442196366807122433)
          ·
            refine ⟨74104375831647275105341825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98805834442196366807122433 74104375831647275105341825)
            ·
              refine ⟨55578281873735456329006369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74104375831647275105341825 55578281873735456329006369)
              ·
                refine ⟨41683711405301592246754777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55578281873735456329006369 41683711405301592246754777)
                ·
                  refine ⟨31262783553976194185066083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41683711405301592246754777 31262783553976194185066083)
                  ·
                    refine ⟨46894175330964291277599125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31262783553976194185066083 46894175330964291277599125)
                    ·
                      refine ⟨2198164468638951153637459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46894175330964291277599125 2198164468638951153637459)
                      ·
                        rfl

theorem cell23_4280910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_4280910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280910 prefixEnd_4280910 := by exact prefixLift 4280910
  have htrace : WordTrace (prefixWord ++ tailWord_4280910) baseStart_4280910 baseEnd_4280910 := by
    simpa [prefixWord, tailWord_4280910, baseEnd_4280910] using wordTrace_append hprefix tailTrace_4280910
  have hstable : (prefixWord ++ tailWord_4280910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280910).length < 2 ^ (prefixWord ++ tailWord_4280910).sum := by decide
  have hdescent : baseEnd_4280910 < baseStart_4280910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280947 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 7, 1, 3]
def baseStart_4280947 : Nat := 118140960795 + 4280947 * 2 ^ 59
def prefixEnd_4280947 : Nat := 4983230072969 + 3 ^ 40 * 4280947 * 2
def baseEnd_4280947 : Nat := 2198183467423167508874789

theorem tailTrace_4280947 : CollatzResearch.WordTrace tailWord_4280947 prefixEnd_4280947 2198183467423167508874789 := by
  unfold tailWord_4280947
  simp only [CollatzResearch.WordTrace]
  refine ⟨156138964421867621384673095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104092642947911747589782063 156138964421867621384673095)
  ·
    refine ⟨234208446632801432077009643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156138964421867621384673095 234208446632801432077009643)
    ·
      refine ⟨351312669949202148115514465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234208446632801432077009643 351312669949202148115514465)
      ·
        refine ⟨263484502461901611086635849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351312669949202148115514465 263484502461901611086635849)
        ·
          refine ⟨197613376846426208314976887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263484502461901611086635849 197613376846426208314976887)
          ·
            refine ⟨296420065269639312472465331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197613376846426208314976887 296420065269639312472465331)
            ·
              refine ⟨444630097904458968708697997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296420065269639312472465331 444630097904458968708697997)
              ·
                refine ⟨166736286714172113265761749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 444630097904458968708697997 166736286714172113265761749)
                ·
                  refine ⟨3907881719863408904666291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 166736286714172113265761749 3907881719863408904666291)
                  ·
                    refine ⟨5861822579795113356999437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3907881719863408904666291 5861822579795113356999437)
                    ·
                      refine ⟨2198183467423167508874789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5861822579795113356999437 2198183467423167508874789)
                      ·
                        rfl

theorem cell23_4280947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 1, 3].length) (baseStart_4280947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280947 prefixEnd_4280947 := by exact prefixLift 4280947
  have htrace : WordTrace (prefixWord ++ tailWord_4280947) baseStart_4280947 baseEnd_4280947 := by
    simpa [prefixWord, tailWord_4280947, baseEnd_4280947] using wordTrace_append hprefix tailTrace_4280947
  have hstable : (prefixWord ++ tailWord_4280947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280947).length < 2 ^ (prefixWord ++ tailWord_4280947).sum := by decide
  have hdescent : baseEnd_4280947 < baseStart_4280947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280974 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2]
def baseStart_4280974 : Nat := 118140960795 + 4280974 * 2 ^ 59
def prefixEnd_4280974 : Nat := 4983230072969 + 3 ^ 40 * 4280974 * 2
def baseEnd_4280974 : Nat := 2198197331400838903237165

theorem tailTrace_4280974 : CollatzResearch.WordTrace tailWord_4280974 prefixEnd_4280974 2198197331400838903237165 := by
  unfold tailWord_4280974
  simp only [CollatzResearch.WordTrace]
  refine ⟨19517493649096225624488247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104093299461846536663937317 19517493649096225624488247)
  ·
    refine ⟨29276240473644338436732371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19517493649096225624488247 29276240473644338436732371)
    ·
      refine ⟨43914360710466507655098557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29276240473644338436732371 43914360710466507655098557)
      ·
        refine ⟨16467885266424940370661959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43914360710466507655098557 16467885266424940370661959)
        ·
          refine ⟨24701827899637410555992939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16467885266424940370661959 24701827899637410555992939)
          ·
            refine ⟨37052741849456115833989409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24701827899637410555992939 37052741849456115833989409)
            ·
              refine ⟨27789556387092086875492057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37052741849456115833989409 27789556387092086875492057)
              ·
                refine ⟨20842167290319065156619043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27789556387092086875492057 20842167290319065156619043)
                ·
                  refine ⟨31263250935478597734928565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20842167290319065156619043 31263250935478597734928565)
                  ·
                    refine ⟨2930929775201118537649553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31263250935478597734928565 2930929775201118537649553)
                    ·
                      refine ⟨2198197331400838903237165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2930929775201118537649553 2198197331400838903237165)
                      ·
                        rfl

theorem cell23_4280974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_4280974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280974 prefixEnd_4280974 := by exact prefixLift 4280974
  have htrace : WordTrace (prefixWord ++ tailWord_4280974) baseStart_4280974 baseEnd_4280974 := by
    simpa [prefixWord, tailWord_4280974, baseEnd_4280974] using wordTrace_append hprefix tailTrace_4280974
  have hstable : (prefixWord ++ tailWord_4280974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280974).length < 2 ^ (prefixWord ++ tailWord_4280974).sum := by decide
  have hdescent : baseEnd_4280974 < baseStart_4280974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4280997 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 4, 4]
def baseStart_4280997 : Nat := 118140960795 + 4280997 * 2 ^ 59
def prefixEnd_4280997 : Nat := 4983230072969 + 3 ^ 40 * 4280997 * 2
def baseEnd_4280997 : Nat := 732736380485297437749853

theorem tailTrace_4280997 : CollatzResearch.WordTrace tailWord_4280997 prefixEnd_4280997 732736380485297437749853 := by
  unfold tailWord_4280997
  simp only [CollatzResearch.WordTrace]
  refine ⟨156140788071686479923993245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104093858714457653282662163 156140788071686479923993245)
  ·
    refine ⟨58552795526882429971497467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156140788071686479923993245 58552795526882429971497467)
    ·
      refine ⟨87829193290323644957246201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58552795526882429971497467 87829193290323644957246201)
      ·
        refine ⟨65871894967742733717934651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87829193290323644957246201 65871894967742733717934651)
        ·
          refine ⟨98807842451614100576901977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65871894967742733717934651 98807842451614100576901977)
          ·
            refine ⟨74105881838710575432676483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98807842451614100576901977 74105881838710575432676483)
            ·
              refine ⟨111158822758065863149014725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74105881838710575432676483 111158822758065863149014725)
              ·
                refine ⟨20842279267137349340440261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111158822758065863149014725 20842279267137349340440261)
                ·
                  refine ⟨3907927362588253001332549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20842279267137349340440261 3907927362588253001332549)
                  ·
                    refine ⟨732736380485297437749853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3907927362588253001332549 732736380485297437749853)
                    ·
                      rfl

theorem cell23_4280997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 4].length) (baseStart_4280997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4280997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4280997 prefixEnd_4280997 := by exact prefixLift 4280997
  have htrace : WordTrace (prefixWord ++ tailWord_4280997) baseStart_4280997 baseEnd_4280997 := by
    simpa [prefixWord, tailWord_4280997, baseEnd_4280997] using wordTrace_append hprefix tailTrace_4280997
  have hstable : (prefixWord ++ tailWord_4280997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4280997).length < 2 ^ (prefixWord ++ tailWord_4280997).sum := by decide
  have hdescent : baseEnd_4280997 < baseStart_4280997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4280997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281021 : List Nat := [1, 4, 1, 2, 1, 3, 1, 3, 3, 2, 2]
def baseStart_4281021 : Nat := 118140960795 + 4281021 * 2 ^ 59
def prefixEnd_4281021 : Nat := 4983230072969 + 3 ^ 40 * 4281021 * 2
def baseEnd_4281021 : Nat := 2198221464991600219349449

theorem tailTrace_4281021 : CollatzResearch.WordTrace tailWord_4281021 prefixEnd_4281021 2198221464991600219349449 := by
  unfold tailWord_4281021
  simp only [CollatzResearch.WordTrace]
  refine ⟨156141663423599532022866917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104094442282399688015244611 156141663423599532022866917)
  ·
    refine ⟨29276561891924912254287547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156141663423599532022866917 29276561891924912254287547)
    ·
      refine ⟨43914842837887368381431321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29276561891924912254287547 43914842837887368381431321)
      ·
        refine ⟨32936132128415526286073491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43914842837887368381431321 32936132128415526286073491)
        ·
          refine ⟨49404198192623289429110237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32936132128415526286073491 49404198192623289429110237)
          ·
            refine ⟨18526574322233733535916339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49404198192623289429110237 18526574322233733535916339)
            ·
              refine ⟨27789861483350600303874509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18526574322233733535916339 27789861483350600303874509)
              ·
                refine ⟨10421198056256475113952941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27789861483350600303874509 10421198056256475113952941)
                ·
                  refine ⟨3907949271096178167732353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10421198056256475113952941 3907949271096178167732353)
                  ·
                    refine ⟨2930961953322133625799265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3907949271096178167732353 2930961953322133625799265)
                    ·
                      refine ⟨2198221464991600219349449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2930961953322133625799265 2198221464991600219349449)
                      ·
                        rfl

theorem cell23_4281021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_4281021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281021 prefixEnd_4281021 := by exact prefixLift 4281021
  have htrace : WordTrace (prefixWord ++ tailWord_4281021) baseStart_4281021 baseEnd_4281021 := by
    simpa [prefixWord, tailWord_4281021, baseEnd_4281021] using wordTrace_append hprefix tailTrace_4281021
  have hstable : (prefixWord ++ tailWord_4281021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281021).length < 2 ^ (prefixWord ++ tailWord_4281021).sum := by decide
  have hdescent : baseEnd_4281021 < baseStart_4281021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281034 : List Nat := [3, 1, 2, 1, 4, 1, 3, 1, 1, 2, 4]
def baseStart_4281034 : Nat := 118140960795 + 4281034 * 2 ^ 59
def prefixEnd_4281034 : Nat := 4983230072969 + 3 ^ 40 * 4281034 * 2
def baseEnd_4281034 : Nat := 2198228140240108668486889

theorem tailTrace_4281034 : CollatzResearch.WordTrace tailWord_4281034 prefixEnd_4281034 2198228140240108668486889 := by
  unfold tailWord_4281034
  simp only [CollatzResearch.WordTrace]
  refine ⟨39035534393138108810772539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104094758381701623495393437 39035534393138108810772539)
  ·
    refine ⟨58553301589707163216158809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39035534393138108810772539 58553301589707163216158809)
    ·
      refine ⟨43914976192280372412119107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58553301589707163216158809 43914976192280372412119107)
      ·
        refine ⟨65872464288420558618178661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43914976192280372412119107 65872464288420558618178661)
        ·
          refine ⟨12351087054078854740908499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65872464288420558618178661 12351087054078854740908499)
          ·
            refine ⟨18526630581118282111362749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12351087054078854740908499 18526630581118282111362749)
            ·
              refine ⟨6947486467919355791761031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18526630581118282111362749 6947486467919355791761031)
              ·
                refine ⟨10421229701879033687641547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6947486467919355791761031 10421229701879033687641547)
                ·
                  refine ⟨15631844552818550531462321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10421229701879033687641547 15631844552818550531462321)
                  ·
                    refine ⟨11723883414613912898596741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15631844552818550531462321 11723883414613912898596741)
                    ·
                      refine ⟨2198228140240108668486889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11723883414613912898596741 2198228140240108668486889)
                      ·
                        rfl

theorem cell23_4281034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_4281034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281034 prefixEnd_4281034 := by exact prefixLift 4281034
  have htrace : WordTrace (prefixWord ++ tailWord_4281034) baseStart_4281034 baseEnd_4281034 := by
    simpa [prefixWord, tailWord_4281034, baseEnd_4281034] using wordTrace_append hprefix tailTrace_4281034
  have hstable : (prefixWord ++ tailWord_4281034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281034).length < 2 ^ (prefixWord ++ tailWord_4281034).sum := by decide
  have hdescent : baseEnd_4281034 < baseStart_4281034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281040 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 3, 9]
def baseStart_4281040 : Nat := 118140960795 + 4281040 * 2 ^ 59
def prefixEnd_4281040 : Nat := 4983230072969 + 3 ^ 40 * 4281040 * 2
def baseEnd_4281040 : Nat := 732743740374678548337287

theorem tailTrace_4281040 : CollatzResearch.WordTrace tailWord_4281040 prefixEnd_4281040 732743740374678548337287 := by
  unfold tailWord_4281040
  simp only [CollatzResearch.WordTrace]
  refine ⟨78071178205265349133904287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104094904273687132178539049 78071178205265349133904287)
  ·
    refine ⟨117106767307898023700856431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78071178205265349133904287 117106767307898023700856431)
    ·
      refine ⟨175660150961847035551284647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117106767307898023700856431 175660150961847035551284647)
      ·
        refine ⟨263490226442770553326926971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175660150961847035551284647 263490226442770553326926971)
        ·
          refine ⟨395235339664155829990390457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263490226442770553326926971 395235339664155829990390457)
          ·
            refine ⟨296426504748116872492792843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 395235339664155829990390457 296426504748116872492792843)
            ·
              refine ⟨444639757122175308739189265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296426504748116872492792843 444639757122175308739189265)
              ·
                refine ⟨333479817841631481554391949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 444639757122175308739189265 333479817841631481554391949)
                ·
                  refine ⟨125054931690611805582896981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 333479817841631481554391949 125054931690611805582896981)
                  ·
                    refine ⟨732743740374678548337287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 125054931690611805582896981 732743740374678548337287)
                    ·
                      rfl

theorem cell23_4281040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 9].length) (baseStart_4281040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281040 prefixEnd_4281040 := by exact prefixLift 4281040
  have htrace : WordTrace (prefixWord ++ tailWord_4281040) baseStart_4281040 baseEnd_4281040 := by
    simpa [prefixWord, tailWord_4281040, baseEnd_4281040] using wordTrace_append hprefix tailTrace_4281040
  have hstable : (prefixWord ++ tailWord_4281040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281040).length < 2 ^ (prefixWord ++ tailWord_4281040).sum := by decide
  have hdescent : baseEnd_4281040 < baseStart_4281040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281044 : List Nat := [2, 4, 1, 3, 2, 1, 1, 9]
def baseStart_4281044 : Nat := 118140960795 + 4281044 * 2 ^ 59
def prefixEnd_4281044 : Nat := 4983230072969 + 3 ^ 40 * 4281044 * 2
def baseEnd_4281044 : Nat := 81416047223950134420809

theorem tailTrace_4281044 : CollatzResearch.WordTrace tailWord_4281044 prefixEnd_4281044 81416047223950134420809 := by
  unfold tailWord_4281044
  simp only [CollatzResearch.WordTrace]
  refine ⟨78071251151258103475477093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104095001535010804633969457 78071251151258103475477093)
  ·
    refine ⟨14638359590860894401651955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78071251151258103475477093 14638359590860894401651955)
    ·
      refine ⟨21957539386291341602477933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14638359590860894401651955 21957539386291341602477933)
      ·
        refine ⟨8234077269859253100929225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21957539386291341602477933 8234077269859253100929225)
        ·
          refine ⟨6175557952394439825696919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8234077269859253100929225 6175557952394439825696919)
          ·
            refine ⟨9263336928591659738545379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6175557952394439825696919 9263336928591659738545379)
            ·
              refine ⟨13895005392887489607818069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9263336928591659738545379 13895005392887489607818069)
              ·
                refine ⟨81416047223950134420809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13895005392887489607818069 81416047223950134420809)
                ·
                  rfl

theorem cell23_4281044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 9].length) (baseStart_4281044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281044 prefixEnd_4281044 := by exact prefixLift 4281044
  have htrace : WordTrace (prefixWord ++ tailWord_4281044) baseStart_4281044 baseEnd_4281044 := by
    simpa [prefixWord, tailWord_4281044, baseEnd_4281044] using wordTrace_append hprefix tailTrace_4281044
  have hstable : (prefixWord ++ tailWord_4281044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281044).length < 2 ^ (prefixWord ++ tailWord_4281044).sum := by decide
  have hdescent : baseEnd_4281044 < baseStart_4281044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281055 : List Nat := [1, 1, 2, 3, 2, 5, 1, 3, 1, 2, 2]
def baseStart_4281055 : Nat := 118140960795 + 4281055 * 2 ^ 59
def prefixEnd_4281055 : Nat := 4983230072969 + 3 ^ 40 * 4281055 * 2
def baseEnd_4281055 : Nat := 2198238923333853086324293

theorem tailTrace_4281055 : CollatzResearch.WordTrace tailWord_4281055 prefixEnd_4281055 2198238923333853086324293 := by
  unfold tailWord_4281055
  simp only [CollatzResearch.WordTrace]
  refine ⟨156142903505476355829604619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104095269003650903886403079 156142903505476355829604619)
  ·
    refine ⟨234214355258214533744406929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156142903505476355829604619 234214355258214533744406929)
    ·
      refine ⟨175660766443660900308305197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234214355258214533744406929 175660766443660900308305197)
      ·
        refine ⟨65872787416372837615614449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175660766443660900308305197 65872787416372837615614449)
        ·
          refine ⟨49404590562279628211710837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65872787416372837615614449 49404590562279628211710837)
          ·
            refine ⟨4631680365213715144847891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49404590562279628211710837 4631680365213715144847891)
            ·
              refine ⟨6947520547820572717271837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4631680365213715144847891 6947520547820572717271837)
              ·
                refine ⟨2605320205432714768976939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6947520547820572717271837 2605320205432714768976939)
                ·
                  refine ⟨3907980308149072153465409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2605320205432714768976939 3907980308149072153465409)
                  ·
                    refine ⟨2930985231111804115099057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3907980308149072153465409 2930985231111804115099057)
                    ·
                      refine ⟨2198238923333853086324293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2930985231111804115099057 2198238923333853086324293)
                      ·
                        rfl

theorem cell23_4281055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 1, 2, 2].length) (baseStart_4281055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281055 prefixEnd_4281055 := by exact prefixLift 4281055
  have htrace : WordTrace (prefixWord ++ tailWord_4281055) baseStart_4281055 baseEnd_4281055 := by
    simpa [prefixWord, tailWord_4281055, baseEnd_4281055] using wordTrace_append hprefix tailTrace_4281055
  have hstable : (prefixWord ++ tailWord_4281055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281055).length < 2 ^ (prefixWord ++ tailWord_4281055).sum := by decide
  have hdescent : baseEnd_4281055 < baseStart_4281055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281097 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 2, 1, 5]
def baseStart_4281097 : Nat := 118140960795 + 4281097 * 2 ^ 59
def prefixEnd_4281097 : Nat := 4983230072969 + 3 ^ 40 * 4281097 * 2
def baseEnd_4281097 : Nat := 2198260489521341921999099

theorem tailTrace_4281097 : CollatzResearch.WordTrace tailWord_4281097 prefixEnd_4281097 2198260489521341921999099 := by
  unfold tailWord_4281097
  simp only [CollatzResearch.WordTrace]
  refine ⟨156144435371324197002633545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104096290247549464668422363 156144435371324197002633545)
  ·
    refine ⟨117108326528493147751975159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156144435371324197002633545 117108326528493147751975159)
    ·
      refine ⟨175662489792739721627962739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117108326528493147751975159 175662489792739721627962739)
      ·
        refine ⟨263493734689109582441944109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175662489792739721627962739 263493734689109582441944109)
        ·
          refine ⟨98810150508416093415729041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 263493734689109582441944109 98810150508416093415729041)
          ·
            refine ⟨74107612881312070061796781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98810150508416093415729041 74107612881312070061796781)
            ·
              refine ⟨27790354830492026273173793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74107612881312070061796781 27790354830492026273173793)
              ·
                refine ⟨20842766122869019704880345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27790354830492026273173793 20842766122869019704880345)
                ·
                  refine ⟨15632074592151764778660259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20842766122869019704880345 15632074592151764778660259)
                  ·
                    refine ⟨23448111888227647167990389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15632074592151764778660259 23448111888227647167990389)
                    ·
                      refine ⟨2198260489521341921999099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23448111888227647167990389 2198260489521341921999099)
                      ·
                        rfl

theorem cell23_4281097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 1, 5].length) (baseStart_4281097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281097 prefixEnd_4281097 := by exact prefixLift 4281097
  have htrace : WordTrace (prefixWord ++ tailWord_4281097) baseStart_4281097 baseEnd_4281097 := by
    simpa [prefixWord, tailWord_4281097, baseEnd_4281097] using wordTrace_append hprefix tailTrace_4281097
  have hstable : (prefixWord ++ tailWord_4281097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281097).length < 2 ^ (prefixWord ++ tailWord_4281097).sum := by decide
  have hdescent : baseEnd_4281097 < baseStart_4281097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281144 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 2, 3, 3]
def baseStart_4281144 : Nat := 118140960795 + 4281144 * 2 ^ 59
def prefixEnd_4281144 : Nat := 4983230072969 + 3 ^ 40 * 4281144 * 2
def baseEnd_4281144 : Nat := 2198284623112103238111383

theorem tailTrace_4281144 : CollatzResearch.WordTrace tailWord_4281144 prefixEnd_4281144 2198284623112103238111383 := by
  unfold tailWord_4281144
  simp only [CollatzResearch.WordTrace]
  refine ⟨78073074801076962014797243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104097433068102616019729657 78073074801076962014797243)
  ·
    refine ⟨117109612201615443022195865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78073074801076962014797243 117109612201615443022195865)
    ·
      refine ⟨87832209151211582266646899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117109612201615443022195865 87832209151211582266646899)
      ·
        refine ⟨131748313726817373399970349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87832209151211582266646899 131748313726817373399970349)
        ·
          refine ⟨49405617647556515024988881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131748313726817373399970349 49405617647556515024988881)
          ·
            refine ⟨37054213235667386268741661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49405617647556515024988881 37054213235667386268741661)
            ·
              refine ⟨13895329963375269850778123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37054213235667386268741661 13895329963375269850778123)
              ·
                refine ⟨20842994945062904776167185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13895329963375269850778123 20842994945062904776167185)
                ·
                  refine ⟨15632246208797178582125389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20842994945062904776167185 15632246208797178582125389)
                  ·
                    refine ⟨5862092328298941968297021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15632246208797178582125389 5862092328298941968297021)
                    ·
                      refine ⟨2198284623112103238111383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5862092328298941968297021 2198284623112103238111383)
                      ·
                        rfl

theorem cell23_4281144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_4281144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281144 prefixEnd_4281144 := by exact prefixLift 4281144
  have htrace : WordTrace (prefixWord ++ tailWord_4281144) baseStart_4281144 baseEnd_4281144 := by
    simpa [prefixWord, tailWord_4281144, baseEnd_4281144] using wordTrace_append hprefix tailTrace_4281144
  have hstable : (prefixWord ++ tailWord_4281144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281144).length < 2 ^ (prefixWord ++ tailWord_4281144).sum := by decide
  have hdescent : baseEnd_4281144 < baseStart_4281144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281157 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 3, 2, 5]
def baseStart_4281157 : Nat := 118140960795 + 4281157 * 2 ^ 59
def prefixEnd_4281157 : Nat := 4983230072969 + 3 ^ 40 * 4281157 * 2
def baseEnd_4281157 : Nat := 2198291298360611687248823

theorem tailTrace_4281157 : CollatzResearch.WordTrace tailWord_4281157 prefixEnd_4281157 2198291298360611687248823 := by
  unfold tailWord_4281157
  simp only [CollatzResearch.WordTrace]
  refine ⟨156146623751106827249817725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104097749167404551499878483 156146623751106827249817725)
  ·
    refine ⟨58554983906665060218681647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156146623751106827249817725 58554983906665060218681647)
    ·
      refine ⟨87832475859997590328022471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58554983906665060218681647 87832475859997590328022471)
      ·
        refine ⟨131748713789996385492033707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87832475859997590328022471 131748713789996385492033707)
        ·
          refine ⟨197623070684994578238050561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131748713789996385492033707 197623070684994578238050561)
          ·
            refine ⟨148217303013745933678537921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197623070684994578238050561 148217303013745933678537921)
            ·
              refine ⟨111162977260309450258903441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148217303013745933678537921 111162977260309450258903441)
              ·
                refine ⟨83372232945232087694177581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111162977260309450258903441 83372232945232087694177581)
                ·
                  refine ⟨31264587354462032885316593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83372232945232087694177581 31264587354462032885316593)
                  ·
                    refine ⟨23448440515846524663987445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31264587354462032885316593 23448440515846524663987445)
                    ·
                      refine ⟨2198291298360611687248823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23448440515846524663987445 2198291298360611687248823)
                      ·
                        rfl

theorem cell23_4281157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_4281157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281157 prefixEnd_4281157 := by exact prefixLift 4281157
  have htrace : WordTrace (prefixWord ++ tailWord_4281157) baseStart_4281157 baseEnd_4281157 := by
    simpa [prefixWord, tailWord_4281157, baseEnd_4281157] using wordTrace_append hprefix tailTrace_4281157
  have hstable : (prefixWord ++ tailWord_4281157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281157).length < 2 ^ (prefixWord ++ tailWord_4281157).sum := by decide
  have hdescent : baseEnd_4281157 < baseStart_4281157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281164 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 1, 7]
def baseStart_4281164 : Nat := 118140960795 + 4281164 * 2 ^ 59
def prefixEnd_4281164 : Nat := 4983230072969 + 3 ^ 40 * 4281164 * 2
def baseEnd_4281164 : Nat := 732764964241731053287097

theorem tailTrace_4281164 : CollatzResearch.WordTrace tailWord_4281164 prefixEnd_4281164 732764964241731053287097 := by
  unfold tailWord_4281164
  simp only [CollatzResearch.WordTrace]
  refine ⟨78073439531040733722661273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104097919374720978296881697 78073439531040733722661273)
  ·
    refine ⟨58555079648280550291995955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78073439531040733722661273 58555079648280550291995955)
    ·
      refine ⟨87832619472420825437993933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58555079648280550291995955 87832619472420825437993933)
      ·
        refine ⟨32937232302157809539247725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87832619472420825437993933 32937232302157809539247725)
        ·
          refine ⟨12351462113309178577217897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32937232302157809539247725 12351462113309178577217897)
          ·
            refine ⟨9263596584981883932913423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12351462113309178577217897 9263596584981883932913423)
            ·
              refine ⟨13895394877472825899370135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9263596584981883932913423 13895394877472825899370135)
              ·
                refine ⟨20843092316209238849055203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13895394877472825899370135 20843092316209238849055203)
                ·
                  refine ⟨31264638474313858273582805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20843092316209238849055203 31264638474313858273582805)
                  ·
                    refine ⟨732764964241731053287097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31264638474313858273582805 732764964241731053287097)
                    ·
                      rfl

theorem cell23_4281164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_4281164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281164 prefixEnd_4281164 := by exact prefixLift 4281164
  have htrace : WordTrace (prefixWord ++ tailWord_4281164) baseStart_4281164 baseEnd_4281164 := by
    simpa [prefixWord, tailWord_4281164, baseEnd_4281164] using wordTrace_append hprefix tailTrace_4281164
  have hstable : (prefixWord ++ tailWord_4281164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281164).length < 2 ^ (prefixWord ++ tailWord_4281164).sum := by decide
  have hdescent : baseEnd_4281164 < baseStart_4281164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281184 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 4]
def baseStart_4281184 : Nat := 118140960795 + 4281184 * 2 ^ 59
def prefixEnd_4281184 : Nat := 4983230072969 + 3 ^ 40 * 4281184 * 2
def baseEnd_4281184 : Nat := 2198305162338283081611199

theorem tailTrace_4281184 : CollatzResearch.WordTrace tailWord_4281184 prefixEnd_4281184 2198305162338283081611199 := by
  unfold tailWord_4281184
  simp only [CollatzResearch.WordTrace]
  refine ⟨78073804261004505430525303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104098405681339340574033737 78073804261004505430525303)
  ·
    refine ⟨117110706391506758145787955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78073804261004505430525303 117110706391506758145787955)
    ·
      refine ⟨175666059587260137218681933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117110706391506758145787955 175666059587260137218681933)
      ·
        refine ⟨65874772345222551457005725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175666059587260137218681933 65874772345222551457005725)
        ·
          refine ⟨24703039629458456796377147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65874772345222551457005725 24703039629458456796377147)
          ·
            refine ⟨37054559444187685194565721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24703039629458456796377147 37054559444187685194565721)
            ·
              refine ⟨27790919583140763895924291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37054559444187685194565721 27790919583140763895924291)
              ·
                refine ⟨41686379374711145843886437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27790919583140763895924291 41686379374711145843886437)
                ·
                  refine ⟨7816196132758339845728707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41686379374711145843886437 7816196132758339845728707)
                  ·
                    refine ⟨11724294199137509768593061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7816196132758339845728707 11724294199137509768593061)
                    ·
                      refine ⟨2198305162338283081611199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11724294199137509768593061 2198305162338283081611199)
                      ·
                        rfl

theorem cell23_4281184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_4281184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281184 prefixEnd_4281184 := by exact prefixLift 4281184
  have htrace : WordTrace (prefixWord ++ tailWord_4281184) baseStart_4281184 baseEnd_4281184 := by
    simpa [prefixWord, tailWord_4281184, baseEnd_4281184] using wordTrace_append hprefix tailTrace_4281184
  have hstable : (prefixWord ++ tailWord_4281184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281184).length < 2 ^ (prefixWord ++ tailWord_4281184).sum := by decide
  have hdescent : baseEnd_4281184 < baseStart_4281184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281201 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 2, 4, 2]
def baseStart_4281201 : Nat := 118140960795 + 4281201 * 2 ^ 59
def prefixEnd_4281201 : Nat := 4983230072969 + 3 ^ 40 * 4281201 * 2
def baseEnd_4281201 : Nat := 2198313891509409515098621

theorem tailTrace_4281201 : CollatzResearch.WordTrace tailWord_4281201 prefixEnd_4281201 2198313891509409515098621 := by
  unfold tailWord_4281201
  simp only [CollatzResearch.WordTrace]
  refine ⟨156148228562947422764419457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104098819041964948509612971 156148228562947422764419457)
  ·
    refine ⟨117111171422210567073314593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156148228562947422764419457 117111171422210567073314593)
    ·
      refine ⟨87833378566657925304985945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117111171422210567073314593 87833378566657925304985945)
      ·
        refine ⟨65875033924993443978739459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87833378566657925304985945 65875033924993443978739459)
        ·
          refine ⟨98812550887490165968109189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65875033924993443978739459 98812550887490165968109189)
          ·
            refine ⟨18527353291404406119020473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98812550887490165968109189 18527353291404406119020473)
            ·
              refine ⟨13895514968553304589265355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18527353291404406119020473 13895514968553304589265355)
              ·
                refine ⟨20843272452829956883898033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13895514968553304589265355 20843272452829956883898033)
                ·
                  refine ⟨15632454339622467662923525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20843272452829956883898033 15632454339622467662923525)
                  ·
                    refine ⟨2931085188679212686798161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15632454339622467662923525 2931085188679212686798161)
                    ·
                      refine ⟨2198313891509409515098621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2931085188679212686798161 2198313891509409515098621)
                      ·
                        rfl

theorem cell23_4281201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_4281201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281201 prefixEnd_4281201 := by exact prefixLift 4281201
  have htrace : WordTrace (prefixWord ++ tailWord_4281201) baseStart_4281201 baseEnd_4281201 := by
    simpa [prefixWord, tailWord_4281201, baseEnd_4281201] using wordTrace_append hprefix tailTrace_4281201
  have hstable : (prefixWord ++ tailWord_4281201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281201).length < 2 ^ (prefixWord ++ tailWord_4281201).sum := by decide
  have hdescent : baseEnd_4281201 < baseStart_4281201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281224 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 8]
def baseStart_4281224 : Nat := 118140960795 + 4281224 * 2 ^ 59
def prefixEnd_4281224 : Nat := 4983230072969 + 3 ^ 40 * 4281224 * 2
def baseEnd_4281224 : Nat := 244258411284940325012335

theorem tailTrace_4281224 : CollatzResearch.WordTrace tailWord_4281224 prefixEnd_4281224 244258411284940325012335 := by
  unfold tailWord_4281224
  simp only [CollatzResearch.WordTrace]
  refine ⟨78074533720932048846253363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104099378294576065128337817 78074533720932048846253363)
  ·
    refine ⟨117111800581398073269380045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78074533720932048846253363 117111800581398073269380045)
    ·
      refine ⟨43916925218024277476017517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117111800581398073269380045 43916925218024277476017517)
      ·
        refine ⟨16468846956759104053506569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43916925218024277476017517 16468846956759104053506569)
        ·
          refine ⟨12351635217569328040129927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16468846956759104053506569 12351635217569328040129927)
          ·
            refine ⟨18527452826353992060194891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12351635217569328040129927 18527452826353992060194891)
            ·
              refine ⟨27791179239530988090292337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18527452826353992060194891 27791179239530988090292337)
              ·
                refine ⟨20843384429648241067719253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27791179239530988090292337 20843384429648241067719253)
                ·
                  refine ⟨244258411284940325012335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20843384429648241067719253 244258411284940325012335)
                  ·
                    rfl

theorem cell23_4281224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 8].length) (baseStart_4281224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281224 prefixEnd_4281224 := by exact prefixLift 4281224
  have htrace : WordTrace (prefixWord ++ tailWord_4281224) baseStart_4281224 baseEnd_4281224 := by
    simpa [prefixWord, tailWord_4281224, baseEnd_4281224] using wordTrace_append hprefix tailTrace_4281224
  have hstable : (prefixWord ++ tailWord_4281224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281224).length < 2 ^ (prefixWord ++ tailWord_4281224).sum := by decide
  have hdescent : baseEnd_4281224 < baseStart_4281224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281228 : List Nat := [2, 2, 1, 2, 1, 2, 5, 3, 1, 4]
def baseStart_4281228 : Nat := 118140960795 + 4281228 * 2 ^ 59
def prefixEnd_4281228 : Nat := 4983230072969 + 3 ^ 40 * 4281228 * 2
def baseEnd_4281228 : Nat := 732775918495693636486999

theorem tailTrace_4281228 : CollatzResearch.WordTrace tailWord_4281228 prefixEnd_4281228 732775918495693636486999 := by
  unfold tailWord_4281228
  simp only [CollatzResearch.WordTrace]
  refine ⟨78074606666924803187826169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104099475555899737583768225 78074606666924803187826169)
  ·
    refine ⟨58555955000193602390869627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78074606666924803187826169 58555955000193602390869627)
    ·
      refine ⟨87833932500290403586304441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58555955000193602390869627 87833932500290403586304441)
      ·
        refine ⟨65875449375217802689728331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87833932500290403586304441 65875449375217802689728331)
        ·
          refine ⟨98813174062826704034592497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65875449375217802689728331 98813174062826704034592497)
          ·
            refine ⟨74109880547120028025944373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98813174062826704034592497 74109880547120028025944373)
            ·
              refine ⟨6947801301292502627432285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74109880547120028025944373 6947801301292502627432285)
              ·
                refine ⟨2605425487984688485287107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6947801301292502627432285 2605425487984688485287107)
                ·
                  refine ⟨3908138231977032727930661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2605425487984688485287107 3908138231977032727930661)
                  ·
                    refine ⟨732775918495693636486999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3908138231977032727930661 732775918495693636486999)
                    ·
                      rfl

theorem cell23_4281228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 1, 4].length) (baseStart_4281228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281228 prefixEnd_4281228 := by exact prefixLift 4281228
  have htrace : WordTrace (prefixWord ++ tailWord_4281228) baseStart_4281228 baseEnd_4281228 := by
    simpa [prefixWord, tailWord_4281228, baseEnd_4281228] using wordTrace_append hprefix tailTrace_4281228
  have hstable : (prefixWord ++ tailWord_4281228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281228).length < 2 ^ (prefixWord ++ tailWord_4281228).sum := by decide
  have hdescent : baseEnd_4281228 < baseStart_4281228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281245 : List Nat := [1, 4, 2, 1, 2, 1, 5, 2, 1, 4]
def baseStart_4281245 : Nat := 118140960795 + 4281245 * 2 ^ 59
def prefixEnd_4281245 : Nat := 4983230072969 + 3 ^ 40 * 4281245 * 2
def baseEnd_4281245 : Nat := 732778828219402447649473

theorem tailTrace_4281245 : CollatzResearch.WordTrace tailWord_4281245 prefixEnd_4281245 732778828219402447649473 := by
  unfold tailWord_4281245
  simp only [CollatzResearch.WordTrace]
  refine ⟨156149833374788018279021189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104099888916525345519347459 156149833374788018279021189)
  ·
    refine ⟨29278093757772753427316473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156149833374788018279021189 29278093757772753427316473)
    ·
      refine ⟨21958570318329565070487355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29278093757772753427316473 21958570318329565070487355)
      ·
        refine ⟨32937855477494347605731033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21958570318329565070487355 32937855477494347605731033)
        ·
          refine ⟨24703391608120760704298275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32937855477494347605731033 24703391608120760704298275)
          ·
            refine ⟨37055087412181141056447413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24703391608120760704298275 37055087412181141056447413)
            ·
              refine ⟨3473914444891981974041945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37055087412181141056447413 3473914444891981974041945)
              ·
                refine ⟨2605435833668986480531459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3473914444891981974041945 2605435833668986480531459)
                ·
                  refine ⟨3908153750503479720797189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2605435833668986480531459 3908153750503479720797189)
                  ·
                    refine ⟨732778828219402447649473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3908153750503479720797189 732778828219402447649473)
                    ·
                      rfl

theorem cell23_4281245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_4281245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281245 prefixEnd_4281245 := by exact prefixLift 4281245
  have htrace : WordTrace (prefixWord ++ tailWord_4281245) baseStart_4281245 baseEnd_4281245 := by
    simpa [prefixWord, tailWord_4281245, baseEnd_4281245] using wordTrace_append hprefix tailTrace_4281245
  have hstable : (prefixWord ++ tailWord_4281245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281245).length < 2 ^ (prefixWord ++ tailWord_4281245).sum := by decide
  have hdescent : baseEnd_4281245 < baseStart_4281245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281271 : List Nat := [1, 1, 3, 1, 3, 1, 5, 2, 1, 5]
def baseStart_4281271 : Nat := 118140960795 + 4281271 * 2 ^ 59
def prefixEnd_4281271 : Nat := 4983230072969 + 3 ^ 40 * 4281271 * 2
def baseEnd_4281271 : Nat := 732783278385074747074433

theorem tailTrace_4281271 : CollatzResearch.WordTrace tailWord_4281271 prefixEnd_4281271 732783278385074747074433 := by
  unfold tailWord_4281271
  simp only [CollatzResearch.WordTrace]
  refine ⟨156150781672693824719467667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104100521115129216479645111 156150781672693824719467667)
  ·
    refine ⟨234226172509040737079201501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156150781672693824719467667 234226172509040737079201501)
    ·
      refine ⟨87834814690890276404700563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234226172509040737079201501 87834814690890276404700563)
      ·
        refine ⟨131752222036335414607050845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87834814690890276404700563 131752222036335414607050845)
        ·
          refine ⟨49407083263625780477644067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131752222036335414607050845 49407083263625780477644067)
          ·
            refine ⟨74110624895438670716466101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49407083263625780477644067 74110624895438670716466101)
            ·
              refine ⟨6947871083947375379668697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74110624895438670716466101 6947871083947375379668697)
              ·
                refine ⟨5210903312960531534751523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6947871083947375379668697 5210903312960531534751523)
                ·
                  refine ⟨7816354969440797302127285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5210903312960531534751523 7816354969440797302127285)
                  ·
                    refine ⟨732783278385074747074433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7816354969440797302127285 732783278385074747074433)
                    ·
                      rfl

theorem cell23_4281271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 5].length) (baseStart_4281271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281271 prefixEnd_4281271 := by exact prefixLift 4281271
  have htrace : WordTrace (prefixWord ++ tailWord_4281271) baseStart_4281271 baseEnd_4281271 := by
    simpa [prefixWord, tailWord_4281271, baseEnd_4281271] using wordTrace_append hprefix tailTrace_4281271
  have hstable : (prefixWord ++ tailWord_4281271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281271).length < 2 ^ (prefixWord ++ tailWord_4281271).sum := by decide
  have hdescent : baseEnd_4281271 < baseStart_4281271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281345 : List Nat := [1, 2, 4, 1, 2, 2, 4, 1, 1, 2, 3]
def baseStart_4281345 : Nat := 118140960795 + 4281345 * 2 ^ 59
def prefixEnd_4281345 : Nat := 4983230072969 + 3 ^ 40 * 4281345 * 2
def baseEnd_4281345 : Nat := 2198387832723656951697959

theorem tailTrace_4281345 : CollatzResearch.WordTrace tailWord_4281345 prefixEnd_4281345 2198387832723656951697959 := by
  unfold tailWord_4281345
  simp only [CollatzResearch.WordTrace]
  refine ⟨156153480674425735357661489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104102320449617156905107659 156153480674425735357661489)
  ·
    refine ⟨117115110505819301518246117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156153480674425735357661489 117115110505819301518246117)
    ·
      refine ⟨21959083219841119034671147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117115110505819301518246117 21959083219841119034671147)
      ·
        refine ⟨32938624829761678552006721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21959083219841119034671147 32938624829761678552006721)
        ·
          refine ⟨24703968622321258914005041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32938624829761678552006721 24703968622321258914005041)
          ·
            refine ⟨18527976466740944185503781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24703968622321258914005041 18527976466740944185503781)
            ·
              refine ⟨3473995587513927034781959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18527976466740944185503781 3473995587513927034781959)
              ·
                refine ⟨5210993381270890552172939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3473995587513927034781959 5210993381270890552172939)
                ·
                  refine ⟨7816490071906335828259409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5210993381270890552172939 7816490071906335828259409)
                  ·
                    refine ⟨5862367553929751871194557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7816490071906335828259409 5862367553929751871194557)
                    ·
                      refine ⟨2198387832723656951697959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5862367553929751871194557 2198387832723656951697959)
                      ·
                        rfl

theorem cell23_4281345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_4281345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281345 prefixEnd_4281345 := by exact prefixLift 4281345
  have htrace : WordTrace (prefixWord ++ tailWord_4281345) baseStart_4281345 baseEnd_4281345 := by
    simpa [prefixWord, tailWord_4281345, baseEnd_4281345] using wordTrace_append hprefix tailTrace_4281345
  have hstable : (prefixWord ++ tailWord_4281345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281345).length < 2 ^ (prefixWord ++ tailWord_4281345).sum := by decide
  have hdescent : baseEnd_4281345 < baseStart_4281345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281362 : List Nat := [3, 2, 5, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_4281362 : Nat := 118140960795 + 4281362 * 2 ^ 59
def prefixEnd_4281362 : Nat := 4983230072969 + 3 ^ 40 * 4281362 * 2
def baseEnd_4281362 : Nat := 2198396561894783385185381

theorem tailTrace_4281362 : CollatzResearch.WordTrace tailWord_4281362 prefixEnd_4281362 2198396561894783385185381 := by
  unfold tailWord_4281362
  simp only [CollatzResearch.WordTrace]
  refine ⟨39038525178841036815257585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104102733810242764840686893 39038525178841036815257585)
  ·
    refine ⟨29278893884130777611443189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39038525178841036815257585 29278893884130777611443189)
    ·
      refine ⟨2744896301637260401072799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29278893884130777611443189 2744896301637260401072799)
      ·
        refine ⟨4117344452455890601609199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2744896301637260401072799 4117344452455890601609199)
        ·
          refine ⟨6176016678683835902413799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4117344452455890601609199 6176016678683835902413799)
          ·
            refine ⟨9264025018025753853620699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6176016678683835902413799 9264025018025753853620699)
            ·
              refine ⟨13896037527038630780431049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9264025018025753853620699 13896037527038630780431049)
              ·
                refine ⟨10422028145278973085323287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13896037527038630780431049 10422028145278973085323287)
                ·
                  refine ⟨15633042217918459627984931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10422028145278973085323287 15633042217918459627984931)
                  ·
                    refine ⟨23449563326877689441977397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15633042217918459627984931 23449563326877689441977397)
                    ·
                      refine ⟨2198396561894783385185381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23449563326877689441977397 2198396561894783385185381)
                      ·
                        rfl

theorem cell23_4281362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_4281362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281362 prefixEnd_4281362 := by exact prefixLift 4281362
  have htrace : WordTrace (prefixWord ++ tailWord_4281362) baseStart_4281362 baseEnd_4281362 := by
    simpa [prefixWord, tailWord_4281362, baseEnd_4281362] using wordTrace_append hprefix tailTrace_4281362
  have hstable : (prefixWord ++ tailWord_4281362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281362).length < 2 ^ (prefixWord ++ tailWord_4281362).sum := by decide
  have hdescent : baseEnd_4281362 < baseStart_4281362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281401 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 1, 3, 5]
def baseStart_4281401 : Nat := 118140960795 + 4281401 * 2 ^ 59
def prefixEnd_4281401 : Nat := 4983230072969 + 3 ^ 40 * 4281401 * 2
def baseEnd_4281401 : Nat := 2198416587640308732597701

theorem tailTrace_4281401 : CollatzResearch.WordTrace tailWord_4281401 prefixEnd_4281401 2198416587640308732597701 := by
  unfold tailWord_4281401
  simp only [CollatzResearch.WordTrace]
  refine ⟨156155523162222856921700057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104103682108148571281133371 156155523162222856921700057)
  ·
    refine ⟨117116642371667142691275043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156155523162222856921700057 117116642371667142691275043)
    ·
      refine ⟨175674963557500714036912565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117116642371667142691275043 175674963557500714036912565)
      ·
        refine ⟨16469527833515691940960553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 175674963557500714036912565 16469527833515691940960553)
        ·
          refine ⟨12352145875136768955720415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16469527833515691940960553 12352145875136768955720415)
          ·
            refine ⟨18528218812705153433580623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12352145875136768955720415 18528218812705153433580623)
            ·
              refine ⟨27792328219057730150370935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18528218812705153433580623 27792328219057730150370935)
              ·
                refine ⟨41688492328586595225556403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27792328219057730150370935 41688492328586595225556403)
                ·
                  refine ⟨62532738492879892838334605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41688492328586595225556403 62532738492879892838334605)
                  ·
                    refine ⟨23449776934829959814375477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62532738492879892838334605 23449776934829959814375477)
                    ·
                      refine ⟨2198416587640308732597701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23449776934829959814375477 2198416587640308732597701)
                      ·
                        rfl

theorem cell23_4281401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_4281401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281401 prefixEnd_4281401 := by exact prefixLift 4281401
  have htrace : WordTrace (prefixWord ++ tailWord_4281401) baseStart_4281401 baseEnd_4281401 := by
    simpa [prefixWord, tailWord_4281401, baseEnd_4281401] using wordTrace_append hprefix tailTrace_4281401
  have hstable : (prefixWord ++ tailWord_4281401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281401).length < 2 ^ (prefixWord ++ tailWord_4281401).sum := by decide
  have hdescent : baseEnd_4281401 < baseStart_4281401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281415 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 4, 2, 2]
def baseStart_4281415 : Nat := 118140960795 + 4281415 * 2 ^ 59
def prefixEnd_4281415 : Nat := 4983230072969 + 3 ^ 40 * 4281415 * 2
def baseEnd_4281415 : Nat := 2198423776369471677822637

theorem tailTrace_4281415 : CollatzResearch.WordTrace tailWord_4281415 prefixEnd_4281415 2198423776369471677822637 := by
  unfold tailWord_4281415
  simp only [CollatzResearch.WordTrace]
  refine ⟨156156033784172137312709699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104104022522781424875139799 156156033784172137312709699)
  ·
    refine ⟨234234050676258205969064549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156156033784172137312709699 234234050676258205969064549)
    ·
      refine ⟨43918884501798413619199603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 234234050676258205969064549 43918884501798413619199603)
      ·
        refine ⟨65878326752697620428799405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43918884501798413619199603 65878326752697620428799405)
        ·
          refine ⟨24704372532261607660799777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65878326752697620428799405 24704372532261607660799777)
          ·
            refine ⟨18528279399196205745599833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24704372532261607660799777 18528279399196205745599833)
            ·
              refine ⟨13896209549397154309199875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18528279399196205745599833 13896209549397154309199875)
              ·
                refine ⟨20844314324095731463799813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13896209549397154309199875 20844314324095731463799813)
                ·
                  refine ⟨3908308935767949649462465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20844314324095731463799813 3908308935767949649462465)
                  ·
                    refine ⟨2931231701825962237096849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3908308935767949649462465 2931231701825962237096849)
                    ·
                      refine ⟨2198423776369471677822637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2931231701825962237096849 2198423776369471677822637)
                      ·
                        rfl

theorem cell23_4281415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_4281415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281415 prefixEnd_4281415 := by exact prefixLift 4281415
  have htrace : WordTrace (prefixWord ++ tailWord_4281415) baseStart_4281415 baseEnd_4281415 := by
    simpa [prefixWord, tailWord_4281415, baseEnd_4281415] using wordTrace_append hprefix tailTrace_4281415
  have hstable : (prefixWord ++ tailWord_4281415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281415).length < 2 ^ (prefixWord ++ tailWord_4281415).sum := by decide
  have hdescent : baseEnd_4281415 < baseStart_4281415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281431 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 3]
def baseStart_4281431 : Nat := 118140960795 + 4281431 * 2 ^ 59
def prefixEnd_4281431 : Nat := 4983230072969 + 3 ^ 40 * 4281431 * 2
def baseEnd_4281431 : Nat := 2198431992059943615222563

theorem tailTrace_4281431 : CollatzResearch.WordTrace tailWord_4281431 prefixEnd_4281431 2198431992059943615222563 := by
  unfold tailWord_4281431
  simp only [CollatzResearch.WordTrace]
  refine ⟨156156617352114172045292147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104104411568076114696861431 156156617352114172045292147)
  ·
    refine ⟨234234926028171258067938221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156156617352114172045292147 234234926028171258067938221)
    ·
      refine ⟨87838097260564221775476833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234234926028171258067938221 87838097260564221775476833)
      ·
        refine ⟨65878572945423166331607625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87838097260564221775476833 65878572945423166331607625)
        ·
          refine ⟨49408929709067374748705719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65878572945423166331607625 49408929709067374748705719)
          ·
            refine ⟨74113394563601062123058579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49408929709067374748705719 74113394563601062123058579)
            ·
              refine ⟨111170091845401593184587869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74113394563601062123058579 111170091845401593184587869)
              ·
                refine ⟨41688784442025597444220451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111170091845401593184587869 41688784442025597444220451)
                ·
                  refine ⟨62533176663038396166330677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41688784442025597444220451 62533176663038396166330677)
                  ·
                    refine ⟨5862485312159849640593501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62533176663038396166330677 5862485312159849640593501)
                    ·
                      refine ⟨2198431992059943615222563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5862485312159849640593501 2198431992059943615222563)
                      ·
                        rfl

theorem cell23_4281431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_4281431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281431 prefixEnd_4281431 := by exact prefixLift 4281431
  have htrace : WordTrace (prefixWord ++ tailWord_4281431) baseStart_4281431 baseEnd_4281431 := by
    simpa [prefixWord, tailWord_4281431, baseEnd_4281431] using wordTrace_append hprefix tailTrace_4281431
  have hstable : (prefixWord ++ tailWord_4281431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281431).length < 2 ^ (prefixWord ++ tailWord_4281431).sum := by decide
  have hdescent : baseEnd_4281431 < baseStart_4281431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281502 : List Nat := [4, 3, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_4281502 : Nat := 118140960795 + 4281502 * 2 ^ 59
def prefixEnd_4281502 : Nat := 4983230072969 + 3 ^ 40 * 4281502 * 2
def baseEnd_4281502 : Nat := 732822816395470945811579

theorem tailTrace_4281502 : CollatzResearch.WordTrace tailWord_4281502 prefixEnd_4281502 732822816395470945811579 := by
  unfold tailWord_4281502
  simp only [CollatzResearch.WordTrace]
  refine ⟨19519900866857118896390845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104106137956571300780751173 19519900866857118896390845)
  ·
    refine ⟨7319962825071419586146567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19519900866857118896390845 7319962825071419586146567)
    ·
      refine ⟨10979944237607129379219851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7319962825071419586146567 10979944237607129379219851)
      ·
        refine ⟨16469916356410694068829777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10979944237607129379219851 16469916356410694068829777)
        ·
          refine ⟨12352437267308020551622333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16469916356410694068829777 12352437267308020551622333)
          ·
            refine ⟨4632163975240507706858375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12352437267308020551622333 4632163975240507706858375)
            ·
              refine ⟨6948245962860761560287563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4632163975240507706858375 6948245962860761560287563)
              ·
                refine ⟨10422368944291142340431345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6948245962860761560287563 10422368944291142340431345)
                ·
                  refine ⟨7816776708218356755323509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10422368944291142340431345 7816776708218356755323509)
                  ·
                    refine ⟨732822816395470945811579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7816776708218356755323509 732822816395470945811579)
                    ·
                      rfl

theorem cell23_4281502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_4281502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281502 prefixEnd_4281502 := by exact prefixLift 4281502
  have htrace : WordTrace (prefixWord ++ tailWord_4281502) baseStart_4281502 baseEnd_4281502 := by
    simpa [prefixWord, tailWord_4281502, baseEnd_4281502] using wordTrace_append hprefix tailTrace_4281502
  have hstable : (prefixWord ++ tailWord_4281502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281502).length < 2 ^ (prefixWord ++ tailWord_4281502).sum := by decide
  have hdescent : baseEnd_4281502 < baseStart_4281502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281532 : List Nat := [2, 2, 2, 3, 2, 1, 2, 4, 1, 4]
def baseStart_4281532 : Nat := 118140960795 + 4281532 * 2 ^ 59
def prefixEnd_4281532 : Nat := 4983230072969 + 3 ^ 40 * 4281532 * 2
def baseEnd_4281532 : Nat := 732827951202015906686533

theorem tailTrace_4281532 : CollatzResearch.WordTrace tailWord_4281532 prefixEnd_4281532 732827951202015906686533 := by
  unfold tailWord_4281532
  simp only [CollatzResearch.WordTrace]
  refine ⟨78080150562374133147359425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104106867416498844196479233 78080150562374133147359425)
  ·
    refine ⟨58560112921780599860519569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78080150562374133147359425 58560112921780599860519569)
    ·
      refine ⟨43920084691335449895389677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58560112921780599860519569 43920084691335449895389677)
      ·
        refine ⟨16470031759250793710771129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43920084691335449895389677 16470031759250793710771129)
        ·
          refine ⟨12352523819438095283078347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16470031759250793710771129 12352523819438095283078347)
          ·
            refine ⟨18528785729157142924617521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12352523819438095283078347 18528785729157142924617521)
            ·
              refine ⟨13896589296867857193463141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18528785729157142924617521 13896589296867857193463141)
              ·
                refine ⟨2605610493162723223774339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13896589296867857193463141 2605610493162723223774339)
                ·
                  refine ⟨3908415739744084835661509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2605610493162723223774339 3908415739744084835661509)
                  ·
                    refine ⟨732827951202015906686533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3908415739744084835661509 732827951202015906686533)
                    ·
                      rfl

theorem cell23_4281532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_4281532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281532 prefixEnd_4281532 := by exact prefixLift 4281532
  have htrace : WordTrace (prefixWord ++ tailWord_4281532) baseStart_4281532 baseEnd_4281532 := by
    simpa [prefixWord, tailWord_4281532, baseEnd_4281532] using wordTrace_append hprefix tailTrace_4281532
  have hstable : (prefixWord ++ tailWord_4281532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281532).length < 2 ^ (prefixWord ++ tailWord_4281532).sum := by decide
  have hdescent : baseEnd_4281532 < baseStart_4281532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281605 : List Nat := [1, 3, 1, 1, 2, 1, 5, 3, 2, 4]
def baseStart_4281605 : Nat := 118140960795 + 4281605 * 2 ^ 59
def prefixEnd_4281605 : Nat := 4983230072969 + 3 ^ 40 * 4281605 * 2
def baseEnd_4281605 : Nat := 732840445897941978148921

theorem tailTrace_4281605 : CollatzResearch.WordTrace tailWord_4281605 prefixEnd_4281605 732840445897941978148921 := by
  unfold tailWord_4281605
  simp only [CollatzResearch.WordTrace]
  refine ⟨156162963653483799762126269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104108642435655866508084179 156162963653483799762126269)
  ·
    refine ⟨58561111370056424910797351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156162963653483799762126269 58561111370056424910797351)
    ·
      refine ⟨87841667055084637366196027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58561111370056424910797351 87841667055084637366196027)
      ·
        refine ⟨131762500582626956049294041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87841667055084637366196027 131762500582626956049294041)
        ·
          refine ⟨98821875436970217036970531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131762500582626956049294041 98821875436970217036970531)
          ·
            refine ⟨148232813155455325555455797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98821875436970217036970531 148232813155455325555455797)
            ·
              refine ⟨13896826233323936770823981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 148232813155455325555455797 13896826233323936770823981)
              ·
                refine ⟨5211309837496476289058993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13896826233323936770823981 5211309837496476289058993)
                ·
                  refine ⟨3908482378122357216794245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5211309837496476289058993 3908482378122357216794245)
                  ·
                    refine ⟨732840445897941978148921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3908482378122357216794245 732840445897941978148921)
                    ·
                      rfl

theorem cell23_4281605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 4].length) (baseStart_4281605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281605 prefixEnd_4281605 := by exact prefixLift 4281605
  have htrace : WordTrace (prefixWord ++ tailWord_4281605) baseStart_4281605 baseEnd_4281605 := by
    simpa [prefixWord, tailWord_4281605, baseEnd_4281605] using wordTrace_append hprefix tailTrace_4281605
  have hstable : (prefixWord ++ tailWord_4281605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281605).length < 2 ^ (prefixWord ++ tailWord_4281605).sum := by decide
  have hdescent : baseEnd_4281605 < baseStart_4281605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281612 : List Nat := [2, 2, 1, 2, 2, 5, 1, 2, 1, 1, 4]
def baseStart_4281612 : Nat := 118140960795 + 4281612 * 2 ^ 59
def prefixEnd_4281612 : Nat := 4983230072969 + 3 ^ 40 * 4281612 * 2
def baseEnd_4281612 : Nat := 2198524932058407407059231

theorem tailTrace_4281612 : CollatzResearch.WordTrace tailWord_4281612 prefixEnd_4281612 2198524932058407407059231 := by
  unfold tailWord_4281612
  simp only [CollatzResearch.WordTrace]
  refine ⟨78081609482229219978815545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104108812642972293305087393 78081609482229219978815545)
  ·
    refine ⟨58561207111671914984111659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78081609482229219978815545 58561207111671914984111659)
    ·
      refine ⟨87841810667507872476167489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58561207111671914984111659 87841810667507872476167489)
      ·
        refine ⟨65881358000630904357125617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87841810667507872476167489 65881358000630904357125617)
        ·
          refine ⟨49411018500473178267844213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65881358000630904357125617 49411018500473178267844213)
          ·
            refine ⟨4632282984419360462610395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49411018500473178267844213 4632282984419360462610395)
            ·
              refine ⟨6948424476629040693915593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4632282984419360462610395 6948424476629040693915593)
              ·
                refine ⟨5211318357471780520436695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6948424476629040693915593 5211318357471780520436695)
                ·
                  refine ⟨7816977536207670780655043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5211318357471780520436695 7816977536207670780655043)
                  ·
                    refine ⟨11725466304311506170982565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7816977536207670780655043 11725466304311506170982565)
                    ·
                      refine ⟨2198524932058407407059231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11725466304311506170982565 2198524932058407407059231)
                      ·
                        rfl

theorem cell23_4281612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_4281612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281612 prefixEnd_4281612 := by exact prefixLift 4281612
  have htrace : WordTrace (prefixWord ++ tailWord_4281612) baseStart_4281612 baseEnd_4281612 := by
    simpa [prefixWord, tailWord_4281612, baseEnd_4281612] using wordTrace_append hprefix tailTrace_4281612
  have hstable : (prefixWord ++ tailWord_4281612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281612).length < 2 ^ (prefixWord ++ tailWord_4281612).sum := by decide
  have hdescent : baseEnd_4281612 < baseStart_4281612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281629 : List Nat := [1, 4, 2, 3, 1, 2, 3, 1, 1, 1, 4]
def baseStart_4281629 : Nat := 118140960795 + 4281629 * 2 ^ 59
def prefixEnd_4281629 : Nat := 4983230072969 + 3 ^ 40 * 4281629 * 2
def baseEnd_4281629 : Nat := 2198533661229533840546653

theorem tailTrace_4281629 : CollatzResearch.WordTrace tailWord_4281629 prefixEnd_4281629 2198533661229533840546653 := by
  unfold tailWord_4281629
  simp only [CollatzResearch.WordTrace]
  refine ⟨156163839005396851860999941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104109226003597901240666627 156163839005396851860999941)
  ·
    refine ⟨29280719813511909723937489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156163839005396851860999941 29280719813511909723937489)
    ·
      refine ⟨21960539860133932292953117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29280719813511909723937489 21960539860133932292953117)
      ·
        refine ⟨8235202447550224609857419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21960539860133932292953117 8235202447550224609857419)
        ·
          refine ⟨12352803671325336914786129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8235202447550224609857419 12352803671325336914786129)
          ·
            refine ⟨9264602753494002686089597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12352803671325336914786129 9264602753494002686089597)
            ·
              refine ⟨3474226032560251007283599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9264602753494002686089597 3474226032560251007283599)
              ·
                refine ⟨5211339048840376510925399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3474226032560251007283599 5211339048840376510925399)
                ·
                  refine ⟨7817008573260564766388099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5211339048840376510925399 7817008573260564766388099)
                  ·
                    refine ⟨11725512859890847149582149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7817008573260564766388099 11725512859890847149582149)
                    ·
                      refine ⟨2198533661229533840546653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11725512859890847149582149 2198533661229533840546653)
                      ·
                        rfl

theorem cell23_4281629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_4281629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281629 prefixEnd_4281629 := by exact prefixLift 4281629
  have htrace : WordTrace (prefixWord ++ tailWord_4281629) baseStart_4281629 baseEnd_4281629 := by
    simpa [prefixWord, tailWord_4281629, baseEnd_4281629] using wordTrace_append hprefix tailTrace_4281629
  have hstable : (prefixWord ++ tailWord_4281629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281629).length < 2 ^ (prefixWord ++ tailWord_4281629).sum := by decide
  have hdescent : baseEnd_4281629 < baseStart_4281629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281632 : List Nat := [2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 5]
def baseStart_4281632 : Nat := 118140960795 + 4281632 * 2 ^ 59
def prefixEnd_4281632 : Nat := 4983230072969 + 3 ^ 40 * 4281632 * 2
def baseEnd_4281632 : Nat := 2198535201671497328809139

theorem tailTrace_4281632 : CollatzResearch.WordTrace tailWord_4281632 prefixEnd_4281632 2198535201671497328809139 := by
  unfold tailWord_4281632
  simp only [CollatzResearch.WordTrace]
  refine ⟨78081974212192991686679575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104109298949590655582239433 78081974212192991686679575)
  ·
    refine ⟨117122961318289487530019363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78081974212192991686679575 117122961318289487530019363)
    ·
      refine ⟨175684441977434231295029045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117122961318289487530019363 175684441977434231295029045)
      ·
        refine ⟨16470416435384459183908973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 175684441977434231295029045 16470416435384459183908973)
        ·
          refine ⟨6176406163269172193965865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16470416435384459183908973 6176406163269172193965865)
          ·
            refine ⟨4632304622451879145474399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6176406163269172193965865 4632304622451879145474399)
            ·
              refine ⟨6948456933677818718211599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4632304622451879145474399 6948456933677818718211599)
              ·
                refine ⟨10422685400516728077317399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6948456933677818718211599 10422685400516728077317399)
                ·
                  refine ⟨15634028100775092115976099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10422685400516728077317399 15634028100775092115976099)
                  ·
                    refine ⟨23451042151162638173964149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15634028100775092115976099 23451042151162638173964149)
                    ·
                      refine ⟨2198535201671497328809139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23451042151162638173964149 2198535201671497328809139)
                      ·
                        rfl

theorem cell23_4281632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_4281632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281632 prefixEnd_4281632 := by exact prefixLift 4281632
  have htrace : WordTrace (prefixWord ++ tailWord_4281632) baseStart_4281632 baseEnd_4281632 := by
    simpa [prefixWord, tailWord_4281632, baseEnd_4281632] using wordTrace_append hprefix tailTrace_4281632
  have hstable : (prefixWord ++ tailWord_4281632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281632).length < 2 ^ (prefixWord ++ tailWord_4281632).sum := by decide
  have hdescent : baseEnd_4281632 < baseStart_4281632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281662 : List Nat := [4, 2, 1, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_4281662 : Nat := 118140960795 + 4281662 * 2 ^ 59
def prefixEnd_4281662 : Nat := 4983230072969 + 3 ^ 40 * 4281662 * 2
def baseEnd_4281662 : Nat := 2198550606091132211434001

theorem tailTrace_4281662 : CollatzResearch.WordTrace tailWord_4281662 prefixEnd_4281662 2198550606091132211434001 := by
  unfold tailWord_4281662
  simp only [CollatzResearch.WordTrace]
  refine ⟨19520630326784662312118905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104110028409518198997967493 19520630326784662312118905)
  ·
    refine ⟨14640472745088496734089179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19520630326784662312118905 14640472745088496734089179)
    ·
      refine ⟨21960709117632745101133769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14640472745088496734089179 21960709117632745101133769)
      ·
        refine ⟨16470531838224558825850327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21960709117632745101133769 16470531838224558825850327)
        ·
          refine ⟨24705797757336838238775491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16470531838224558825850327 24705797757336838238775491)
          ·
            refine ⟨37058696636005257358163237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24705797757336838238775491 37058696636005257358163237)
            ·
              refine ⟨6948505619250985754655607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37058696636005257358163237 6948505619250985754655607)
              ·
                refine ⟨10422758428876478631983411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6948505619250985754655607 10422758428876478631983411)
                ·
                  refine ⟨15634137643314717947975117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10422758428876478631983411 15634137643314717947975117)
                  ·
                    refine ⟨5862801616243019230490669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15634137643314717947975117 5862801616243019230490669)
                    ·
                      refine ⟨2198550606091132211434001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5862801616243019230490669 2198550606091132211434001)
                      ·
                        rfl

theorem cell23_4281662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_4281662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281662 prefixEnd_4281662 := by exact prefixLift 4281662
  have htrace : WordTrace (prefixWord ++ tailWord_4281662) baseStart_4281662 baseEnd_4281662 := by
    simpa [prefixWord, tailWord_4281662, baseEnd_4281662] using wordTrace_append hprefix tailTrace_4281662
  have hstable : (prefixWord ++ tailWord_4281662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281662).length < 2 ^ (prefixWord ++ tailWord_4281662).sum := by decide
  have hdescent : baseEnd_4281662 < baseStart_4281662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281672 : List Nat := [2, 1, 3, 1, 1, 2, 1, 6, 1, 3, 2]
def baseStart_4281672 : Nat := 118140960795 + 4281672 * 2 ^ 59
def prefixEnd_4281672 : Nat := 4983230072969 + 3 ^ 40 * 4281672 * 2
def baseEnd_4281672 : Nat := 2198555740897677172308955

theorem tailTrace_4281672 : CollatzResearch.WordTrace tailWord_4281672 prefixEnd_4281672 2198555740897677172308955 := by
  unfold tailWord_4281672
  simp only [CollatzResearch.WordTrace]
  refine ⟨78082703672120535102407635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104110271562827380136543513 78082703672120535102407635)
  ·
    refine ⟨117124055508180802653611453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78082703672120535102407635 117124055508180802653611453)
    ·
      refine ⟨43921520815567800995104295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117124055508180802653611453 43921520815567800995104295)
      ·
        refine ⟨65882281223351701492656443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43921520815567800995104295 65882281223351701492656443)
        ·
          refine ⟨98823421835027552238984665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65882281223351701492656443 98823421835027552238984665)
          ·
            refine ⟨74117566376270664179238499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98823421835027552238984665 74117566376270664179238499)
            ·
              refine ⟨111176349564405996268857749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74117566376270664179238499 111176349564405996268857749)
              ·
                refine ⟨5211391385831531075102707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 111176349564405996268857749 5211391385831531075102707)
                ·
                  refine ⟨7817087078747296612654061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5211391385831531075102707 7817087078747296612654061)
                  ·
                    refine ⟨2931407654530236229745273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7817087078747296612654061 2931407654530236229745273)
                    ·
                      refine ⟨2198555740897677172308955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2931407654530236229745273 2198555740897677172308955)
                      ·
                        rfl

theorem cell23_4281672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_4281672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281672 prefixEnd_4281672 := by exact prefixLift 4281672
  have htrace : WordTrace (prefixWord ++ tailWord_4281672) baseStart_4281672 baseEnd_4281672 := by
    simpa [prefixWord, tailWord_4281672, baseEnd_4281672] using wordTrace_append hprefix tailTrace_4281672
  have hstable : (prefixWord ++ tailWord_4281672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281672).length < 2 ^ (prefixWord ++ tailWord_4281672).sum := by decide
  have hdescent : baseEnd_4281672 < baseStart_4281672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281678 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 1, 8]
def baseStart_4281678 : Nat := 118140960795 + 4281678 * 2 ^ 59
def prefixEnd_4281678 : Nat := 4983230072969 + 3 ^ 40 * 4281678 * 2
def baseEnd_4281678 : Nat := 732852940593868049611309

theorem tailTrace_4281678 : CollatzResearch.WordTrace tailWord_4281678 prefixEnd_4281678 732852940593868049611309 := by
  unfold tailWord_4281678
  simp only [CollatzResearch.WordTrace]
  refine ⟨19520703272777416653691711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104110417454812888819689125 19520703272777416653691711)
  ·
    refine ⟨29281054909166124980537567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19520703272777416653691711 29281054909166124980537567)
    ·
      refine ⟨43921582363749187470806351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29281054909166124980537567 43921582363749187470806351)
      ·
        refine ⟨65882373545623781206209527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43921582363749187470806351 65882373545623781206209527)
        ·
          refine ⟨98823560318435671809314291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65882373545623781206209527 98823560318435671809314291)
          ·
            refine ⟨148235340477653507713971437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98823560318435671809314291 148235340477653507713971437)
            ·
              refine ⟨55588252679120065392739289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148235340477653507713971437 55588252679120065392739289)
              ·
                refine ⟨41691189509340049044554467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55588252679120065392739289 41691189509340049044554467)
                ·
                  refine ⟨62536784264010073566831701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41691189509340049044554467 62536784264010073566831701)
                  ·
                    refine ⟨732852940593868049611309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62536784264010073566831701 732852940593868049611309)
                    ·
                      rfl

theorem cell23_4281678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_4281678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281678 prefixEnd_4281678 := by exact prefixLift 4281678
  have htrace : WordTrace (prefixWord ++ tailWord_4281678) baseStart_4281678 baseEnd_4281678 := by
    simpa [prefixWord, tailWord_4281678, baseEnd_4281678] using wordTrace_append hprefix tailTrace_4281678
  have hstable : (prefixWord ++ tailWord_4281678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281678).length < 2 ^ (prefixWord ++ tailWord_4281678).sum := by decide
  have hdescent : baseEnd_4281678 < baseStart_4281678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281688 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 1, 3, 5]
def baseStart_4281688 : Nat := 118140960795 + 4281688 * 2 ^ 59
def prefixEnd_4281688 : Nat := 4983230072969 + 3 ^ 40 * 4281688 * 2
def baseEnd_4281688 : Nat := 2198563956588149109708881

theorem tailTrace_4281688 : CollatzResearch.WordTrace tailWord_4281688 prefixEnd_4281688 2198563956588149109708881 := by
  unfold tailWord_4281688
  simp only [CollatzResearch.WordTrace]
  refine ⟨78082995456091552468698859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104110660608122069958265145 78082995456091552468698859)
  ·
    refine ⟨117124493184137328703048289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78082995456091552468698859 117124493184137328703048289)
    ·
      refine ⟨87843369888102996527286217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117124493184137328703048289 87843369888102996527286217)
      ·
        refine ⟨65882527416077247395464663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87843369888102996527286217 65882527416077247395464663)
        ·
          refine ⟨98823791124115871093196995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65882527416077247395464663 98823791124115871093196995)
          ·
            refine ⟨148235686686173806639795493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98823791124115871093196995 148235686686173806639795493)
            ·
              refine ⟨27794191253657588744961655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148235686686173806639795493 27794191253657588744961655)
              ·
                refine ⟨41691286880486383117442483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27794191253657588744961655 41691286880486383117442483)
                ·
                  refine ⟨62536930320729574676163725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41691286880486383117442483 62536930320729574676163725)
                  ·
                    refine ⟨23451348870273590503561397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62536930320729574676163725 23451348870273590503561397)
                    ·
                      refine ⟨2198563956588149109708881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23451348870273590503561397 2198563956588149109708881)
                      ·
                        rfl

theorem cell23_4281688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_4281688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281688 prefixEnd_4281688 := by exact prefixLift 4281688
  have htrace : WordTrace (prefixWord ++ tailWord_4281688) baseStart_4281688 baseEnd_4281688 := by
    simpa [prefixWord, tailWord_4281688, baseEnd_4281688] using wordTrace_append hprefix tailTrace_4281688
  have hstable : (prefixWord ++ tailWord_4281688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281688).length < 2 ^ (prefixWord ++ tailWord_4281688).sum := by decide
  have hdescent : baseEnd_4281688 < baseStart_4281688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281689 : List Nat := [1, 2, 1, 2, 2, 2, 6, 1, 1, 3, 2]
def baseStart_4281689 : Nat := 118140960795 + 4281689 * 2 ^ 59
def prefixEnd_4281689 : Nat := 4983230072969 + 3 ^ 40 * 4281689 * 2
def baseEnd_4281689 : Nat := 2198564470068803605796377

theorem tailTrace_4281689 : CollatzResearch.WordTrace tailWord_4281689 prefixEnd_4281689 2198564470068803605796377 := by
  unfold tailWord_4281689
  simp only [CollatzResearch.WordTrace]
  refine ⟨156166027385179482108184121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104110684923452988072122747 156166027385179482108184121)
  ·
    refine ⟨117124520538884611581138091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156166027385179482108184121 117124520538884611581138091)
    ·
      refine ⟨175686780808326917371707137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117124520538884611581138091 175686780808326917371707137)
      ·
        refine ⟨131765085606245188028780353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175686780808326917371707137 131765085606245188028780353)
        ·
          refine ⟨98823814204683891021585265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131765085606245188028780353 98823814204683891021585265)
          ·
            refine ⟨74117860653512918266188949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98823814204683891021585265 74117860653512918266188949)
            ·
              refine ⟨3474274718133418043727607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74117860653512918266188949 3474274718133418043727607)
              ·
                refine ⟨5211412077200127065591411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3474274718133418043727607 5211412077200127065591411)
                ·
                  refine ⟨7817118115800190598387117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5211412077200127065591411 7817118115800190598387117)
                  ·
                    refine ⟨2931419293425071474395169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7817118115800190598387117 2931419293425071474395169)
                    ·
                      refine ⟨2198564470068803605796377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2931419293425071474395169 2198564470068803605796377)
                      ·
                        rfl

theorem cell23_4281689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 1, 3, 2].length) (baseStart_4281689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281689 prefixEnd_4281689 := by exact prefixLift 4281689
  have htrace : WordTrace (prefixWord ++ tailWord_4281689) baseStart_4281689 baseEnd_4281689 := by
    simpa [prefixWord, tailWord_4281689, baseEnd_4281689] using wordTrace_append hprefix tailTrace_4281689
  have hstable : (prefixWord ++ tailWord_4281689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281689).length < 2 ^ (prefixWord ++ tailWord_4281689).sum := by decide
  have hdescent : baseEnd_4281689 < baseStart_4281689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281759 : List Nat := [1, 1, 2, 5, 1, 3, 3, 2, 5]
def baseStart_4281759 : Nat := 118140960795 + 4281759 * 2 ^ 59
def prefixEnd_4281759 : Nat := 4983230072969 + 3 ^ 40 * 4281759 * 2
def baseEnd_4281759 : Nat := 244288934857179814657895

theorem tailTrace_4281759 : CollatzResearch.WordTrace tailWord_4281759 prefixEnd_4281759 244288934857179814657895 := by
  unfold tailWord_4281759
  simp only [CollatzResearch.WordTrace]
  refine ⟨156168580494925884063232331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104112386996617256042154887 156168580494925884063232331)
  ·
    refine ⟨234252870742388826094848497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156168580494925884063232331 234252870742388826094848497)
    ·
      refine ⟨175689653056791619571136373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234252870742388826094848497 175689653056791619571136373)
      ·
        refine ⟨16470904974074214334794035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 175689653056791619571136373 16470904974074214334794035)
        ·
          refine ⟨24706357461111321502191053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16470904974074214334794035 24706357461111321502191053)
          ·
            refine ⟨9264884047916745563321645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24706357461111321502191053 9264884047916745563321645)
            ·
              refine ⟨3474331517968779586245617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9264884047916745563321645 3474331517968779586245617)
              ·
                refine ⟨2605748638476584689684213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3474331517968779586245617 2605748638476584689684213)
                ·
                  refine ⟨244288934857179814657895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2605748638476584689684213 244288934857179814657895)
                  ·
                    rfl

theorem cell23_4281759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 5].length) (baseStart_4281759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281759 prefixEnd_4281759 := by exact prefixLift 4281759
  have htrace : WordTrace (prefixWord ++ tailWord_4281759) baseStart_4281759 baseEnd_4281759 := by
    simpa [prefixWord, tailWord_4281759, baseEnd_4281759] using wordTrace_append hprefix tailTrace_4281759
  have hstable : (prefixWord ++ tailWord_4281759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281759).length < 2 ^ (prefixWord ++ tailWord_4281759).sum := by decide
  have hdescent : baseEnd_4281759 < baseStart_4281759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281795 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 3]
def baseStart_4281795 : Nat := 118140960795 + 4281795 * 2 ^ 59
def prefixEnd_4281795 : Nat := 4983230072969 + 3 ^ 40 * 4281795 * 2
def baseEnd_4281795 : Nat := 2198618899018180191070889

theorem tailTrace_4281795 : CollatzResearch.WordTrace tailWord_4281795 prefixEnd_4281795 2198618899018180191070889 := by
  unfold tailWord_4281795
  simp only [CollatzResearch.WordTrace]
  refine ⟨156169893522795462211542839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104113262348530308141028559 156169893522795462211542839)
  ·
    refine ⟨234254840284193193317314259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156169893522795462211542839 234254840284193193317314259)
    ·
      refine ⟨351382260426289789975971389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234254840284193193317314259 351382260426289789975971389)
      ·
        refine ⟨131768347659858671240989271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 351382260426289789975971389 131768347659858671240989271)
        ·
          refine ⟨197652521489788006861483907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131768347659858671240989271 197652521489788006861483907)
          ·
            refine ⟨296478782234682010292225861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197652521489788006861483907 296478782234682010292225861)
            ·
              refine ⟨55589771669002876929792349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 296478782234682010292225861 55589771669002876929792349)
              ·
                refine ⟨20846164375876078848672131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55589771669002876929792349 20846164375876078848672131)
                ·
                  refine ⟨31269246563814118273008197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20846164375876078848672131 31269246563814118273008197)
                  ·
                    refine ⟨5862983730715147176189037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31269246563814118273008197 5862983730715147176189037)
                    ·
                      refine ⟨2198618899018180191070889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5862983730715147176189037 2198618899018180191070889)
                      ·
                        rfl

theorem cell23_4281795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_4281795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281795 prefixEnd_4281795 := by exact prefixLift 4281795
  have htrace : WordTrace (prefixWord ++ tailWord_4281795) baseStart_4281795 baseEnd_4281795 := by
    simpa [prefixWord, tailWord_4281795, baseEnd_4281795] using wordTrace_append hprefix tailTrace_4281795
  have hstable : (prefixWord ++ tailWord_4281795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281795).length < 2 ^ (prefixWord ++ tailWord_4281795).sum := by decide
  have hdescent : baseEnd_4281795 < baseStart_4281795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281846 : List Nat := [5, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3]
def baseStart_4281846 : Nat := 118140960795 + 4281846 * 2 ^ 59
def prefixEnd_4281846 : Nat := 4983230072969 + 3 ^ 40 * 4281846 * 2
def baseEnd_4281846 : Nat := 2198645086531559491533155

theorem tailTrace_4281846 : CollatzResearch.WordTrace tailWord_4281846 prefixEnd_4281846 2198645086531559491533155 := by
  unfold tailWord_4281846
  simp only [CollatzResearch.WordTrace]
  refine ⟨9760734602850668620103087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104114502430407131947766261 9760734602850668620103087)
  ·
    refine ⟨14641101904276002930154631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9760734602850668620103087 14641101904276002930154631)
    ·
      refine ⟨21961652856414004395231947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14641101904276002930154631 21961652856414004395231947)
      ·
        refine ⟨32942479284621006592847921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21961652856414004395231947 32942479284621006592847921)
        ·
          refine ⟨24706859463465754944635941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32942479284621006592847921 24706859463465754944635941)
          ·
            refine ⟨4632536149399829052119239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24706859463465754944635941 4632536149399829052119239)
            ·
              refine ⟨6948804224099743578178859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4632536149399829052119239 6948804224099743578178859)
              ·
                refine ⟨10423206336149615367268289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6948804224099743578178859 10423206336149615367268289)
                ·
                  refine ⟨7817404752112211525451217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10423206336149615367268289 7817404752112211525451217)
                  ·
                    refine ⟨5863053564084158644088413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7817404752112211525451217 5863053564084158644088413)
                    ·
                      refine ⟨2198645086531559491533155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5863053564084158644088413 2198645086531559491533155)
                      ·
                        rfl

theorem cell23_4281846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_4281846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281846 prefixEnd_4281846 := by exact prefixLift 4281846
  have htrace : WordTrace (prefixWord ++ tailWord_4281846) baseStart_4281846 baseEnd_4281846 := by
    simpa [prefixWord, tailWord_4281846, baseEnd_4281846] using wordTrace_append hprefix tailTrace_4281846
  have hstable : (prefixWord ++ tailWord_4281846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281846).length < 2 ^ (prefixWord ++ tailWord_4281846).sum := by decide
  have hdescent : baseEnd_4281846 < baseStart_4281846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281896 : List Nat := [2, 1, 5, 2, 2, 1, 2, 2, 1, 5]
def baseStart_4281896 : Nat := 118140960795 + 4281896 * 2 ^ 59
def prefixEnd_4281896 : Nat := 4983230072969 + 3 ^ 40 * 4281896 * 2
def baseEnd_4281896 : Nat := 732890253521428098635975

theorem tailTrace_4281896 : CollatzResearch.WordTrace tailWord_4281896 prefixEnd_4281896 732890253521428098635975 := by
  unfold tailWord_4281896
  simp only [CollatzResearch.WordTrace]
  refine ⟨78086788647714778230484771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104115718196953037640646361 78086788647714778230484771)
  ·
    refine ⟨117130182971572167345727157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78086788647714778230484771 117130182971572167345727157)
    ·
      refine ⟨10980954653584890688661921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117130182971572167345727157 10980954653584890688661921)
      ·
        refine ⟨8235715990188668016496441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10980954653584890688661921 8235715990188668016496441)
        ·
          refine ⟨6176786992641501012372331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8235715990188668016496441 6176786992641501012372331)
          ·
            refine ⟨9265180488962251518558497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6176786992641501012372331 9265180488962251518558497)
            ·
              refine ⟨6948885366721688638918873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9265180488962251518558497 6948885366721688638918873)
              ·
                refine ⟨5211664025041266479189155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6948885366721688638918873 5211664025041266479189155)
                ·
                  refine ⟨7817496037561899718783733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5211664025041266479189155 7817496037561899718783733)
                  ·
                    refine ⟨732890253521428098635975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7817496037561899718783733 732890253521428098635975)
                    ·
                      rfl

theorem cell23_4281896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_4281896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281896 prefixEnd_4281896 := by exact prefixLift 4281896
  have htrace : WordTrace (prefixWord ++ tailWord_4281896) baseStart_4281896 baseEnd_4281896 := by
    simpa [prefixWord, tailWord_4281896, baseEnd_4281896] using wordTrace_append hprefix tailTrace_4281896
  have hstable : (prefixWord ++ tailWord_4281896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281896).length < 2 ^ (prefixWord ++ tailWord_4281896).sum := by decide
  have hdescent : baseEnd_4281896 < baseStart_4281896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281919 : List Nat := [1, 1, 2, 2, 3, 3, 2, 3, 1, 2, 3]
def baseStart_4281919 : Nat := 118140960795 + 4281919 * 2 ^ 59
def prefixEnd_4281919 : Nat := 4983230072969 + 3 ^ 40 * 4281919 * 2
def baseEnd_4281919 : Nat := 2198682570619337705920319

theorem tailTrace_4281919 : CollatzResearch.WordTrace tailWord_4281919 prefixEnd_4281919 2198682570619337705920319 := by
  unfold tailWord_4281919
  simp only [CollatzResearch.WordTrace]
  refine ⟨156174416174346231389056811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104116277449564154259371207 156174416174346231389056811)
  ·
    refine ⟨234261624261519347083585217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156174416174346231389056811 234261624261519347083585217)
    ·
      refine ⟨175696218196139510312688913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234261624261519347083585217 175696218196139510312688913)
      ·
        refine ⟨131772163647104632734516685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175696218196139510312688913 131772163647104632734516685)
        ·
          refine ⟨49414561367664237275443757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131772163647104632734516685 49414561367664237275443757)
          ·
            refine ⟨18530460512874088978291409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49414561367664237275443757 18530460512874088978291409)
            ·
              refine ⟨13897845384655566733718557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18530460512874088978291409 13897845384655566733718557)
              ·
                refine ⟨5211692019245837525144459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13897845384655566733718557 5211692019245837525144459)
                ·
                  refine ⟨7817538028868756287716689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5211692019245837525144459 7817538028868756287716689)
                  ·
                    refine ⟨5863153521651567215787517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7817538028868756287716689 5863153521651567215787517)
                    ·
                      refine ⟨2198682570619337705920319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5863153521651567215787517 2198682570619337705920319)
                      ·
                        rfl

theorem cell23_4281919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 2, 3].length) (baseStart_4281919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281919 prefixEnd_4281919 := by exact prefixLift 4281919
  have htrace : WordTrace (prefixWord ++ tailWord_4281919) baseStart_4281919 baseEnd_4281919 := by
    simpa [prefixWord, tailWord_4281919, baseEnd_4281919] using wordTrace_append hprefix tailTrace_4281919
  have hstable : (prefixWord ++ tailWord_4281919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281919).length < 2 ^ (prefixWord ++ tailWord_4281919).sum := by decide
  have hdescent : baseEnd_4281919 < baseStart_4281919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281935 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 2, 7]
def baseStart_4281935 : Nat := 118140960795 + 4281935 * 2 ^ 59
def prefixEnd_4281935 : Nat := 4983230072969 + 3 ^ 40 * 4281935 * 2
def baseEnd_4281935 : Nat := 732896928769936547773415

theorem tailTrace_4281935 : CollatzResearch.WordTrace tailWord_4281935 prefixEnd_4281935 732896928769936547773415 := by
  unfold tailWord_4281935
  simp only [CollatzResearch.WordTrace]
  refine ⟨156174999742288266121639259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104116666494858844081092839 156174999742288266121639259)
  ·
    refine ⟨234262499613432399182458889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156174999742288266121639259 234262499613432399182458889)
    ·
      refine ⟨175696874710074299386844167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234262499613432399182458889 175696874710074299386844167)
      ·
        refine ⟨263545312065111449080266251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175696874710074299386844167 263545312065111449080266251)
        ·
          refine ⟨395317968097667173620399377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263545312065111449080266251 395317968097667173620399377)
          ·
            refine ⟨296488476073250380215299533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 395317968097667173620399377 296488476073250380215299533)
            ·
              refine ⟨111183178527468892580737325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 296488476073250380215299533 111183178527468892580737325)
              ·
                refine ⟨41693691947800834717776497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111183178527468892580737325 41693691947800834717776497)
                ·
                  refine ⟨31270268960850626038332373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41693691947800834717776497 31270268960850626038332373)
                  ·
                    refine ⟨732896928769936547773415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31270268960850626038332373 732896928769936547773415)
                    ·
                      rfl

theorem cell23_4281935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 7].length) (baseStart_4281935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281935 prefixEnd_4281935 := by exact prefixLift 4281935
  have htrace : WordTrace (prefixWord ++ tailWord_4281935) baseStart_4281935 baseEnd_4281935 := by
    simpa [prefixWord, tailWord_4281935, baseEnd_4281935] using wordTrace_append hprefix tailTrace_4281935
  have hstable : (prefixWord ++ tailWord_4281935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281935).length < 2 ^ (prefixWord ++ tailWord_4281935).sum := by decide
  have hdescent : baseEnd_4281935 < baseStart_4281935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4281966 : List Nat := [4, 1, 2, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_4281966 : Nat := 118140960795 + 4281966 * 2 ^ 59
def prefixEnd_4281966 : Nat := 4983230072969 + 3 ^ 40 * 4281966 * 2
def baseEnd_4281966 : Nat := 2198706704210099022032603

theorem tailTrace_4281966 : CollatzResearch.WordTrace tailWord_4281966 prefixEnd_4281966 2198706704210099022032603 := by
  unfold tailWord_4281966
  simp only [CollatzResearch.WordTrace]
  refine ⟨19522016300646994802002219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104117420270117305610678501 19522016300646994802002219)
  ·
    refine ⟨29283024450970492203003329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19522016300646994802002219 29283024450970492203003329)
    ·
      refine ⟨21962268338227869152252497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29283024450970492203003329 21962268338227869152252497)
      ·
        refine ⟨16471701253670901864189373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21962268338227869152252497 16471701253670901864189373)
        ·
          refine ⟨6176887970126588199071015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16471701253670901864189373 6176887970126588199071015)
          ·
            refine ⟨9265331955189882298606523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6176887970126588199071015 9265331955189882298606523)
            ·
              refine ⟨13897997932784823447909785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9265331955189882298606523 13897997932784823447909785)
              ·
                refine ⟨10423498449588617585932339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13897997932784823447909785 10423498449588617585932339)
                ·
                  refine ⟨15635247674382926378898509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10423498449588617585932339 15635247674382926378898509)
                  ·
                    refine ⟨5863217877893597392086941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15635247674382926378898509 5863217877893597392086941)
                    ·
                      refine ⟨2198706704210099022032603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5863217877893597392086941 2198706704210099022032603)
                      ·
                        rfl

theorem cell23_4281966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_4281966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281966 prefixEnd_4281966 := by exact prefixLift 4281966
  have htrace : WordTrace (prefixWord ++ tailWord_4281966) baseStart_4281966 baseEnd_4281966 := by
    simpa [prefixWord, tailWord_4281966, baseEnd_4281966] using wordTrace_append hprefix tailTrace_4281966
  have hstable : (prefixWord ++ tailWord_4281966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281966).length < 2 ^ (prefixWord ++ tailWord_4281966).sum := by decide
  have hdescent : baseEnd_4281966 < baseStart_4281966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
