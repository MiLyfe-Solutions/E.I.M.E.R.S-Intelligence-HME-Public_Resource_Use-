import V185TrunkScan22Chunk075

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_682996 : List Nat := [2, 6, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_682996 : Nat := 118140960795 + 682996 * 2 ^ 59
def prefixEnd_682996 : Nat := 4983230072969 + 3 ^ 40 * 682996 * 2
def baseEnd_682996 : Nat := 233803488732210005805977

theorem tailTrace_682996 : CollatzResearch.WordTrace tailWord_682996 prefixEnd_682996 233803488732210005805977 := by
  unfold tailWord_682996
  simp only [CollatzResearch.WordTrace]
  refine ⟨12455455316814806637606421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16607273755753075516808561 12455455316814806637606421)
  ·
    refine ⟨583849467975694061137801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12455455316814806637606421 583849467975694061137801)
    ·
      refine ⟨437887100981770545853351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 583849467975694061137801 437887100981770545853351)
      ·
        refine ⟨656830651472655818780027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437887100981770545853351 656830651472655818780027)
        ·
          refine ⟨985245977208983728170041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656830651472655818780027 985245977208983728170041)
          ·
            refine ⟨738934482906737796127531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 985245977208983728170041 738934482906737796127531)
            ·
              refine ⟨1108401724360106694191297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 738934482906737796127531 1108401724360106694191297)
              ·
                refine ⟨831301293270080020643473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1108401724360106694191297 831301293270080020643473)
                ·
                  refine ⟨623475969952560015482605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 831301293270080020643473 623475969952560015482605)
                  ·
                    refine ⟨233803488732210005805977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 623475969952560015482605 233803488732210005805977)
                    ·
                      rfl

theorem cell22_682996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_682996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682996 prefixEnd_682996 := by exact prefixLift 682996
  have htrace : WordTrace (prefixWord ++ tailWord_682996) baseStart_682996 baseEnd_682996 := by
    simpa [prefixWord, tailWord_682996, baseEnd_682996] using wordTrace_append hprefix tailTrace_682996
  have hstable : (prefixWord ++ tailWord_682996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682996).length < 2 ^ (prefixWord ++ tailWord_682996).sum := by decide
  have hdescent : baseEnd_682996 < baseStart_682996 := by decide
  rcases family_descends (prefixWord ++ tailWord_682996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683031 : List Nat := [1, 1, 3, 5, 1, 1, 2, 2, 6]
def baseStart_683031 : Nat := 118140960795 + 683031 * 2 ^ 59
def prefixEnd_683031 : Nat := 4983230072969 + 3 ^ 40 * 683031 * 2
def baseEnd_683031 : Nat := 77938489982493860393623

theorem tailTrace_683031 : CollatzResearch.WordTrace tailWord_683031 prefixEnd_683031 77938489982493860393623 := by
  unfold tailWord_683031
  simp only [CollatzResearch.WordTrace]
  refine ⟨24912187188502814252736947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16608124792335209501824631 24912187188502814252736947)
  ·
    refine ⟨37368280782754221379105421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24912187188502814252736947 37368280782754221379105421)
    ·
      refine ⟨14013105293532833017164533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37368280782754221379105421 14013105293532833017164533)
      ·
        refine ⟨1313728621268703095359175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14013105293532833017164533 1313728621268703095359175)
        ·
          refine ⟨1970592931903054643038763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1313728621268703095359175 1970592931903054643038763)
          ·
            refine ⟨2955889397854581964558145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1970592931903054643038763 2955889397854581964558145)
            ·
              refine ⟨2216917048390936473418609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2955889397854581964558145 2216917048390936473418609)
              ·
                refine ⟨1662687786293202355063957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2216917048390936473418609 1662687786293202355063957)
                ·
                  refine ⟨77938489982493860393623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1662687786293202355063957 77938489982493860393623)
                  ·
                    rfl

theorem cell22_683031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 6].length) (baseStart_683031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683031 prefixEnd_683031 := by exact prefixLift 683031
  have htrace : WordTrace (prefixWord ++ tailWord_683031) baseStart_683031 baseEnd_683031 := by
    simpa [prefixWord, tailWord_683031, baseEnd_683031] using wordTrace_append hprefix tailTrace_683031
  have hstable : (prefixWord ++ tailWord_683031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683031).length < 2 ^ (prefixWord ++ tailWord_683031).sum := by decide
  have hdescent : baseEnd_683031 < baseStart_683031 := by decide
  rcases family_descends (prefixWord ++ tailWord_683031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683065 : List Nat := [1, 2, 1, 5, 2, 2, 3, 2, 4]
def baseStart_683065 : Nat := 118140960795 + 683065 * 2 ^ 59
def prefixEnd_683065 : Nat := 4983230072969 + 3 ^ 40 * 683065 * 2
def baseEnd_683065 : Nat := 77942369614105608610255

theorem tailTrace_683065 : CollatzResearch.WordTrace tailWord_683065 prefixEnd_683065 77942369614105608610255 := by
  unfold tailWord_683065
  simp only [CollatzResearch.WordTrace]
  refine ⟨24913427270379638059474649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16608951513586425372983099 24913427270379638059474649)
  ·
    refine ⟨18685070452784728544605987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24913427270379638059474649 18685070452784728544605987)
    ·
      refine ⟨28027605679177092816908981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18685070452784728544605987 28027605679177092816908981)
      ·
        refine ⟨2627588032422852451585217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28027605679177092816908981 2627588032422852451585217)
        ·
          refine ⟨1970691024317139338688913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2627588032422852451585217 1970691024317139338688913)
          ·
            refine ⟨1478018268237854504016685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1970691024317139338688913 1478018268237854504016685)
            ·
              refine ⟨554256850589195439006257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1478018268237854504016685 554256850589195439006257)
              ·
                refine ⟨415692637941896579254693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 554256850589195439006257 415692637941896579254693)
                ·
                  refine ⟨77942369614105608610255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 415692637941896579254693 77942369614105608610255)
                  ·
                    rfl

theorem cell22_683065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 4].length) (baseStart_683065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683065 prefixEnd_683065 := by exact prefixLift 683065
  have htrace : WordTrace (prefixWord ++ tailWord_683065) baseStart_683065 baseEnd_683065 := by
    simpa [prefixWord, tailWord_683065, baseEnd_683065] using wordTrace_append hprefix tailTrace_683065
  have hstable : (prefixWord ++ tailWord_683065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683065).length < 2 ^ (prefixWord ++ tailWord_683065).sum := by decide
  have hdescent : baseEnd_683065 < baseStart_683065 := by decide
  rcases family_descends (prefixWord ++ tailWord_683065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683168 : List Nat := [2, 1, 1, 4, 2, 1, 3, 3, 1, 4]
def baseStart_683168 : Nat := 118140960795 + 683168 * 2 ^ 59
def prefixEnd_683168 : Nat := 4983230072969 + 3 ^ 40 * 683168 * 2
def baseEnd_683168 : Nat := 233862367847258890505449

theorem tailTrace_683168 : CollatzResearch.WordTrace tailWord_683168 prefixEnd_683168 233862367847258890505449 := by
  unfold tailWord_683168
  simp only [CollatzResearch.WordTrace]
  refine ⟨12458591994503243325237079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16611455992670991100316105 12458591994503243325237079)
  ·
    refine ⟨18687887991754864987855619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12458591994503243325237079 18687887991754864987855619)
    ·
      refine ⟨28031831987632297481783429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18687887991754864987855619 28031831987632297481783429)
      ·
        refine ⟨5255968497681055777834393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28031831987632297481783429 5255968497681055777834393)
        ·
          refine ⟨3941976373260791833375795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5255968497681055777834393 3941976373260791833375795)
          ·
            refine ⟨5912964559891187750063693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3941976373260791833375795 5912964559891187750063693)
            ·
              refine ⟨2217361709959195406273885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5912964559891187750063693 2217361709959195406273885)
              ·
                refine ⟨831510641234698277352707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2217361709959195406273885 831510641234698277352707)
                ·
                  refine ⟨1247265961852047416029061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831510641234698277352707 1247265961852047416029061)
                  ·
                    refine ⟨233862367847258890505449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1247265961852047416029061 233862367847258890505449)
                    ·
                      rfl

theorem cell22_683168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 1, 4].length) (baseStart_683168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683168 prefixEnd_683168 := by exact prefixLift 683168
  have htrace : WordTrace (prefixWord ++ tailWord_683168) baseStart_683168 baseEnd_683168 := by
    simpa [prefixWord, tailWord_683168, baseEnd_683168] using wordTrace_append hprefix tailTrace_683168
  have hstable : (prefixWord ++ tailWord_683168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683168).length < 2 ^ (prefixWord ++ tailWord_683168).sum := by decide
  have hdescent : baseEnd_683168 < baseStart_683168 := by decide
  rcases family_descends (prefixWord ++ tailWord_683168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683183 : List Nat := [1, 1, 2, 1, 2, 3, 4, 4, 4]
def baseStart_683183 : Nat := 118140960795 + 683183 * 2 ^ 59
def prefixEnd_683183 : Nat := 4983230072969 + 3 ^ 40 * 683183 * 2
def baseEnd_683183 : Nat := 77955834217934617126801

theorem tailTrace_683183 : CollatzResearch.WordTrace tailWord_683183 prefixEnd_683183 77955834217934617126801 := by
  unfold tailWord_683183
  simp only [CollatzResearch.WordTrace]
  refine ⟨24917731083952144212270203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16611820722634762808180135 24917731083952144212270203)
  ·
    refine ⟨37376596625928216318405305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24917731083952144212270203 37376596625928216318405305)
    ·
      refine ⟨28032447469446162238803979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37376596625928216318405305 28032447469446162238803979)
      ·
        refine ⟨42048671204169243358205969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28032447469446162238803979 42048671204169243358205969)
        ·
          refine ⟨31536503403126932518654477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42048671204169243358205969 31536503403126932518654477)
          ·
            refine ⟨11826188776172599694495429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31536503403126932518654477 11826188776172599694495429)
            ·
              refine ⟨2217410395532362442717893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11826188776172599694495429 2217410395532362442717893)
              ·
                refine ⟨415764449162317958009605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2217410395532362442717893 415764449162317958009605)
                ·
                  refine ⟨77955834217934617126801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 415764449162317958009605 77955834217934617126801)
                  ·
                    rfl

theorem cell22_683183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 4].length) (baseStart_683183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683183 prefixEnd_683183 := by exact prefixLift 683183
  have htrace : WordTrace (prefixWord ++ tailWord_683183) baseStart_683183 baseEnd_683183 := by
    simpa [prefixWord, tailWord_683183, baseEnd_683183] using wordTrace_append hprefix tailTrace_683183
  have hstable : (prefixWord ++ tailWord_683183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683183).length < 2 ^ (prefixWord ++ tailWord_683183).sum := by decide
  have hdescent : baseEnd_683183 < baseStart_683183 := by decide
  rcases family_descends (prefixWord ++ tailWord_683183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683290 : List Nat := [3, 1, 1, 3, 3, 2, 2, 2, 5]
def baseStart_683290 : Nat := 118140960795 + 683290 * 2 ^ 59
def prefixEnd_683290 : Nat := 4983230072969 + 3 ^ 40 * 683290 * 2
def baseEnd_683290 : Nat := 77968043646830412985025

theorem tailTrace_683290 : CollatzResearch.WordTrace tailWord_683290 prefixEnd_683290 77968043646830412985025 := by
  unfold tailWord_683290
  simp only [CollatzResearch.WordTrace]
  refine ⟨6230408423641125371603831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16614422463043000990943549 6230408423641125371603831)
  ·
    refine ⟨9345612635461688057405747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6230408423641125371603831 9345612635461688057405747)
    ·
      refine ⟨14018418953192532086108621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9345612635461688057405747 14018418953192532086108621)
      ·
        refine ⟨5256907107447199532290733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14018418953192532086108621 5256907107447199532290733)
        ·
          refine ⟨1971340165292699824609025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5256907107447199532290733 1971340165292699824609025)
          ·
            refine ⟨1478505123969524868456769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1971340165292699824609025 1478505123969524868456769)
            ·
              refine ⟨1108878842977143651342577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1478505123969524868456769 1108878842977143651342577)
              ·
                refine ⟨831659132232857738506933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1108878842977143651342577 831659132232857738506933)
                ·
                  refine ⟨77968043646830412985025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 831659132232857738506933 77968043646830412985025)
                  ·
                    rfl

theorem cell22_683290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_683290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683290 prefixEnd_683290 := by exact prefixLift 683290
  have htrace : WordTrace (prefixWord ++ tailWord_683290) baseStart_683290 baseEnd_683290 := by
    simpa [prefixWord, tailWord_683290, baseEnd_683290] using wordTrace_append hprefix tailTrace_683290
  have hstable : (prefixWord ++ tailWord_683290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683290).length < 2 ^ (prefixWord ++ tailWord_683290).sum := by decide
  have hdescent : baseEnd_683290 < baseStart_683290 := by decide
  rcases family_descends (prefixWord ++ tailWord_683290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683335 : List Nat := [1, 1, 4, 1, 2, 3, 1, 5, 4]
def baseStart_683335 : Nat := 118140960795 + 683335 * 2 ^ 59
def prefixEnd_683335 : Nat := 4983230072969 + 3 ^ 40 * 683335 * 2
def baseEnd_683335 : Nat := 77973178453375373859979

theorem tailTrace_683335 : CollatzResearch.WordTrace tailWord_683335 prefixEnd_683335 77973178453375373859979 := by
  unfold tailWord_683335
  simp only [CollatzResearch.WordTrace]
  refine ⟨24923274979401474171803459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16615516652934316114535639 24923274979401474171803459)
  ·
    refine ⟨37384912469102211257705189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24923274979401474171803459 37384912469102211257705189)
    ·
      refine ⟨7009671087956664610819723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37384912469102211257705189 7009671087956664610819723)
      ·
        refine ⟨10514506631934996916229585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7009671087956664610819723 10514506631934996916229585)
        ·
          refine ⟨7885879973951247687172189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10514506631934996916229585 7885879973951247687172189)
          ·
            refine ⟨2957204990231717882689571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7885879973951247687172189 2957204990231717882689571)
            ·
              refine ⟨4435807485347576824034357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2957204990231717882689571 4435807485347576824034357)
              ·
                refine ⟨415856951751335327253221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4435807485347576824034357 415856951751335327253221)
                ·
                  refine ⟨77973178453375373859979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 415856951751335327253221 77973178453375373859979)
                  ·
                    rfl

theorem cell22_683335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 4].length) (baseStart_683335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683335 prefixEnd_683335 := by exact prefixLift 683335
  have htrace : WordTrace (prefixWord ++ tailWord_683335) baseStart_683335 baseEnd_683335 := by
    simpa [prefixWord, tailWord_683335, baseEnd_683335] using wordTrace_append hprefix tailTrace_683335
  have hstable : (prefixWord ++ tailWord_683335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683335).length < 2 ^ (prefixWord ++ tailWord_683335).sum := by decide
  have hdescent : baseEnd_683335 < baseStart_683335 := by decide
  rcases family_descends (prefixWord ++ tailWord_683335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683341 : List Nat := [1, 6, 1, 3, 2, 1, 1, 2, 5]
def baseStart_683341 : Nat := 118140960795 + 683341 * 2 ^ 59
def prefixEnd_683341 : Nat := 4983230072969 + 3 ^ 40 * 683341 * 2
def baseEnd_683341 : Nat := 77973863094248035309973

theorem tailTrace_683341 : CollatzResearch.WordTrace tailWord_683341 prefixEnd_683341 77973863094248035309973 := by
  unfold tailWord_683341
  simp only [CollatzResearch.WordTrace]
  refine ⟨24923493817379737196521877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16615662544919824797681251 24923493817379737196521877)
  ·
    refine ⟨1168288772689675181086963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24923493817379737196521877 1168288772689675181086963)
    ·
      refine ⟨1752433159034512771630445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1168288772689675181086963 1752433159034512771630445)
      ·
        refine ⟨657162434637942289361417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1752433159034512771630445 657162434637942289361417)
        ·
          refine ⟨492871825978456717021063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 657162434637942289361417 492871825978456717021063)
          ·
            refine ⟨739307738967685075531595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492871825978456717021063 739307738967685075531595)
            ·
              refine ⟨1108961608451527613297393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 739307738967685075531595 1108961608451527613297393)
              ·
                refine ⟨831721206338645709973045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1108961608451527613297393 831721206338645709973045)
                ·
                  refine ⟨77973863094248035309973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 831721206338645709973045 77973863094248035309973)
                  ·
                    rfl

theorem cell22_683341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_683341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683341 prefixEnd_683341 := by exact prefixLift 683341
  have htrace : WordTrace (prefixWord ++ tailWord_683341) baseStart_683341 baseEnd_683341 := by
    simpa [prefixWord, tailWord_683341, baseEnd_683341] using wordTrace_append hprefix tailTrace_683341
  have hstable : (prefixWord ++ tailWord_683341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683341).length < 2 ^ (prefixWord ++ tailWord_683341).sum := by decide
  have hdescent : baseEnd_683341 < baseStart_683341 := by decide
  rcases family_descends (prefixWord ++ tailWord_683341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683367 : List Nat := [1, 1, 5, 1, 4, 2, 1, 1, 1, 5]
def baseStart_683367 : Nat := 118140960795 + 683367 * 2 ^ 59
def prefixEnd_683367 : Nat := 4983230072969 + 3 ^ 40 * 683367 * 2
def baseEnd_683367 : Nat := 233930489614088704779839

theorem tailTrace_683367 : CollatzResearch.WordTrace tailWord_683367 prefixEnd_683367 233930489614088704779839 := by
  unfold tailWord_683367
  simp only [CollatzResearch.WordTrace]
  refine ⟨24924442115285543636968355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16616294743523695757978903 24924442115285543636968355)
  ·
    refine ⟨37386663172928315455452533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24924442115285543636968355 37386663172928315455452533)
    ·
      refine ⟨3504999672462029573948675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37386663172928315455452533 3504999672462029573948675)
      ·
        refine ⟨5257499508693044360923013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3504999672462029573948675 5257499508693044360923013)
        ·
          refine ⟨985781157879945817673065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5257499508693044360923013 985781157879945817673065)
          ·
            refine ⟨739335868409959363254799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 985781157879945817673065 739335868409959363254799)
            ·
              refine ⟨1109003802614939044882199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 739335868409959363254799 1109003802614939044882199)
              ·
                refine ⟨1663505703922408567323299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1109003802614939044882199 1663505703922408567323299)
                ·
                  refine ⟨2495258555883612850984949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1663505703922408567323299 2495258555883612850984949)
                  ·
                    refine ⟨233930489614088704779839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2495258555883612850984949 233930489614088704779839)
                    ·
                      rfl

theorem cell22_683367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_683367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683367 prefixEnd_683367 := by exact prefixLift 683367
  have htrace : WordTrace (prefixWord ++ tailWord_683367) baseStart_683367 baseEnd_683367 := by
    simpa [prefixWord, tailWord_683367, baseEnd_683367] using wordTrace_append hprefix tailTrace_683367
  have hstable : (prefixWord ++ tailWord_683367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683367).length < 2 ^ (prefixWord ++ tailWord_683367).sum := by decide
  have hdescent : baseEnd_683367 < baseStart_683367 := by decide
  rcases family_descends (prefixWord ++ tailWord_683367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683378 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_683378 : Nat := 118140960795 + 683378 * 2 ^ 59
def prefixEnd_683378 : Nat := 4983230072969 + 3 ^ 40 * 683378 * 2
def baseEnd_683378 : Nat := 233934255138888342754805

theorem tailTrace_683378 : CollatzResearch.WordTrace tailWord_683378 prefixEnd_683378 233934255138888342754805 := by
  unfold tailWord_683378
  simp only [CollatzResearch.WordTrace]
  refine ⟨6231210829561423128904697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16616562212163795010412525 6231210829561423128904697)
  ·
    refine ⟨4673408122171067346678523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6231210829561423128904697 4673408122171067346678523)
    ·
      refine ⟨7010112183256601020017785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4673408122171067346678523 7010112183256601020017785)
      ·
        refine ⟨5257584137442450765013339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7010112183256601020017785 5257584137442450765013339)
        ·
          refine ⟨7886376206163676147520009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5257584137442450765013339 7886376206163676147520009)
          ·
            refine ⟨5914782154622757110640007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7886376206163676147520009 5914782154622757110640007)
            ·
              refine ⟨8872173231934135665960011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5914782154622757110640007 8872173231934135665960011)
              ·
                refine ⟨13308259847901203498940017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8872173231934135665960011 13308259847901203498940017)
                ·
                  refine ⟨9981194885925902624205013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13308259847901203498940017 9981194885925902624205013)
                  ·
                    refine ⟨233934255138888342754805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9981194885925902624205013 233934255138888342754805)
                    ·
                      rfl

theorem cell22_683378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_683378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683378 prefixEnd_683378 := by exact prefixLift 683378
  have htrace : WordTrace (prefixWord ++ tailWord_683378) baseStart_683378 baseEnd_683378 := by
    simpa [prefixWord, tailWord_683378, baseEnd_683378] using wordTrace_append hprefix tailTrace_683378
  have hstable : (prefixWord ++ tailWord_683378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683378).length < 2 ^ (prefixWord ++ tailWord_683378).sum := by decide
  have hdescent : baseEnd_683378 < baseStart_683378 := by decide
  rcases family_descends (prefixWord ++ tailWord_683378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683455 : List Nat := [1, 1, 2, 2, 2, 1, 1, 7, 1, 4]
def baseStart_683455 : Nat := 118140960795 + 683455 * 2 ^ 59
def prefixEnd_683455 : Nat := 4983230072969 + 3 ^ 40 * 683455 * 2
def baseEnd_683455 : Nat := 233960613812485808579569

theorem tailTrace_683455 : CollatzResearch.WordTrace tailWord_683455 prefixEnd_683455 233960613812485808579569 := by
  unfold tailWord_683455
  simp only [CollatzResearch.WordTrace]
  refine ⟨24927651738966734666171819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16618434492644489777447879 24927651738966734666171819)
  ·
    refine ⟨37391477608450101999257729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24927651738966734666171819 37391477608450101999257729)
    ·
      refine ⟨28043608206337576499443297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37391477608450101999257729 28043608206337576499443297)
      ·
        refine ⟨21032706154753182374582473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28043608206337576499443297 21032706154753182374582473)
        ·
          refine ⟨15774529616064886780936855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21032706154753182374582473 15774529616064886780936855)
          ·
            refine ⟨23661794424097330171405283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15774529616064886780936855 23661794424097330171405283)
            ·
              refine ⟨35492691636145995257107925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23661794424097330171405283 35492691636145995257107925)
              ·
                refine ⟨831859960222171763838467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 35492691636145995257107925 831859960222171763838467)
                ·
                  refine ⟨1247789940333257645757701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831859960222171763838467 1247789940333257645757701)
                  ·
                    refine ⟨233960613812485808579569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1247789940333257645757701 233960613812485808579569)
                    ·
                      rfl

theorem cell22_683455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 4].length) (baseStart_683455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683455 prefixEnd_683455 := by exact prefixLift 683455
  have htrace : WordTrace (prefixWord ++ tailWord_683455) baseStart_683455 baseEnd_683455 := by
    simpa [prefixWord, tailWord_683455, baseEnd_683455] using wordTrace_append hprefix tailTrace_683455
  have hstable : (prefixWord ++ tailWord_683455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683455).length < 2 ^ (prefixWord ++ tailWord_683455).sum := by decide
  have hdescent : baseEnd_683455 < baseStart_683455 := by decide
  rcases family_descends (prefixWord ++ tailWord_683455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683483 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 7, 6]
def baseStart_683483 : Nat := 118140960795 + 683483 * 2 ^ 59
def prefixEnd_683483 : Nat := 4983230072969 + 3 ^ 40 * 683483 * 2
def baseEnd_683483 : Nat := 233970198784703068879483

theorem tailTrace_683483 : CollatzResearch.WordTrace tailWord_683483 prefixEnd_683483 233970198784703068879483 := by
  unfold tailWord_683483
  simp only [CollatzResearch.WordTrace]
  refine ⟨24928672982865295448191103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16619115321910196965460735 24928672982865295448191103)
  ·
    refine ⟨37393009474297943172286655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24928672982865295448191103 37393009474297943172286655)
    ·
      refine ⟨56089514211446914758429983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37393009474297943172286655 56089514211446914758429983)
      ·
        refine ⟨84134271317170372137644975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56089514211446914758429983 84134271317170372137644975)
        ·
          refine ⟨126201406975755558206467463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84134271317170372137644975 126201406975755558206467463)
          ·
            refine ⟨189302110463633337309701195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126201406975755558206467463 189302110463633337309701195)
            ·
              refine ⟨283953165695450005964551793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189302110463633337309701195 283953165695450005964551793)
              ·
                refine ⟨212964874271587504473413845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283953165695450005964551793 212964874271587504473413845)
                ·
                  refine ⟨4991364240740332136095637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 212964874271587504473413845 4991364240740332136095637)
                  ·
                    refine ⟨233970198784703068879483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4991364240740332136095637 233970198784703068879483)
                    ·
                      rfl

theorem cell22_683483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 6].length) (baseStart_683483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683483 prefixEnd_683483 := by exact prefixLift 683483
  have htrace : WordTrace (prefixWord ++ tailWord_683483) baseStart_683483 baseEnd_683483 := by
    simpa [prefixWord, tailWord_683483, baseEnd_683483] using wordTrace_append hprefix tailTrace_683483
  have hstable : (prefixWord ++ tailWord_683483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683483).length < 2 ^ (prefixWord ++ tailWord_683483).sum := by decide
  have hdescent : baseEnd_683483 < baseStart_683483 := by decide
  rcases family_descends (prefixWord ++ tailWord_683483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683500 : List Nat := [2, 2, 1, 1, 2, 1, 2, 5, 2, 4]
def baseStart_683500 : Nat := 118140960795 + 683500 * 2 ^ 59
def prefixEnd_683500 : Nat := 4983230072969 + 3 ^ 40 * 683500 * 2
def baseEnd_683500 : Nat := 233976018232120691204431

theorem tailTrace_683500 : CollatzResearch.WordTrace tailWord_683500 prefixEnd_683500 233976018232120691204431 := by
  unfold tailWord_683500
  simp only [CollatzResearch.WordTrace]
  refine ⟨12464646511901853675779977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16619528682535804901039969 12464646511901853675779977)
  ·
    refine ⟨9348484883926390256834983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12464646511901853675779977 9348484883926390256834983)
    ·
      refine ⟨14022727325889585385252475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9348484883926390256834983 14022727325889585385252475)
      ·
        refine ⟨21034090988834378077878713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14022727325889585385252475 21034090988834378077878713)
        ·
          refine ⟨15775568241625783558409035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21034090988834378077878713 15775568241625783558409035)
          ·
            refine ⟨23663352362438675337613553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15775568241625783558409035 23663352362438675337613553)
            ·
              refine ⟨17747514271829006503210165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23663352362438675337613553 17747514271829006503210165)
              ·
                refine ⟨1663829462983969359675953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17747514271829006503210165 1663829462983969359675953)
                ·
                  refine ⟨1247872097237977019756965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1663829462983969359675953 1247872097237977019756965)
                  ·
                    refine ⟨233976018232120691204431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1247872097237977019756965 233976018232120691204431)
                    ·
                      rfl

theorem cell22_683500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_683500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683500 prefixEnd_683500 := by exact prefixLift 683500
  have htrace : WordTrace (prefixWord ++ tailWord_683500) baseStart_683500 baseEnd_683500 := by
    simpa [prefixWord, tailWord_683500, baseEnd_683500] using wordTrace_append hprefix tailTrace_683500
  have hstable : (prefixWord ++ tailWord_683500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683500).length < 2 ^ (prefixWord ++ tailWord_683500).sum := by decide
  have hdescent : baseEnd_683500 < baseStart_683500 := by decide
  rcases family_descends (prefixWord ++ tailWord_683500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683502 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 4, 3]
def baseStart_683502 : Nat := 118140960795 + 683502 * 2 ^ 59
def prefixEnd_683502 : Nat := 4983230072969 + 3 ^ 40 * 683502 * 2
def baseEnd_683502 : Nat := 233976702872993352654425

theorem tailTrace_683502 : CollatzResearch.WordTrace tailWord_683502 prefixEnd_683502 233976702872993352654425 := by
  unfold tailWord_683502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3116170746224557711641595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16619577313197641128755173 3116170746224557711641595)
  ·
    refine ⟨4674256119336836567462393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3116170746224557711641595 4674256119336836567462393)
    ·
      refine ⟨3505692089502627425596795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4674256119336836567462393 3505692089502627425596795)
      ·
        refine ⟨5258538134253941138395193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3505692089502627425596795 5258538134253941138395193)
        ·
          refine ⟨3943903600690455853796395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5258538134253941138395193 3943903600690455853796395)
          ·
            refine ⟨5915855401035683780694593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3943903600690455853796395 5915855401035683780694593)
            ·
              refine ⟨4436891550776762835520945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5915855401035683780694593 4436891550776762835520945)
              ·
                refine ⟨3327668663082572126640709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4436891550776762835520945 3327668663082572126640709)
                ·
                  refine ⟨623937874327982273745133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3327668663082572126640709 623937874327982273745133)
                  ·
                    refine ⟨233976702872993352654425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 623937874327982273745133 233976702872993352654425)
                    ·
                      rfl

theorem cell22_683502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_683502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683502 prefixEnd_683502 := by exact prefixLift 683502
  have htrace : WordTrace (prefixWord ++ tailWord_683502) baseStart_683502 baseEnd_683502 := by
    simpa [prefixWord, tailWord_683502, baseEnd_683502] using wordTrace_append hprefix tailTrace_683502
  have hstable : (prefixWord ++ tailWord_683502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683502).length < 2 ^ (prefixWord ++ tailWord_683502).sum := by decide
  have hdescent : baseEnd_683502 < baseStart_683502 := by decide
  rcases family_descends (prefixWord ++ tailWord_683502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683506 : List Nat := [3, 2, 1, 4, 1, 3, 2, 1, 1, 4]
def baseStart_683506 : Nat := 118140960795 + 683506 * 2 ^ 59
def prefixEnd_683506 : Nat := 4983230072969 + 3 ^ 40 * 683506 * 2
def baseEnd_683506 : Nat := 233978072154738675554413

theorem tailTrace_683506 : CollatzResearch.WordTrace tailWord_683506 prefixEnd_683506 233978072154738675554413 := by
  unfold tailWord_683506
  simp only [CollatzResearch.WordTrace]
  refine ⟨6232377965445492594069593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16619674574521313584185581 6232377965445492594069593)
  ·
    refine ⟨4674283474084119445552195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6232377965445492594069593 4674283474084119445552195)
    ·
      refine ⟨7011425211126179168328293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4674283474084119445552195 7011425211126179168328293)
      ·
        refine ⟨1314642227086158594061555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7011425211126179168328293 1314642227086158594061555)
        ·
          refine ⟨1971963340629237891092333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1314642227086158594061555 1971963340629237891092333)
          ·
            refine ⟨739486252735964209159625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1971963340629237891092333 739486252735964209159625)
            ·
              refine ⟨554614689551973156869719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 739486252735964209159625 554614689551973156869719)
              ·
                refine ⟨831922034327959735304579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554614689551973156869719 831922034327959735304579)
                ·
                  refine ⟨1247883051491939602956869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831922034327959735304579 1247883051491939602956869)
                  ·
                    refine ⟨233978072154738675554413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1247883051491939602956869 233978072154738675554413)
                    ·
                      rfl

theorem cell22_683506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_683506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683506 prefixEnd_683506 := by exact prefixLift 683506
  have htrace : WordTrace (prefixWord ++ tailWord_683506) baseStart_683506 baseEnd_683506 := by
    simpa [prefixWord, tailWord_683506, baseEnd_683506] using wordTrace_append hprefix tailTrace_683506
  have hstable : (prefixWord ++ tailWord_683506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683506).length < 2 ^ (prefixWord ++ tailWord_683506).sum := by decide
  have hdescent : baseEnd_683506 < baseStart_683506 := by decide
  rcases family_descends (prefixWord ++ tailWord_683506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683581 : List Nat := [1, 4, 1, 3, 3, 2, 1, 1, 3, 3]
def baseStart_683581 : Nat := 118140960795 + 683581 * 2 ^ 59
def prefixEnd_683581 : Nat := 4983230072969 + 3 ^ 40 * 683581 * 2
def baseEnd_683581 : Nat := 234003746187463479929183

theorem tailTrace_683581 : CollatzResearch.WordTrace tailWord_683581 prefixEnd_683581 234003746187463479929183 := by
  unfold tailWord_683581
  simp only [CollatzResearch.WordTrace]
  refine ⟨24932247336510258185258597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16621498224340172123505731 24932247336510258185258597)
  ·
    refine ⟨4674796375595673409735987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24932247336510258185258597 4674796375595673409735987)
    ·
      refine ⟨7012194563393510114603981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4674796375595673409735987 7012194563393510114603981)
      ·
        refine ⟨2629572961272566292976493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7012194563393510114603981 2629572961272566292976493)
        ·
          refine ⟨986089860477212359866185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2629572961272566292976493 986089860477212359866185)
          ·
            refine ⟨739567395357909269899639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 986089860477212359866185 739567395357909269899639)
            ·
              refine ⟨1109351093036863904849459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 739567395357909269899639 1109351093036863904849459)
              ·
                refine ⟨1664026639555295857274189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1109351093036863904849459 1664026639555295857274189)
                ·
                  refine ⟨624009989833235946477821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1664026639555295857274189 624009989833235946477821)
                  ·
                    refine ⟨234003746187463479929183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 624009989833235946477821 234003746187463479929183)
                    ·
                      rfl

theorem cell22_683581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_683581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683581 prefixEnd_683581 := by exact prefixLift 683581
  have htrace : WordTrace (prefixWord ++ tailWord_683581) baseStart_683581 baseEnd_683581 := by
    simpa [prefixWord, tailWord_683581, baseEnd_683581] using wordTrace_append hprefix tailTrace_683581
  have hstable : (prefixWord ++ tailWord_683581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683581).length < 2 ^ (prefixWord ++ tailWord_683581).sum := by decide
  have hdescent : baseEnd_683581 < baseStart_683581 := by decide
  rcases family_descends (prefixWord ++ tailWord_683581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683605 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 8]
def baseStart_683605 : Nat := 118140960795 + 683605 * 2 ^ 59
def prefixEnd_683605 : Nat := 4983230072969 + 3 ^ 40 * 683605 * 2
def baseEnd_683605 : Nat := 78003987292645139109703

theorem tailTrace_683605 : CollatzResearch.WordTrace tailWord_683605 prefixEnd_683605 78003987292645139109703 := by
  unfold tailWord_683605
  simp only [CollatzResearch.WordTrace]
  refine ⟨24933122688423310284132269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16622081792282206856088179 24933122688423310284132269)
  ·
    refine ⟨9349921008158741356549601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24933122688423310284132269 9349921008158741356549601)
    ·
      refine ⟨7012440756119056017412201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9349921008158741356549601 7012440756119056017412201)
      ·
        refine ⟨5259330567089292013059151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7012440756119056017412201 5259330567089292013059151)
        ·
          refine ⟨7888995850633938019588727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5259330567089292013059151 7888995850633938019588727)
          ·
            refine ⟨11833493775950907029383091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7888995850633938019588727 11833493775950907029383091)
            ·
              refine ⟨17750240663926360544074637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11833493775950907029383091 17750240663926360544074637)
              ·
                refine ⟨6656340248972385204027989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17750240663926360544074637 6656340248972385204027989)
                ·
                  refine ⟨78003987292645139109703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6656340248972385204027989 78003987292645139109703)
                  ·
                    rfl

theorem cell22_683605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_683605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683605 prefixEnd_683605 := by exact prefixLift 683605
  have htrace : WordTrace (prefixWord ++ tailWord_683605) baseStart_683605 baseEnd_683605 := by
    simpa [prefixWord, tailWord_683605, baseEnd_683605] using wordTrace_append hprefix tailTrace_683605
  have hstable : (prefixWord ++ tailWord_683605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683605).length < 2 ^ (prefixWord ++ tailWord_683605).sum := by decide
  have hdescent : baseEnd_683605 < baseStart_683605 := by decide
  rcases family_descends (prefixWord ++ tailWord_683605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683607 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 3, 4]
def baseStart_683607 : Nat := 118140960795 + 683607 * 2 ^ 59
def prefixEnd_683607 : Nat := 4983230072969 + 3 ^ 40 * 683607 * 2
def baseEnd_683607 : Nat := 234012646518808078779103

theorem tailTrace_683607 : CollatzResearch.WordTrace tailWord_683607 prefixEnd_683607 234012646518808078779103 := by
  unfold tailWord_683607
  simp only [CollatzResearch.WordTrace]
  refine ⟨24933195634416064625705075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16622130422944043083803383 24933195634416064625705075)
  ·
    refine ⟨37399793451624096938557613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24933195634416064625705075 37399793451624096938557613)
    ·
      refine ⟨14024922544359036351959105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37399793451624096938557613 14024922544359036351959105)
      ·
        refine ⟨10518691908269277263969329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14024922544359036351959105 10518691908269277263969329)
        ·
          refine ⟨7889018931201957947976997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10518691908269277263969329 7889018931201957947976997)
          ·
            refine ⟨1479191049600367115245687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7889018931201957947976997 1479191049600367115245687)
            ·
              refine ⟨2218786574400550672868531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1479191049600367115245687 2218786574400550672868531)
              ·
                refine ⟨3328179861600826009302797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2218786574400550672868531 3328179861600826009302797)
                ·
                  refine ⟨1248067448100309753488549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3328179861600826009302797 1248067448100309753488549)
                  ·
                    refine ⟨234012646518808078779103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1248067448100309753488549 234012646518808078779103)
                    ·
                      rfl

theorem cell22_683607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_683607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683607 prefixEnd_683607 := by exact prefixLift 683607
  have htrace : WordTrace (prefixWord ++ tailWord_683607) baseStart_683607 baseEnd_683607 := by
    simpa [prefixWord, tailWord_683607, baseEnd_683607] using wordTrace_append hprefix tailTrace_683607
  have hstable : (prefixWord ++ tailWord_683607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683607).length < 2 ^ (prefixWord ++ tailWord_683607).sum := by decide
  have hdescent : baseEnd_683607 < baseStart_683607 := by decide
  rcases family_descends (prefixWord ++ tailWord_683607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683665 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 1, 9]
def baseStart_683665 : Nat := 118140960795 + 683665 * 2 ^ 59
def prefixEnd_683665 : Nat := 4983230072969 + 3 ^ 40 * 683665 * 2
def baseEnd_683665 : Nat := 234032501104115260828925

theorem tailTrace_683665 : CollatzResearch.WordTrace tailWord_683665 prefixEnd_683665 234032501104115260828925 := by
  unfold tailWord_683665
  simp only [CollatzResearch.WordTrace]
  refine ⟨24935311068205940531316449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16623540712137293687544299 24935311068205940531316449)
  ·
    refine ⟨18701483301154455398487337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24935311068205940531316449 18701483301154455398487337)
    ·
      refine ⟨14026112475865841548865503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18701483301154455398487337 14026112475865841548865503)
      ·
        refine ⟨21039168713798762323298255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14026112475865841548865503 21039168713798762323298255)
        ·
          refine ⟨31558753070698143484947383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21039168713798762323298255 31558753070698143484947383)
          ·
            refine ⟨47338129606047215227421075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31558753070698143484947383 47338129606047215227421075)
            ·
              refine ⟨71007194409070822841131613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47338129606047215227421075 71007194409070822841131613)
              ·
                refine ⟨26627697903401558565424355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71007194409070822841131613 26627697903401558565424355)
                ·
                  refine ⟨39941546855102337848136533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26627697903401558565424355 39941546855102337848136533)
                  ·
                    refine ⟨234032501104115260828925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 39941546855102337848136533 234032501104115260828925)
                    ·
                      rfl

theorem cell22_683665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_683665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683665 prefixEnd_683665 := by exact prefixLift 683665
  have htrace : WordTrace (prefixWord ++ tailWord_683665) baseStart_683665 baseEnd_683665 := by
    simpa [prefixWord, tailWord_683665, baseEnd_683665] using wordTrace_append hprefix tailTrace_683665
  have hstable : (prefixWord ++ tailWord_683665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683665).length < 2 ^ (prefixWord ++ tailWord_683665).sum := by decide
  have hdescent : baseEnd_683665 < baseStart_683665 := by decide
  rcases family_descends (prefixWord ++ tailWord_683665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683699 : List Nat := [1, 1, 1, 2, 3, 3, 4, 1, 3, 3]
def baseStart_683699 : Nat := 118140960795 + 683699 * 2 ^ 59
def prefixEnd_683699 : Nat := 4983230072969 + 3 ^ 40 * 683699 * 2
def baseEnd_683699 : Nat := 234044139998950505478821

theorem tailTrace_683699 : CollatzResearch.WordTrace tailWord_683699 prefixEnd_683699 234044139998950505478821 := by
  unfold tailWord_683699
  simp only [CollatzResearch.WordTrace]
  refine ⟨24936551150082764338054151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16624367433388509558702767 24936551150082764338054151)
  ·
    refine ⟨37404826725124146507081227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24936551150082764338054151 37404826725124146507081227)
    ·
      refine ⟨56107240087686219760621841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37404826725124146507081227 56107240087686219760621841)
      ·
        refine ⟨42080430065764664820466381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56107240087686219760621841 42080430065764664820466381)
        ·
          refine ⟨15780161274661749307674893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42080430065764664820466381 15780161274661749307674893)
          ·
            refine ⟨5917560477998155990378085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15780161274661749307674893 5917560477998155990378085)
            ·
              refine ⟨1109542589624654248195891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5917560477998155990378085 1109542589624654248195891)
              ·
                refine ⟨1664313884436981372293837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1109542589624654248195891 1664313884436981372293837)
                ·
                  refine ⟨624117706663868014610189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1664313884436981372293837 624117706663868014610189)
                  ·
                    refine ⟨234044139998950505478821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 624117706663868014610189 234044139998950505478821)
                    ·
                      rfl

theorem cell22_683699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 3].length) (baseStart_683699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683699 prefixEnd_683699 := by exact prefixLift 683699
  have htrace : WordTrace (prefixWord ++ tailWord_683699) baseStart_683699 baseEnd_683699 := by
    simpa [prefixWord, tailWord_683699, baseEnd_683699] using wordTrace_append hprefix tailTrace_683699
  have hstable : (prefixWord ++ tailWord_683699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683699).length < 2 ^ (prefixWord ++ tailWord_683699).sum := by decide
  have hdescent : baseEnd_683699 < baseStart_683699 := by decide
  rcases family_descends (prefixWord ++ tailWord_683699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683718 : List Nat := [6, 1, 2, 1, 1, 1, 4, 6]
def baseStart_683718 : Nat := 118140960795 + 683718 * 2 ^ 59
def prefixEnd_683718 : Nat := 4983230072969 + 3 ^ 40 * 683718 * 2
def baseEnd_683718 : Nat := 26005627120804532139307

theorem tailTrace_683718 : CollatzResearch.WordTrace tailWord_683718 prefixEnd_683718 26005627120804532139307 := by
  unfold tailWord_683718
  simp only [CollatzResearch.WordTrace]
  refine ⟨779288879281685330718619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16624829424675953721997205 779288879281685330718619)
  ·
    refine ⟨1168933318922527996077929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 779288879281685330718619 1168933318922527996077929)
    ·
      refine ⟨876699989191895997058447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1168933318922527996077929 876699989191895997058447)
      ·
        refine ⟨1315049983787843995587671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 876699989191895997058447 1315049983787843995587671)
        ·
          refine ⟨1972574975681765993381507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1315049983787843995587671 1972574975681765993381507)
          ·
            refine ⟨2958862463522648990072261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1972574975681765993381507 2958862463522648990072261)
            ·
              refine ⟨554786711910496685638549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2958862463522648990072261 554786711910496685638549)
              ·
                refine ⟨26005627120804532139307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 554786711910496685638549 26005627120804532139307)
                ·
                  rfl

theorem cell22_683718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_683718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683718 prefixEnd_683718 := by exact prefixLift 683718
  have htrace : WordTrace (prefixWord ++ tailWord_683718) baseStart_683718 baseEnd_683718 := by
    simpa [prefixWord, tailWord_683718, baseEnd_683718] using wordTrace_append hprefix tailTrace_683718
  have hstable : (prefixWord ++ tailWord_683718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683718).length < 2 ^ (prefixWord ++ tailWord_683718).sum := by decide
  have hdescent : baseEnd_683718 < baseStart_683718 := by decide
  rcases family_descends (prefixWord ++ tailWord_683718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683787 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 1, 6]
def baseStart_683787 : Nat := 118140960795 + 683787 * 2 ^ 59
def prefixEnd_683787 : Nat := 4983230072969 + 3 ^ 40 * 683787 * 2
def baseEnd_683787 : Nat := 234074264197347609278551

theorem tailTrace_683787 : CollatzResearch.WordTrace tailWord_683787 prefixEnd_683787 234074264197347609278551 := by
  unfold tailWord_683787
  simp only [CollatzResearch.WordTrace]
  refine ⟨24939760773763955367257615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16626507182509303578171743 24939760773763955367257615)
  ·
    refine ⟨37409641160645933050886423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24939760773763955367257615 37409641160645933050886423)
    ·
      refine ⟨56114461740968899576329635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37409641160645933050886423 56114461740968899576329635)
      ·
        refine ⟨84171692611453349364494453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56114461740968899576329635 84171692611453349364494453)
        ·
          refine ⟨7891096182323751502921355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84171692611453349364494453 7891096182323751502921355)
          ·
            refine ⟨11836644273485627254382033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7891096182323751502921355 11836644273485627254382033)
            ·
              refine ⟨8877483205114220440786525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11836644273485627254382033 8877483205114220440786525)
              ·
                refine ⟨3329056201917832665294947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8877483205114220440786525 3329056201917832665294947)
                ·
                  refine ⟨4993584302876748997942421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3329056201917832665294947 4993584302876748997942421)
                  ·
                    refine ⟨234074264197347609278551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4993584302876748997942421 234074264197347609278551)
                    ·
                      rfl

theorem cell22_683787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 6].length) (baseStart_683787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683787 prefixEnd_683787 := by exact prefixLift 683787
  have htrace : WordTrace (prefixWord ++ tailWord_683787) baseStart_683787 baseEnd_683787 := by
    simpa [prefixWord, tailWord_683787, baseEnd_683787] using wordTrace_append hprefix tailTrace_683787
  have hstable : (prefixWord ++ tailWord_683787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683787).length < 2 ^ (prefixWord ++ tailWord_683787).sum := by decide
  have hdescent : baseEnd_683787 < baseStart_683787 := by decide
  rcases family_descends (prefixWord ++ tailWord_683787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683802 : List Nat := [3, 1, 1, 3, 2, 12]
def baseStart_683802 : Nat := 118140960795 + 683802 * 2 ^ 59
def prefixEnd_683802 : Nat := 4983230072969 + 3 ^ 40 * 683802 * 2
def baseEnd_683802 : Nat := 2889869123504846545105

theorem tailTrace_683802 : CollatzResearch.WordTrace tailWord_683802 prefixEnd_683802 2889869123504846545105 := by
  unfold tailWord_683802
  simp only [CollatzResearch.WordTrace]
  refine ⟨6235076967177403232263415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16626871912473075286035773 6235076967177403232263415)
  ·
    refine ⟨9352615450766104848395123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6235076967177403232263415 9352615450766104848395123)
    ·
      refine ⟨14028923176149157272592685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9352615450766104848395123 14028923176149157272592685)
      ·
        refine ⟨5260846191055933977222257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14028923176149157272592685 5260846191055933977222257)
        ·
          refine ⟨3945634643291950482916693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5260846191055933977222257 3945634643291950482916693)
          ·
            refine ⟨2889869123504846545105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3945634643291950482916693 2889869123504846545105)
            ·
              rfl

theorem cell22_683802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 12].length) (baseStart_683802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683802 prefixEnd_683802 := by exact prefixLift 683802
  have htrace : WordTrace (prefixWord ++ tailWord_683802) baseStart_683802 baseEnd_683802 := by
    simpa [prefixWord, tailWord_683802, baseEnd_683802] using wordTrace_append hprefix tailTrace_683802
  have hstable : (prefixWord ++ tailWord_683802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683802).length < 2 ^ (prefixWord ++ tailWord_683802).sum := by decide
  have hdescent : baseEnd_683802 < baseStart_683802 := by decide
  rcases family_descends (prefixWord ++ tailWord_683802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683804 : List Nat := [2, 2, 3, 1, 1, 2, 1, 4, 2, 4]
def baseStart_683804 : Nat := 118140960795 + 683804 * 2 ^ 59
def prefixEnd_683804 : Nat := 4983230072969 + 3 ^ 40 * 683804 * 2
def baseEnd_683804 : Nat := 234080083644765231603499

theorem tailTrace_683804 : CollatzResearch.WordTrace tailWord_683804 prefixEnd_683804 234080083644765231603499 := by
  unfold tailWord_683804
  simp only [CollatzResearch.WordTrace]
  refine ⟨12470190407351183635313233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16626920543134911513750977 12470190407351183635313233)
  ·
    refine ⟨9352642805513387726484925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12470190407351183635313233 9352642805513387726484925)
    ·
      refine ⟨3507241052067520397431847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9352642805513387726484925 3507241052067520397431847)
      ·
        refine ⟨5260861578101280596147771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3507241052067520397431847 5260861578101280596147771)
        ·
          refine ⟨7891292367151920894221657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5260861578101280596147771 7891292367151920894221657)
          ·
            refine ⟨5918469275363940670666243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7891292367151920894221657 5918469275363940670666243)
            ·
              refine ⟨8877703913045911005999365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5918469275363940670666243 8877703913045911005999365)
              ·
                refine ⟨1664569483696108313624881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8877703913045911005999365 1664569483696108313624881)
                ·
                  refine ⟨1248427112772081235218661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1664569483696108313624881 1248427112772081235218661)
                  ·
                    refine ⟨234080083644765231603499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1248427112772081235218661 234080083644765231603499)
                    ·
                      rfl

theorem cell22_683804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_683804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683804 prefixEnd_683804 := by exact prefixLift 683804
  have htrace : WordTrace (prefixWord ++ tailWord_683804) baseStart_683804 baseEnd_683804 := by
    simpa [prefixWord, tailWord_683804, baseEnd_683804] using wordTrace_append hprefix tailTrace_683804
  have hstable : (prefixWord ++ tailWord_683804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683804).length < 2 ^ (prefixWord ++ tailWord_683804).sum := by decide
  have hdescent : baseEnd_683804 < baseStart_683804 := by decide
  rcases family_descends (prefixWord ++ tailWord_683804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683838 : List Nat := [4, 2, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_683838 : Nat := 118140960795 + 683838 * 2 ^ 59
def prefixEnd_683838 : Nat := 4983230072969 + 3 ^ 40 * 683838 * 2
def baseEnd_683838 : Nat := 234091722539600476253395

theorem tailTrace_683838 : CollatzResearch.WordTrace tailWord_683838 prefixEnd_683838 234091722539600476253395 := by
  unfold tailWord_683838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3117702612072398884670521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16627747264386127384909445 3117702612072398884670521)
  ·
    refine ⟨2338276959054299163502891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3117702612072398884670521 2338276959054299163502891)
    ·
      refine ⟨3507415438581448745254337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2338276959054299163502891 3507415438581448745254337)
      ·
        refine ⟨2630561578936086558940753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3507415438581448745254337 2630561578936086558940753)
        ·
          refine ⟨1972921184202064919205565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2630561578936086558940753 1972921184202064919205565)
          ·
            refine ⟨739845444075774344702087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1972921184202064919205565 739845444075774344702087)
            ·
              refine ⟨1109768166113661517053131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 739845444075774344702087 1109768166113661517053131)
              ·
                refine ⟨1664652249170492275579697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1109768166113661517053131 1664652249170492275579697)
                ·
                  refine ⟨1248489186877869206684773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1664652249170492275579697 1248489186877869206684773)
                  ·
                    refine ⟨234091722539600476253395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1248489186877869206684773 234091722539600476253395)
                    ·
                      rfl

theorem cell22_683838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_683838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683838 prefixEnd_683838 := by exact prefixLift 683838
  have htrace : WordTrace (prefixWord ++ tailWord_683838) baseStart_683838 baseEnd_683838 := by
    simpa [prefixWord, tailWord_683838, baseEnd_683838] using wordTrace_append hprefix tailTrace_683838
  have hstable : (prefixWord ++ tailWord_683838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683838).length < 2 ^ (prefixWord ++ tailWord_683838).sum := by decide
  have hdescent : baseEnd_683838 < baseStart_683838 := by decide
  rcases family_descends (prefixWord ++ tailWord_683838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683879 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 2, 5]
def baseStart_683879 : Nat := 118140960795 + 683879 * 2 ^ 59
def prefixEnd_683879 : Nat := 4983230072969 + 3 ^ 40 * 683879 * 2
def baseEnd_683879 : Nat := 234105757677490035978269

theorem tailTrace_683879 : CollatzResearch.WordTrace tailWord_683879 prefixEnd_683879 234105757677490035978269 := by
  unfold tailWord_683879
  simp only [CollatzResearch.WordTrace]
  refine ⟨24943116289430655079606691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16628744192953770053071127 24943116289430655079606691)
  ·
    refine ⟨37414674434145982619410037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24943116289430655079606691 37414674434145982619410037)
    ·
      refine ⟨3507625728201185870569691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37414674434145982619410037 3507625728201185870569691)
      ·
        refine ⟨5261438592301778805854537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3507625728201185870569691 5261438592301778805854537)
        ·
          refine ⟨3946078944226334104390903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5261438592301778805854537 3946078944226334104390903)
          ·
            refine ⟨5919118416339501156586355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3946078944226334104390903 5919118416339501156586355)
            ·
              refine ⟨8878677624509251734879533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5919118416339501156586355 8878677624509251734879533)
              ·
                refine ⟨3329504109190969400579825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8878677624509251734879533 3329504109190969400579825)
                ·
                  refine ⟨2497128081893227050434869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3329504109190969400579825 2497128081893227050434869)
                  ·
                    refine ⟨234105757677490035978269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2497128081893227050434869 234105757677490035978269)
                    ·
                      rfl

theorem cell22_683879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_683879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683879 prefixEnd_683879 := by exact prefixLift 683879
  have htrace : WordTrace (prefixWord ++ tailWord_683879) baseStart_683879 baseEnd_683879 := by
    simpa [prefixWord, tailWord_683879, baseEnd_683879] using wordTrace_append hprefix tailTrace_683879
  have hstable : (prefixWord ++ tailWord_683879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683879).length < 2 ^ (prefixWord ++ tailWord_683879).sum := by decide
  have hdescent : baseEnd_683879 < baseStart_683879 := by decide
  rcases family_descends (prefixWord ++ tailWord_683879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683902 : List Nat := [4, 2, 3, 1, 1, 1, 3, 3, 1, 3]
def baseStart_683902 : Nat := 118140960795 + 683902 * 2 ^ 59
def prefixEnd_683902 : Nat := 4983230072969 + 3 ^ 40 * 683902 * 2
def baseEnd_683902 : Nat := 234113631047525642653199

theorem tailTrace_683902 : CollatzResearch.WordTrace tailWord_683902 prefixEnd_683902 234113631047525642653199 := by
  unfold tailWord_683902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3117994396043416250961745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16629303445564886671795973 3117994396043416250961745)
  ·
    refine ⟨2338495797032562188221309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3117994396043416250961745 2338495797032562188221309)
    ·
      refine ⟨876935923887210820582991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2338495797032562188221309 876935923887210820582991)
      ·
        refine ⟨1315403885830816230874487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 876935923887210820582991 1315403885830816230874487)
        ·
          refine ⟨1973105828746224346311731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1315403885830816230874487 1973105828746224346311731)
          ·
            refine ⟨2959658743119336519467597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1973105828746224346311731 2959658743119336519467597)
            ·
              refine ⟨1109872028669751194800349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2959658743119336519467597 1109872028669751194800349)
              ·
                refine ⟨416202010751156698050131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1109872028669751194800349 416202010751156698050131)
                ·
                  refine ⟨624303016126735047075197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 416202010751156698050131 624303016126735047075197)
                  ·
                    refine ⟨234113631047525642653199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 624303016126735047075197 234113631047525642653199)
                    ·
                      rfl

theorem cell22_683902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_683902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683902 prefixEnd_683902 := by exact prefixLift 683902
  have htrace : WordTrace (prefixWord ++ tailWord_683902) baseStart_683902 baseEnd_683902 := by
    simpa [prefixWord, tailWord_683902, baseEnd_683902] using wordTrace_append hprefix tailTrace_683902
  have hstable : (prefixWord ++ tailWord_683902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683902).length < 2 ^ (prefixWord ++ tailWord_683902).sum := by decide
  have hdescent : baseEnd_683902 < baseStart_683902 := by decide
  rcases family_descends (prefixWord ++ tailWord_683902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683939 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 6, 4]
def baseStart_683939 : Nat := 118140960795 + 683939 * 2 ^ 59
def prefixEnd_683939 : Nat := 4983230072969 + 3 ^ 40 * 683939 * 2
def baseEnd_683939 : Nat := 234126296903669879478085

theorem tailTrace_683939 : CollatzResearch.WordTrace tailWord_683939 prefixEnd_683939 234126296903669879478085 := by
  unfold tailWord_683939
  simp only [CollatzResearch.WordTrace]
  refine ⟨24945304669213285326790871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16630203112808856884527247 24945304669213285326790871)
  ·
    refine ⟨37417957003819927990186307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24945304669213285326790871 37417957003819927990186307)
    ·
      refine ⟨56126935505729891985279461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37417957003819927990186307 56126935505729891985279461)
      ·
        refine ⟨10523800407324354747239899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56126935505729891985279461 10523800407324354747239899)
        ·
          refine ⟨15785700610986532120859849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10523800407324354747239899 15785700610986532120859849)
          ·
            refine ⟨11839275458239899090644887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15785700610986532120859849 11839275458239899090644887)
            ·
              refine ⟨17758913187359848635967331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11839275458239899090644887 17758913187359848635967331)
              ·
                refine ⟨26638369781039772953950997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17758913187359848635967331 26638369781039772953950997)
                ·
                  refine ⟨1248673583486239357216453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26638369781039772953950997 1248673583486239357216453)
                  ·
                    refine ⟨234126296903669879478085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1248673583486239357216453 234126296903669879478085)
                    ·
                      rfl

theorem cell22_683939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 4].length) (baseStart_683939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683939 prefixEnd_683939 := by exact prefixLift 683939
  have htrace : WordTrace (prefixWord ++ tailWord_683939) baseStart_683939 baseEnd_683939 := by
    simpa [prefixWord, tailWord_683939, baseEnd_683939] using wordTrace_append hprefix tailTrace_683939
  have hstable : (prefixWord ++ tailWord_683939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683939).length < 2 ^ (prefixWord ++ tailWord_683939).sum := by decide
  have hdescent : baseEnd_683939 < baseStart_683939 := by decide
  rcases family_descends (prefixWord ++ tailWord_683939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683984 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 2, 6]
def baseStart_683984 : Nat := 118140960795 + 683984 * 2 ^ 59
def prefixEnd_683984 : Nat := 4983230072969 + 3 ^ 40 * 683984 * 2
def baseEnd_683984 : Nat := 234141701323304762102947

theorem tailTrace_683984 : CollatzResearch.WordTrace tailWord_683984 prefixEnd_683984 234141701323304762102947 := by
  unfold tailWord_683984
  simp only [CollatzResearch.WordTrace]
  refine ⟨12473472977025129006089503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16631297302700172008119337 12473472977025129006089503)
  ·
    refine ⟨18710209465537693509134255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12473472977025129006089503 18710209465537693509134255)
    ·
      refine ⟨28065314198306540263701383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18710209465537693509134255 28065314198306540263701383)
      ·
        refine ⟨42097971297459810395552075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28065314198306540263701383 42097971297459810395552075)
        ·
          refine ⟨63146956946189715593328113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42097971297459810395552075 63146956946189715593328113)
          ·
            refine ⟨47360217709642286694996085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63146956946189715593328113 47360217709642286694996085)
            ·
              refine ⟨4440020410278964377655883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47360217709642286694996085 4440020410278964377655883)
              ·
                refine ⟨6660030615418446566483825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4440020410278964377655883 6660030615418446566483825)
                ·
                  refine ⟨4995022961563834924862869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6660030615418446566483825 4995022961563834924862869)
                  ·
                    refine ⟨234141701323304762102947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4995022961563834924862869 234141701323304762102947)
                    ·
                      rfl

theorem cell22_683984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_683984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_683984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_683984 prefixEnd_683984 := by exact prefixLift 683984
  have htrace : WordTrace (prefixWord ++ tailWord_683984) baseStart_683984 baseEnd_683984 := by
    simpa [prefixWord, tailWord_683984, baseEnd_683984] using wordTrace_append hprefix tailTrace_683984
  have hstable : (prefixWord ++ tailWord_683984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683984).length < 2 ^ (prefixWord ++ tailWord_683984).sum := by decide
  have hdescent : baseEnd_683984 < baseStart_683984 := by decide
  rcases family_descends (prefixWord ++ tailWord_683984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684003 : List Nat := [1, 1, 1, 6, 1, 3, 1, 2, 3, 3]
def baseStart_684003 : Nat := 118140960795 + 684003 * 2 ^ 59
def prefixEnd_684003 : Nat := 4983230072969 + 3 ^ 40 * 684003 * 2
def baseEnd_684003 : Nat := 234148205411595045877889

theorem tailTrace_684003 : CollatzResearch.WordTrace tailWord_684003 prefixEnd_684003 234148205411595045877889 := by
  unfold tailWord_684003
  simp only [CollatzResearch.WordTrace]
  refine ⟨24947638940981424257120663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16631759293987616171413775 24947638940981424257120663)
  ·
    refine ⟨37421458411472136385680995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24947638940981424257120663 37421458411472136385680995)
    ·
      refine ⟨56132187617208204578521493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37421458411472136385680995 56132187617208204578521493)
      ·
        refine ⟨2631196294556634589618195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56132187617208204578521493 2631196294556634589618195)
        ·
          refine ⟨3946794441834951884427293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2631196294556634589618195 3946794441834951884427293)
          ·
            refine ⟨1480047915688106956660235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3946794441834951884427293 1480047915688106956660235)
            ·
              refine ⟨2220071873532160434990353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1480047915688106956660235 2220071873532160434990353)
              ·
                refine ⟨1665053905149120326242765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2220071873532160434990353 1665053905149120326242765)
                ·
                  refine ⟨624395214430920122341037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1665053905149120326242765 624395214430920122341037)
                  ·
                    refine ⟨234148205411595045877889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 624395214430920122341037 234148205411595045877889)
                    ·
                      rfl

theorem cell22_684003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 3].length) (baseStart_684003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684003 prefixEnd_684003 := by exact prefixLift 684003
  have htrace : WordTrace (prefixWord ++ tailWord_684003) baseStart_684003 baseEnd_684003 := by
    simpa [prefixWord, tailWord_684003, baseEnd_684003] using wordTrace_append hprefix tailTrace_684003
  have hstable : (prefixWord ++ tailWord_684003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684003).length < 2 ^ (prefixWord ++ tailWord_684003).sum := by decide
  have hdescent : baseEnd_684003 < baseStart_684003 := by decide
  rcases family_descends (prefixWord ++ tailWord_684003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684063 : List Nat := [1, 1, 2, 4, 1, 2, 4, 2, 1, 4]
def baseStart_684063 : Nat := 118140960795 + 684063 * 2 ^ 59
def prefixEnd_684063 : Nat := 4983230072969 + 3 ^ 40 * 684063 * 2
def baseEnd_684063 : Nat := 234168744637774889377705

theorem tailTrace_684063 : CollatzResearch.WordTrace tailWord_684063 prefixEnd_684063 234168744637774889377705 := by
  unfold tailWord_684063
  simp only [CollatzResearch.WordTrace]
  refine ⟨24949827320764054504304843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16633218213842703002869895 24949827320764054504304843)
  ·
    refine ⟨37424740981146081756457265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24949827320764054504304843 37424740981146081756457265)
    ·
      refine ⟨28068555735859561317342949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37424740981146081756457265 28068555735859561317342949)
      ·
        refine ⟨5262854200473667747001803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28068555735859561317342949 5262854200473667747001803)
        ·
          refine ⟨7894281300710501620502705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5262854200473667747001803 7894281300710501620502705)
          ·
            refine ⟨5920710975532876215377029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7894281300710501620502705 5920710975532876215377029)
            ·
              refine ⟨1110133307912414290383193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5920710975532876215377029 1110133307912414290383193)
              ·
                refine ⟨832599980934310717787395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1110133307912414290383193 832599980934310717787395)
                ·
                  refine ⟨1248899971401466076681093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 832599980934310717787395 1248899971401466076681093)
                  ·
                    refine ⟨234168744637774889377705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1248899971401466076681093 234168744637774889377705)
                    ·
                      rfl

theorem cell22_684063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 4].length) (baseStart_684063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684063 prefixEnd_684063 := by exact prefixLift 684063
  have htrace : WordTrace (prefixWord ++ tailWord_684063) baseStart_684063 baseEnd_684063 := by
    simpa [prefixWord, tailWord_684063, baseEnd_684063] using wordTrace_append hprefix tailTrace_684063
  have hstable : (prefixWord ++ tailWord_684063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684063).length < 2 ^ (prefixWord ++ tailWord_684063).sum := by decide
  have hdescent : baseEnd_684063 < baseStart_684063 := by decide
  rcases family_descends (prefixWord ++ tailWord_684063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684071 : List Nat := [1, 1, 7, 1, 3, 1, 1, 3, 1, 3]
def baseStart_684071 : Nat := 118140960795 + 684071 * 2 ^ 59
def prefixEnd_684071 : Nat := 4983230072969 + 3 ^ 40 * 684071 * 2
def baseEnd_684071 : Nat := 234171483201265535177681

theorem tailTrace_684071 : CollatzResearch.WordTrace tailWord_684071 prefixEnd_684071 234171483201265535177681 := by
  unfold tailWord_684071
  simp only [CollatzResearch.WordTrace]
  refine ⟨24950119104735071870596067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16633412736490047913730711 24950119104735071870596067)
  ·
    refine ⟨37425178657102607805894101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24950119104735071870596067 37425178657102607805894101)
    ·
      refine ⟨877152624775842370450643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 37425178657102607805894101 877152624775842370450643)
      ·
        refine ⟨1315728937163763555675965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 877152624775842370450643 1315728937163763555675965)
        ·
          refine ⟨493398351436411333378487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1315728937163763555675965 493398351436411333378487)
          ·
            refine ⟨740097527154617000067731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493398351436411333378487 740097527154617000067731)
            ·
              refine ⟨1110146290731925500101597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740097527154617000067731 1110146290731925500101597)
              ·
                refine ⟨416304859024472062538099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1110146290731925500101597 416304859024472062538099)
                ·
                  refine ⟨624457288536708093807149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 416304859024472062538099 624457288536708093807149)
                  ·
                    refine ⟨234171483201265535177681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 624457288536708093807149 234171483201265535177681)
                    ·
                      rfl

theorem cell22_684071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_684071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684071 prefixEnd_684071 := by exact prefixLift 684071
  have htrace : WordTrace (prefixWord ++ tailWord_684071) baseStart_684071 baseEnd_684071 := by
    simpa [prefixWord, tailWord_684071, baseEnd_684071] using wordTrace_append hprefix tailTrace_684071
  have hstable : (prefixWord ++ tailWord_684071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684071).length < 2 ^ (prefixWord ++ tailWord_684071).sum := by decide
  have hdescent : baseEnd_684071 < baseStart_684071 := by decide
  rcases family_descends (prefixWord ++ tailWord_684071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684091 : List Nat := [1, 1, 1, 1, 1, 2, 1, 8, 2, 4]
def baseStart_684091 : Nat := 118140960795 + 684091 * 2 ^ 59
def prefixEnd_684091 : Nat := 4983230072969 + 3 ^ 40 * 684091 * 2
def baseEnd_684091 : Nat := 234178329609992149677619

theorem tailTrace_684091 : CollatzResearch.WordTrace tailWord_684091 prefixEnd_684091 234178329609992149677619 := by
  unfold tailWord_684091
  simp only [CollatzResearch.WordTrace]
  refine ⟨24950848564662615286324127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16633899043108410190882751 24950848564662615286324127)
  ·
    refine ⟨37426272846993922929486191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24950848564662615286324127 37426272846993922929486191)
    ·
      refine ⟨56139409270490884394229287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37426272846993922929486191 56139409270490884394229287)
      ·
        refine ⟨84209113905736326591343931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56139409270490884394229287 84209113905736326591343931)
        ·
          refine ⟨126313670858604489887015897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84209113905736326591343931 126313670858604489887015897)
          ·
            refine ⟨94735253143953367415261923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126313670858604489887015897 94735253143953367415261923)
            ·
              refine ⟨142102879715930051122892885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94735253143953367415261923 142102879715930051122892885)
              ·
                refine ⟨1665268121671055286596401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 142102879715930051122892885 1665268121671055286596401)
                ·
                  refine ⟨1248951091253291464947301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1665268121671055286596401 1248951091253291464947301)
                  ·
                    refine ⟨234178329609992149677619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1248951091253291464947301 234178329609992149677619)
                    ·
                      rfl

theorem cell22_684091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 4].length) (baseStart_684091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684091 prefixEnd_684091 := by exact prefixLift 684091
  have htrace : WordTrace (prefixWord ++ tailWord_684091) baseStart_684091 baseEnd_684091 := by
    simpa [prefixWord, tailWord_684091, baseEnd_684091] using wordTrace_append hprefix tailTrace_684091
  have hstable : (prefixWord ++ tailWord_684091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684091).length < 2 ^ (prefixWord ++ tailWord_684091).sum := by decide
  have hdescent : baseEnd_684091 < baseStart_684091 := by decide
  rcases family_descends (prefixWord ++ tailWord_684091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684093 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 4, 3]
def baseStart_684093 : Nat := 118140960795 + 684093 * 2 ^ 59
def prefixEnd_684093 : Nat := 4983230072969 + 3 ^ 40 * 684093 * 2
def baseEnd_684093 : Nat := 234179014250864811127613

theorem tailTrace_684093 : CollatzResearch.WordTrace tailWord_684093 prefixEnd_684093 234179014250864811127613 := by
  unfold tailWord_684093
  simp only [CollatzResearch.WordTrace]
  refine ⟨24950921510655369627896933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16633947673770246418597955 24950921510655369627896933)
  ·
    refine ⟨4678297783247881805230675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24950921510655369627896933 4678297783247881805230675)
    ·
      refine ⟨7017446674871822707846013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4678297783247881805230675 7017446674871822707846013)
      ·
        refine ⟨2631542503076933515442255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7017446674871822707846013 2631542503076933515442255)
        ·
          refine ⟨3947313754615400273163383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2631542503076933515442255 3947313754615400273163383)
          ·
            refine ⟨5920970631923100409745075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3947313754615400273163383 5920970631923100409745075)
            ·
              refine ⟨8881455947884650614617613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5920970631923100409745075 8881455947884650614617613)
              ·
                refine ⟨3330545980456743980481605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8881455947884650614617613 3330545980456743980481605)
                ·
                  refine ⟨624477371335639496340301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3330545980456743980481605 624477371335639496340301)
                  ·
                    refine ⟨234179014250864811127613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 624477371335639496340301 234179014250864811127613)
                    ·
                      rfl

theorem cell22_684093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_684093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684093 prefixEnd_684093 := by exact prefixLift 684093
  have htrace : WordTrace (prefixWord ++ tailWord_684093) baseStart_684093 baseEnd_684093 := by
    simpa [prefixWord, tailWord_684093, baseEnd_684093] using wordTrace_append hprefix tailTrace_684093
  have hstable : (prefixWord ++ tailWord_684093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684093).length < 2 ^ (prefixWord ++ tailWord_684093).sum := by decide
  have hdescent : baseEnd_684093 < baseStart_684093 := by decide
  rcases family_descends (prefixWord ++ tailWord_684093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684110 : List Nat := [4, 1, 1, 1, 1, 5, 1, 3, 2, 3]
def baseStart_684110 : Nat := 118140960795 + 684110 * 2 ^ 59
def prefixEnd_684110 : Nat := 4983230072969 + 3 ^ 40 * 684110 * 2
def baseEnd_684110 : Nat := 234184833698282433452561

theorem tailTrace_684110 : CollatzResearch.WordTrace tailWord_684110 prefixEnd_684110 234184833698282433452561 := by
  unfold tailWord_684110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3118942693949222691408223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16634361034395854354177189 3118942693949222691408223)
  ·
    refine ⟨4678414040923834037112335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3118942693949222691408223 4678414040923834037112335)
    ·
      refine ⟨7017621061385751055668503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4678414040923834037112335 7017621061385751055668503)
      ·
        refine ⟨10526431592078626583502755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7017621061385751055668503 10526431592078626583502755)
        ·
          refine ⟨15789647388117939875254133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10526431592078626583502755 15789647388117939875254133)
          ·
            refine ⟨1480279442636056863305075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15789647388117939875254133 1480279442636056863305075)
            ·
              refine ⟨2220419163954085294957613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1480279442636056863305075 2220419163954085294957613)
              ·
                refine ⟨832657186482781985609105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2220419163954085294957613 832657186482781985609105)
                ·
                  refine ⟨624492889862086489206829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 832657186482781985609105 624492889862086489206829)
                  ·
                    refine ⟨234184833698282433452561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 624492889862086489206829 234184833698282433452561)
                    ·
                      rfl

theorem cell22_684110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_684110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684110 prefixEnd_684110 := by exact prefixLift 684110
  have htrace : WordTrace (prefixWord ++ tailWord_684110) baseStart_684110 baseEnd_684110 := by
    simpa [prefixWord, tailWord_684110, baseEnd_684110] using wordTrace_append hprefix tailTrace_684110
  have hstable : (prefixWord ++ tailWord_684110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684110).length < 2 ^ (prefixWord ++ tailWord_684110).sum := by decide
  have hdescent : baseEnd_684110 < baseStart_684110 := by decide
  rcases family_descends (prefixWord ++ tailWord_684110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684125 : List Nat := [1, 4, 4, 1, 1, 1, 1, 3, 2, 4]
def baseStart_684125 : Nat := 118140960795 + 684125 * 2 ^ 59
def prefixEnd_684125 : Nat := 4983230072969 + 3 ^ 40 * 684125 * 2
def baseEnd_684125 : Nat := 234189968504827394327515

theorem tailTrace_684125 : CollatzResearch.WordTrace tailWord_684125 prefixEnd_684125 234189968504827394327515 := by
  unfold tailWord_684125
  simp only [CollatzResearch.WordTrace]
  refine ⟨24952088646539439093061829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16634725764359626062041219 24952088646539439093061829)
  ·
    refine ⟨4678516621226144829949093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24952088646539439093061829 4678516621226144829949093)
    ·
      refine ⟨877221866479902155615455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4678516621226144829949093 877221866479902155615455)
      ·
        refine ⟨1315832799719853233423183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 877221866479902155615455 1315832799719853233423183)
        ·
          refine ⟨1973749199579779850134775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1315832799719853233423183 1973749199579779850134775)
          ·
            refine ⟨2960623799369669775202163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1973749199579779850134775 2960623799369669775202163)
            ·
              refine ⟨4440935699054504662803245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2960623799369669775202163 4440935699054504662803245)
              ·
                refine ⟨1665350887145439248551217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4440935699054504662803245 1665350887145439248551217)
                ·
                  refine ⟨1249013165359079436413413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1665350887145439248551217 1249013165359079436413413)
                  ·
                    refine ⟨234189968504827394327515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1249013165359079436413413 234189968504827394327515)
                    ·
                      rfl

theorem cell22_684125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_684125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684125 prefixEnd_684125 := by exact prefixLift 684125
  have htrace : WordTrace (prefixWord ++ tailWord_684125) baseStart_684125 baseEnd_684125 := by
    simpa [prefixWord, tailWord_684125, baseEnd_684125] using wordTrace_append hprefix tailTrace_684125
  have hstable : (prefixWord ++ tailWord_684125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684125).length < 2 ^ (prefixWord ++ tailWord_684125).sum := by decide
  have hdescent : baseEnd_684125 < baseStart_684125 := by decide
  rcases family_descends (prefixWord ++ tailWord_684125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684320 : List Nat := [2, 1, 1, 5, 2, 1, 1, 4, 5]
def baseStart_684320 : Nat := 118140960795 + 684320 * 2 ^ 59
def prefixEnd_684320 : Nat := 4983230072969 + 3 ^ 40 * 684320 * 2
def baseEnd_684320 : Nat := 78085573663303961900639

theorem tailTrace_684320 : CollatzResearch.WordTrace tailWord_684320 prefixEnd_684320 78085573663303961900639 := by
  unfold tailWord_684320
  simp only [CollatzResearch.WordTrace]
  refine ⟨12479600440416493698205207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16639467253888658264273609 12479600440416493698205207)
  ·
    refine ⟨18719400660624740547307811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12479600440416493698205207 18719400660624740547307811)
    ·
      refine ⟨28079100990937110820961717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18719400660624740547307811 28079100990937110820961717)
      ·
        refine ⟨2632415717900354139465161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28079100990937110820961717 2632415717900354139465161)
        ·
          refine ⟨1974311788425265604598871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2632415717900354139465161 1974311788425265604598871)
          ·
            refine ⟨2961467682637898406898307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974311788425265604598871 2961467682637898406898307)
            ·
              refine ⟨4442201523956847610347461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2961467682637898406898307 4442201523956847610347461)
              ·
                refine ⟨832912785741908926940149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4442201523956847610347461 832912785741908926940149)
                ·
                  refine ⟨78085573663303961900639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 832912785741908926940149 78085573663303961900639)
                  ·
                    rfl

theorem cell22_684320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 5].length) (baseStart_684320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684320 prefixEnd_684320 := by exact prefixLift 684320
  have htrace : WordTrace (prefixWord ++ tailWord_684320) baseStart_684320 baseEnd_684320 := by
    simpa [prefixWord, tailWord_684320, baseEnd_684320] using wordTrace_append hprefix tailTrace_684320
  have hstable : (prefixWord ++ tailWord_684320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684320).length < 2 ^ (prefixWord ++ tailWord_684320).sum := by decide
  have hdescent : baseEnd_684320 < baseStart_684320 := by decide
  rcases family_descends (prefixWord ++ tailWord_684320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684324 : List Nat := [2, 3, 1, 3, 1, 3, 1, 4, 1, 3]
def baseStart_684324 : Nat := 118140960795 + 684324 * 2 ^ 59
def prefixEnd_684324 : Nat := 4983230072969 + 3 ^ 40 * 684324 * 2
def baseEnd_684324 : Nat := 234258090271657208601905

theorem tailTrace_684324 : CollatzResearch.WordTrace tailWord_684324 prefixEnd_684324 234258090271657208601905 := by
  unfold tailWord_684324
  simp only [CollatzResearch.WordTrace]
  refine ⟨12479673386409248039778013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16639564515212330719704017 12479673386409248039778013)
  ·
    refine ⟨4679877519903468014916755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12479673386409248039778013 4679877519903468014916755)
    ·
      refine ⟨7019816279855202022375133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4679877519903468014916755 7019816279855202022375133)
      ·
        refine ⟨2632431104945700758390675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7019816279855202022375133 2632431104945700758390675)
        ·
          refine ⟨3948646657418551137586013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2632431104945700758390675 3948646657418551137586013)
          ·
            refine ⟨1480742496531956676594755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3948646657418551137586013 1480742496531956676594755)
            ·
              refine ⟨2221113744797935014892133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1480742496531956676594755 2221113744797935014892133)
              ·
                refine ⟨416458827149612815292275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2221113744797935014892133 416458827149612815292275)
                ·
                  refine ⟨624688240724419222938413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 416458827149612815292275 624688240724419222938413)
                  ·
                    refine ⟨234258090271657208601905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 624688240724419222938413 234258090271657208601905)
                    ·
                      rfl

theorem cell22_684324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_684324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684324 prefixEnd_684324 := by exact prefixLift 684324
  have htrace : WordTrace (prefixWord ++ tailWord_684324) baseStart_684324 baseEnd_684324 := by
    simpa [prefixWord, tailWord_684324, baseEnd_684324] using wordTrace_append hprefix tailTrace_684324
  have hstable : (prefixWord ++ tailWord_684324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684324).length < 2 ^ (prefixWord ++ tailWord_684324).sum := by decide
  have hdescent : baseEnd_684324 < baseStart_684324 := by decide
  rcases family_descends (prefixWord ++ tailWord_684324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684363 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 3, 5]
def baseStart_684363 : Nat := 118140960795 + 684363 * 2 ^ 59
def prefixEnd_684363 : Nat := 4983230072969 + 3 ^ 40 * 684363 * 2
def baseEnd_684363 : Nat := 234271440768674106876785

theorem tailTrace_684363 : CollatzResearch.WordTrace tailWord_684363 prefixEnd_684363 234271440768674106876785 := by
  unfold tailWord_684363
  simp only [CollatzResearch.WordTrace]
  refine ⟨24960769219677205740225743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16640512813118137160150495 24960769219677205740225743)
  ·
    refine ⟨37441153829515808610338615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24960769219677205740225743 37441153829515808610338615)
    ·
      refine ⟨56161730744273712915507923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37441153829515808610338615 56161730744273712915507923)
      ·
        refine ⟨84242596116410569373261885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56161730744273712915507923 84242596116410569373261885)
        ·
          refine ⟨31590973543653963514973207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84242596116410569373261885 31590973543653963514973207)
          ·
            refine ⟨47386460315480945272459811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31590973543653963514973207 47386460315480945272459811)
            ·
              refine ⟨71079690473221417908689717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47386460315480945272459811 71079690473221417908689717)
              ·
                refine ⟨6663720981864507928939661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71079690473221417908689717 6663720981864507928939661)
                ·
                  refine ⟨2498895368199190473352373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6663720981864507928939661 2498895368199190473352373)
                  ·
                    refine ⟨234271440768674106876785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2498895368199190473352373 234271440768674106876785)
                    ·
                      rfl

theorem cell22_684363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 5].length) (baseStart_684363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684363 prefixEnd_684363 := by exact prefixLift 684363
  have htrace : WordTrace (prefixWord ++ tailWord_684363) baseStart_684363 baseEnd_684363 := by
    simpa [prefixWord, tailWord_684363, baseEnd_684363] using wordTrace_append hprefix tailTrace_684363
  have hstable : (prefixWord ++ tailWord_684363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684363).length < 2 ^ (prefixWord ++ tailWord_684363).sum := by decide
  have hdescent : baseEnd_684363 < baseStart_684363 := by decide
  rcases family_descends (prefixWord ++ tailWord_684363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684393 : List Nat := [1, 2, 1, 1, 1, 3, 4, 9]
def baseStart_684393 : Nat := 118140960795 + 684393 * 2 ^ 59
def prefixEnd_684393 : Nat := 4983230072969 + 3 ^ 40 * 684393 * 2
def baseEnd_684393 : Nat := 26031301153529336514077

theorem tailTrace_684393 : CollatzResearch.WordTrace tailWord_684393 prefixEnd_684393 26031301153529336514077 := by
  unfold tailWord_684393
  simp only [CollatzResearch.WordTrace]
  refine ⟨24961863409568520863817833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16641242273045680575878555 24961863409568520863817833)
  ·
    refine ⟨18721397557176390647863375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24961863409568520863817833 18721397557176390647863375)
    ·
      refine ⟨28082096335764585971795063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18721397557176390647863375 28082096335764585971795063)
      ·
        refine ⟨42123144503646878957692595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28082096335764585971795063 42123144503646878957692595)
        ·
          refine ⟨63184716755470318436538893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42123144503646878957692595 63184716755470318436538893)
          ·
            refine ⟨23694268783301369413702085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63184716755470318436538893 23694268783301369413702085)
            ·
              refine ⟨4442675396869006765069141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23694268783301369413702085 4442675396869006765069141)
              ·
                refine ⟨26031301153529336514077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4442675396869006765069141 26031301153529336514077)
                ·
                  rfl

theorem cell22_684393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 9].length) (baseStart_684393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684393 prefixEnd_684393 := by exact prefixLift 684393
  have htrace : WordTrace (prefixWord ++ tailWord_684393) baseStart_684393 baseEnd_684393 := by
    simpa [prefixWord, tailWord_684393, baseEnd_684393] using wordTrace_append hprefix tailTrace_684393
  have hstable : (prefixWord ++ tailWord_684393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684393).length < 2 ^ (prefixWord ++ tailWord_684393).sum := by decide
  have hdescent : baseEnd_684393 < baseStart_684393 := by decide
  rcases family_descends (prefixWord ++ tailWord_684393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684549 : List Nat := [1, 3, 1, 1, 2, 2, 5, 2, 2, 3]
def baseStart_684549 : Nat := 118140960795 + 684549 * 2 ^ 59
def prefixEnd_684549 : Nat := 4983230072969 + 3 ^ 40 * 684549 * 2
def baseEnd_684549 : Nat := 234335112369831621726215

theorem tailTrace_684549 : CollatzResearch.WordTrace tailWord_684549 prefixEnd_684549 234335112369831621726215 := by
  unfold tailWord_684549
  simp only [CollatzResearch.WordTrace]
  refine ⟨24967553197003359506496701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16645035464668906337664467 24967553197003359506496701)
  ·
    refine ⟨9362832448876259814936263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24967553197003359506496701 9362832448876259814936263)
    ·
      refine ⟨14044248673314389722404395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9362832448876259814936263 14044248673314389722404395)
      ·
        refine ⟨21066373009971584583606593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14044248673314389722404395 21066373009971584583606593)
        ·
          refine ⟨15799779757478688437704945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21066373009971584583606593 15799779757478688437704945)
          ·
            refine ⟨11849834818109016328278709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15799779757478688437704945 11849834818109016328278709)
            ·
              refine ⟨1110922014197720280776129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11849834818109016328278709 1110922014197720280776129)
              ·
                refine ⟨833191510648290210582097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1110922014197720280776129 833191510648290210582097)
                ·
                  refine ⟨624893632986217657936573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 833191510648290210582097 624893632986217657936573)
                  ·
                    refine ⟨234335112369831621726215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 624893632986217657936573 234335112369831621726215)
                    ·
                      rfl

theorem cell22_684549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_684549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684549 prefixEnd_684549 := by exact prefixLift 684549
  have htrace : WordTrace (prefixWord ++ tailWord_684549) baseStart_684549 baseEnd_684549 := by
    simpa [prefixWord, tailWord_684549, baseEnd_684549] using wordTrace_append hprefix tailTrace_684549
  have hstable : (prefixWord ++ tailWord_684549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684549).length < 2 ^ (prefixWord ++ tailWord_684549).sum := by decide
  have hdescent : baseEnd_684549 < baseStart_684549 := by decide
  rcases family_descends (prefixWord ++ tailWord_684549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684564 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_684564 : Nat := 118140960795 + 684564 * 2 ^ 59
def prefixEnd_684564 : Nat := 4983230072969 + 3 ^ 40 * 684564 * 2
def baseEnd_684564 : Nat := 234340247176376582601169

theorem tailTrace_684564 : CollatzResearch.WordTrace tailWord_684564 prefixEnd_684564 234340247176376582601169 := by
  unfold tailWord_684564
  simp only [CollatzResearch.WordTrace]
  refine ⟨12484050145974508534146373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16645400194632678045528497 12484050145974508534146373)
  ·
    refine ⟨2340759402370220350152445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12484050145974508534146373 2340759402370220350152445)
    ·
      refine ⟨877784775888832631307167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2340759402370220350152445 877784775888832631307167)
      ·
        refine ⟨1316677163833248946960751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 877784775888832631307167 1316677163833248946960751)
        ·
          refine ⟨1975015745749873420441127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1316677163833248946960751 1975015745749873420441127)
          ·
            refine ⟨2962523618624810130661691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1975015745749873420441127 2962523618624810130661691)
            ·
              refine ⟨4443785427937215195992537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2962523618624810130661691 4443785427937215195992537)
              ·
                refine ⟨3332839070952911396994403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4443785427937215195992537 3332839070952911396994403)
                ·
                  refine ⟨4999258606429367095491605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3332839070952911396994403 4999258606429367095491605)
                  ·
                    refine ⟨234340247176376582601169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4999258606429367095491605 234340247176376582601169)
                    ·
                      rfl

theorem cell22_684564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_684564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684564 prefixEnd_684564 := by exact prefixLift 684564
  have htrace : WordTrace (prefixWord ++ tailWord_684564) baseStart_684564 baseEnd_684564 := by
    simpa [prefixWord, tailWord_684564, baseEnd_684564] using wordTrace_append hprefix tailTrace_684564
  have hstable : (prefixWord ++ tailWord_684564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684564).length < 2 ^ (prefixWord ++ tailWord_684564).sum := by decide
  have hdescent : baseEnd_684564 < baseStart_684564 := by decide
  rcases family_descends (prefixWord ++ tailWord_684564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684579 : List Nat := [1, 1, 1, 4, 4, 3, 2, 6]
def baseStart_684579 : Nat := 118140960795 + 684579 * 2 ^ 59
def prefixEnd_684579 : Nat := 4983230072969 + 3 ^ 40 * 684579 * 2
def baseEnd_684579 : Nat := 26038375775880171497347

theorem tailTrace_684579 : CollatzResearch.WordTrace tailWord_684579 prefixEnd_684579 26038375775880171497347 := by
  unfold tailWord_684579
  simp only [CollatzResearch.WordTrace]
  refine ⟨24968647386894674630088791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16645764924596449753392527 24968647386894674630088791)
  ·
    refine ⟨37452971080342011945133187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24968647386894674630088791 37452971080342011945133187)
    ·
      refine ⟨56179456620513017917699781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37452971080342011945133187 56179456620513017917699781)
      ·
        refine ⟨10533648116346190859568709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56179456620513017917699781 10533648116346190859568709)
        ·
          refine ⟨1975059021814910786169133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10533648116346190859568709 1975059021814910786169133)
          ·
            refine ⟨740647133180591544813425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1975059021814910786169133 740647133180591544813425)
            ·
              refine ⟨555485349885443658610069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 740647133180591544813425 555485349885443658610069)
              ·
                refine ⟨26038375775880171497347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 555485349885443658610069 26038375775880171497347)
                ·
                  rfl

theorem cell22_684579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 6].length) (baseStart_684579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684579 prefixEnd_684579 := by exact prefixLift 684579
  have htrace : WordTrace (prefixWord ++ tailWord_684579) baseStart_684579 baseEnd_684579 := by
    simpa [prefixWord, tailWord_684579, baseEnd_684579] using wordTrace_append hprefix tailTrace_684579
  have hstable : (prefixWord ++ tailWord_684579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684579).length < 2 ^ (prefixWord ++ tailWord_684579).sum := by decide
  have hdescent : baseEnd_684579 < baseStart_684579 := by decide
  rcases family_descends (prefixWord ++ tailWord_684579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684596 : List Nat := [2, 5, 1, 3, 1, 2, 8]
def baseStart_684596 : Nat := 118140960795 + 684596 * 2 ^ 59
def prefixEnd_684596 : Nat := 4983230072969 + 3 ^ 40 * 684596 * 2
def baseEnd_684596 : Nat := 8679674127049598733373

theorem tailTrace_684596 : CollatzResearch.WordTrace tailWord_684596 prefixEnd_684596 8679674127049598733373 := by
  unfold tailWord_684596
  simp only [CollatzResearch.WordTrace]
  refine ⟨12484633713916543266728821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16646178285222057688971761 12484633713916543266728821)
  ·
    refine ⟨1170434410679675931255827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12484633713916543266728821 1170434410679675931255827)
    ·
      refine ⟨1755651616019513896883741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1170434410679675931255827 1755651616019513896883741)
      ·
        refine ⟨658369356007317711331403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1755651616019513896883741 658369356007317711331403)
        ·
          refine ⟨987554034010976566997105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658369356007317711331403 987554034010976566997105)
          ·
            refine ⟨740665525508232425247829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 987554034010976566997105 740665525508232425247829)
            ·
              refine ⟨8679674127049598733373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 740665525508232425247829 8679674127049598733373)
              ·
                rfl

theorem cell22_684596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 8].length) (baseStart_684596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684596 prefixEnd_684596 := by exact prefixLift 684596
  have htrace : WordTrace (prefixWord ++ tailWord_684596) baseStart_684596 baseEnd_684596 := by
    simpa [prefixWord, tailWord_684596, baseEnd_684596] using wordTrace_append hprefix tailTrace_684596
  have hstable : (prefixWord ++ tailWord_684596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684596).length < 2 ^ (prefixWord ++ tailWord_684596).sum := by decide
  have hdescent : baseEnd_684596 < baseStart_684596 := by decide
  rcases family_descends (prefixWord ++ tailWord_684596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684607 : List Nat := [1, 1, 2, 2, 3, 2, 2, 4, 5]
def baseStart_684607 : Nat := 118140960795 + 684607 * 2 ^ 59
def prefixEnd_684607 : Nat := 4983230072969 + 3 ^ 40 * 684607 * 2
def baseEnd_684607 : Nat := 78118322318379601258679

theorem tailTrace_684607 : CollatzResearch.WordTrace tailWord_684607 prefixEnd_684607 78118322318379601258679 := by
  unfold tailWord_684607
  simp only [CollatzResearch.WordTrace]
  refine ⟨24969668630793235412108075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16646445753862156941405383 24969668630793235412108075)
  ·
    refine ⟨37454502946189853118162113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24969668630793235412108075 37454502946189853118162113)
    ·
      refine ⟨28090877209642389838621585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37454502946189853118162113 28090877209642389838621585)
      ·
        refine ⟨21068157907231792378966189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28090877209642389838621585 21068157907231792378966189)
        ·
          refine ⟨7900559215211922142112321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21068157907231792378966189 7900559215211922142112321)
          ·
            refine ⟨5925419411408941606584241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7900559215211922142112321 5925419411408941606584241)
            ·
              refine ⟨4444064558556706204938181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5925419411408941606584241 4444064558556706204938181)
              ·
                refine ⟨833262104729382413425909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4444064558556706204938181 833262104729382413425909)
                ·
                  refine ⟨78118322318379601258679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 833262104729382413425909 78118322318379601258679)
                  ·
                    rfl

theorem cell22_684607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 5].length) (baseStart_684607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684607 prefixEnd_684607 := by exact prefixLift 684607
  have htrace : WordTrace (prefixWord ++ tailWord_684607) baseStart_684607 baseEnd_684607 := by
    simpa [prefixWord, tailWord_684607, baseEnd_684607] using wordTrace_append hprefix tailTrace_684607
  have hstable : (prefixWord ++ tailWord_684607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684607).length < 2 ^ (prefixWord ++ tailWord_684607).sum := by decide
  have hdescent : baseEnd_684607 < baseStart_684607 := by decide
  rcases family_descends (prefixWord ++ tailWord_684607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684622 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_684622 : Nat := 118140960795 + 684622 * 2 ^ 59
def prefixEnd_684622 : Nat := 4983230072969 + 3 ^ 40 * 684622 * 2
def baseEnd_684622 : Nat := 234360101761683764650991

theorem tailTrace_684622 : CollatzResearch.WordTrace tailWord_684622 prefixEnd_684622 234360101761683764650991 := by
  unfold tailWord_684622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3121276965717361621738015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16646810483825928649269413 3121276965717361621738015)
  ·
    refine ⟨4681915448576042432607023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3121276965717361621738015 4681915448576042432607023)
    ·
      refine ⟨7022873172864063648910535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4681915448576042432607023 7022873172864063648910535)
      ·
        refine ⟨10534309759296095473365803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7022873172864063648910535 10534309759296095473365803)
        ·
          refine ⟨15801464638944143210048705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10534309759296095473365803 15801464638944143210048705)
          ·
            refine ⟨11851098479208107407536529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15801464638944143210048705 11851098479208107407536529)
            ·
              refine ⟨8888323859406080555652397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11851098479208107407536529 8888323859406080555652397)
              ·
                refine ⟨3333121447277280208369649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8888323859406080555652397 3333121447277280208369649)
                ·
                  refine ⟨2499841085457960156277237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3333121447277280208369649 2499841085457960156277237)
                  ·
                    refine ⟨234360101761683764650991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2499841085457960156277237 234360101761683764650991)
                    ·
                      rfl

theorem cell22_684622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_684622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684622 prefixEnd_684622 := by exact prefixLift 684622
  have htrace : WordTrace (prefixWord ++ tailWord_684622) baseStart_684622 baseEnd_684622 := by
    simpa [prefixWord, tailWord_684622, baseEnd_684622] using wordTrace_append hprefix tailTrace_684622
  have hstable : (prefixWord ++ tailWord_684622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684622).length < 2 ^ (prefixWord ++ tailWord_684622).sum := by decide
  have hdescent : baseEnd_684622 < baseStart_684622 := by decide
  rcases family_descends (prefixWord ++ tailWord_684622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684662 : List Nat := [5, 1, 1, 2, 3, 2, 2, 2, 1, 3]
def baseStart_684662 : Nat := 118140960795 + 684662 * 2 ^ 59
def prefixEnd_684662 : Nat := 4983230072969 + 3 ^ 40 * 684662 * 2
def baseEnd_684662 : Nat := 234373794579136993650869

theorem tailTrace_684662 : CollatzResearch.WordTrace tailWord_684662 prefixEnd_684662 234373794579136993650869 := by
  unfold tailWord_684662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1560729665349623737835015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16647783097062653203573493 1560729665349623737835015)
  ·
    refine ⟨2341094498024435606752523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1560729665349623737835015 2341094498024435606752523)
    ·
      refine ⟨3511641747036653410128785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2341094498024435606752523 3511641747036653410128785)
      ·
        refine ⟨2633731310277490057596589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3511641747036653410128785 2633731310277490057596589)
        ·
          refine ⟨987649241354058771598721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2633731310277490057596589 987649241354058771598721)
          ·
            refine ⟨740736931015544078699041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 987649241354058771598721 740736931015544078699041)
            ·
              refine ⟨555552698261658059024281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 740736931015544078699041 555552698261658059024281)
              ·
                refine ⟨416664523696243544268211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 555552698261658059024281 416664523696243544268211)
                ·
                  refine ⟨624996785544365316402317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 416664523696243544268211 624996785544365316402317)
                  ·
                    refine ⟨234373794579136993650869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 624996785544365316402317 234373794579136993650869)
                    ·
                      rfl

theorem cell22_684662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_684662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684662 prefixEnd_684662 := by exact prefixLift 684662
  have htrace : WordTrace (prefixWord ++ tailWord_684662) baseStart_684662 baseEnd_684662 := by
    simpa [prefixWord, tailWord_684662, baseEnd_684662] using wordTrace_append hprefix tailTrace_684662
  have hstable : (prefixWord ++ tailWord_684662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684662).length < 2 ^ (prefixWord ++ tailWord_684662).sum := by decide
  have hdescent : baseEnd_684662 < baseStart_684662 := by decide
  rcases family_descends (prefixWord ++ tailWord_684662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684705 : List Nat := [1, 2, 3, 3, 4, 1, 2, 1, 1, 4]
def baseStart_684705 : Nat := 118140960795 + 684705 * 2 ^ 59
def prefixEnd_684705 : Nat := 4983230072969 + 3 ^ 40 * 684705 * 2
def baseEnd_684705 : Nat := 234388514357899214825737

theorem tailTrace_684705 : CollatzResearch.WordTrace tailWord_684705 prefixEnd_684705 234388514357899214825737 := by
  unfold tailWord_684705
  simp only [CollatzResearch.WordTrace]
  refine ⟨24973242984438198149175569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16648828656292132099450379 24973242984438198149175569)
  ·
    refine ⟨18729932238328648611881677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24973242984438198149175569 18729932238328648611881677)
    ·
      refine ⟨7023724589373243229455629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18729932238328648611881677 7023724589373243229455629)
      ·
        refine ⟨2633896721014966211045861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7023724589373243229455629 2633896721014966211045861)
        ·
          refine ⟨493855635190306164571099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2633896721014966211045861 493855635190306164571099)
          ·
            refine ⟨740783452785459246856649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493855635190306164571099 740783452785459246856649)
            ·
              refine ⟨555587589589094435142487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 740783452785459246856649 555587589589094435142487)
              ·
                refine ⟨833381384383641652713731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 555587589589094435142487 833381384383641652713731)
                ·
                  refine ⟨1250072076575462479070597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 833381384383641652713731 1250072076575462479070597)
                  ·
                    refine ⟨234388514357899214825737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1250072076575462479070597 234388514357899214825737)
                    ·
                      rfl

theorem cell22_684705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_684705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684705 prefixEnd_684705 := by exact prefixLift 684705
  have htrace : WordTrace (prefixWord ++ tailWord_684705) baseStart_684705 baseEnd_684705 := by
    simpa [prefixWord, tailWord_684705, baseEnd_684705] using wordTrace_append hprefix tailTrace_684705
  have hstable : (prefixWord ++ tailWord_684705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684705).length < 2 ^ (prefixWord ++ tailWord_684705).sum := by decide
  have hdescent : baseEnd_684705 < baseStart_684705 := by decide
  rcases family_descends (prefixWord ++ tailWord_684705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684718 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 4, 3]
def baseStart_684718 : Nat := 118140960795 + 684718 * 2 ^ 59
def prefixEnd_684718 : Nat := 4983230072969 + 3 ^ 40 * 684718 * 2
def baseEnd_684718 : Nat := 234392964523571514250697

theorem tailTrace_684718 : CollatzResearch.WordTrace tailWord_684718 prefixEnd_684718 234392964523571514250697 := by
  unfold tailWord_684718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3121714641673887671174851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16649144755594067579599205 3121714641673887671174851)
  ·
    refine ⟨4682571962510831506762277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3121714641673887671174851 4682571962510831506762277)
    ·
      refine ⟨877982242970780907517927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4682571962510831506762277 877982242970780907517927)
      ·
        refine ⟨1316973364456171361276891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 877982242970780907517927 1316973364456171361276891)
        ·
          refine ⟨1975460046684257041915337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1316973364456171361276891 1975460046684257041915337)
          ·
            refine ⟨1481595035013192781436503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1975460046684257041915337 1481595035013192781436503)
            ·
              refine ⟨2222392552519789172154755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1481595035013192781436503 2222392552519789172154755)
              ·
                refine ⟨3333588828779683758232133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2222392552519789172154755 3333588828779683758232133)
                ·
                  refine ⟨625047905396190704668525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3333588828779683758232133 625047905396190704668525)
                  ·
                    refine ⟨234392964523571514250697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 625047905396190704668525 234392964523571514250697)
                    ·
                      rfl

theorem cell22_684718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_684718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684718 prefixEnd_684718 := by exact prefixLift 684718
  have htrace : WordTrace (prefixWord ++ tailWord_684718) baseStart_684718 baseEnd_684718 := by
    simpa [prefixWord, tailWord_684718, baseEnd_684718] using wordTrace_append hprefix tailTrace_684718
  have hstable : (prefixWord ++ tailWord_684718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684718).length < 2 ^ (prefixWord ++ tailWord_684718).sum := by decide
  have hdescent : baseEnd_684718 < baseStart_684718 := by decide
  rcases family_descends (prefixWord ++ tailWord_684718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684746 : List Nat := [3, 1, 2, 1, 4, 1, 2, 2, 3, 3]
def baseStart_684746 : Nat := 118140960795 + 684746 * 2 ^ 59
def prefixEnd_684746 : Nat := 4983230072969 + 3 ^ 40 * 684746 * 2
def baseEnd_684746 : Nat := 234402549495788774550611

theorem tailTrace_684746 : CollatzResearch.WordTrace tailWord_684746 prefixEnd_684746 234402549495788774550611 := by
  unfold tailWord_684746
  simp only [CollatzResearch.WordTrace]
  refine ⟨6243684594322415537854523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16649825584859774767612061 6243684594322415537854523)
  ·
    refine ⟨9365526891483623306781785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6243684594322415537854523 9365526891483623306781785)
    ·
      refine ⟨7024145168612717480086339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9365526891483623306781785 7024145168612717480086339)
      ·
        refine ⟨10536217752919076220129509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7024145168612717480086339 10536217752919076220129509)
        ·
          refine ⟨1975540828672326791274283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10536217752919076220129509 1975540828672326791274283)
          ·
            refine ⟨2963311243008490186911425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1975540828672326791274283 2963311243008490186911425)
            ·
              refine ⟨2222483432256367640183569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2963311243008490186911425 2222483432256367640183569)
              ·
                refine ⟨1666862574192275730137677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2222483432256367640183569 1666862574192275730137677)
                ·
                  refine ⟨625073465322103398801629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1666862574192275730137677 625073465322103398801629)
                  ·
                    refine ⟨234402549495788774550611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 625073465322103398801629 234402549495788774550611)
                    ·
                      rfl

theorem cell22_684746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_684746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684746 prefixEnd_684746 := by exact prefixLift 684746
  have htrace : WordTrace (prefixWord ++ tailWord_684746) baseStart_684746 baseEnd_684746 := by
    simpa [prefixWord, tailWord_684746, baseEnd_684746] using wordTrace_append hprefix tailTrace_684746
  have hstable : (prefixWord ++ tailWord_684746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684746).length < 2 ^ (prefixWord ++ tailWord_684746).sum := by decide
  have hdescent : baseEnd_684746 < baseStart_684746 := by decide
  rcases family_descends (prefixWord ++ tailWord_684746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684804 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 8]
def baseStart_684804 : Nat := 118140960795 + 684804 * 2 ^ 59
def prefixEnd_684804 : Nat := 4983230072969 + 3 ^ 40 * 684804 * 2
def baseEnd_684804 : Nat := 78140801360365318866811

theorem tailTrace_684804 : CollatzResearch.WordTrace tailWord_684804 prefixEnd_684804 78140801360365318866811 := by
  unfold tailWord_684804
  simp only [CollatzResearch.WordTrace]
  refine ⟨12488426905539769028514733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16651235874053025371352977 12488426905539769028514733)
  ·
    refine ⟨4683160089577413385693025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12488426905539769028514733 4683160089577413385693025)
    ·
      refine ⟨3512370067183060039269769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4683160089577413385693025 3512370067183060039269769)
      ·
        refine ⟨2634277550387295029452327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3512370067183060039269769 2634277550387295029452327)
        ·
          refine ⟨3951416325580942544178491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2634277550387295029452327 3951416325580942544178491)
          ·
            refine ⟨5927124488371413816267737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3951416325580942544178491 5927124488371413816267737)
            ·
              refine ⟨4445343366278560362200803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5927124488371413816267737 4445343366278560362200803)
              ·
                refine ⟨6668015049417840543301205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4445343366278560362200803 6668015049417840543301205)
                ·
                  refine ⟨78140801360365318866811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6668015049417840543301205 78140801360365318866811)
                  ·
                    rfl

theorem cell22_684804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_684804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684804 prefixEnd_684804 := by exact prefixLift 684804
  have htrace : WordTrace (prefixWord ++ tailWord_684804) baseStart_684804 baseEnd_684804 := by
    simpa [prefixWord, tailWord_684804, baseEnd_684804] using wordTrace_append hprefix tailTrace_684804
  have hstable : (prefixWord ++ tailWord_684804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684804).length < 2 ^ (prefixWord ++ tailWord_684804).sum := by decide
  have hdescent : baseEnd_684804 < baseStart_684804 := by decide
  rcases family_descends (prefixWord ++ tailWord_684804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684819 : List Nat := [1, 1, 1, 2, 1, 3, 5, 2, 1, 5]
def baseStart_684819 : Nat := 118140960795 + 684819 * 2 ^ 59
def prefixEnd_684819 : Nat := 4983230072969 + 3 ^ 40 * 684819 * 2
def baseEnd_684819 : Nat := 234427538887640917475387

theorem tailTrace_684819 : CollatzResearch.WordTrace tailWord_684819 prefixEnd_684819 234427538887640917475387 := by
  unfold tailWord_684819
  simp only [CollatzResearch.WordTrace]
  refine ⟨24977400906025195618825511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16651600604016797079217007 24977400906025195618825511)
  ·
    refine ⟨37466101359037793428238267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24977400906025195618825511 37466101359037793428238267)
    ·
      refine ⟨56199152038556690142357401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37466101359037793428238267 56199152038556690142357401)
      ·
        refine ⟨42149364028917517606768051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56199152038556690142357401 42149364028917517606768051)
        ·
          refine ⟨63224046043376276410152077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42149364028917517606768051 63224046043376276410152077)
          ·
            refine ⟨23709017266266103653807029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63224046043376276410152077 23709017266266103653807029)
            ·
              refine ⟨2222720368712447217544409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23709017266266103653807029 2222720368712447217544409)
              ·
                refine ⟨1667040276534335413158307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2222720368712447217544409 1667040276534335413158307)
                ·
                  refine ⟨2500560414801503119737461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1667040276534335413158307 2500560414801503119737461)
                  ·
                    refine ⟨234427538887640917475387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2500560414801503119737461 234427538887640917475387)
                    ·
                      rfl

theorem cell22_684819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 5].length) (baseStart_684819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684819 prefixEnd_684819 := by exact prefixLift 684819
  have htrace : WordTrace (prefixWord ++ tailWord_684819) baseStart_684819 baseEnd_684819 := by
    simpa [prefixWord, tailWord_684819, baseEnd_684819] using wordTrace_append hprefix tailTrace_684819
  have hstable : (prefixWord ++ tailWord_684819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684819).length < 2 ^ (prefixWord ++ tailWord_684819).sum := by decide
  have hdescent : baseEnd_684819 < baseStart_684819 := by decide
  rcases family_descends (prefixWord ++ tailWord_684819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684821 : List Nat := [1, 3, 2, 1, 2, 2, 2, 5, 4]
def baseStart_684821 : Nat := 118140960795 + 684821 * 2 ^ 59
def prefixEnd_684821 : Nat := 4983230072969 + 3 ^ 40 * 684821 * 2
def baseEnd_684821 : Nat := 78142741176171192975127

theorem tailTrace_684821 : CollatzResearch.WordTrace tailWord_684821 prefixEnd_684821 78142741176171192975127 := by
  unfold tailWord_684821
  simp only [CollatzResearch.WordTrace]
  refine ⟨24977473852017949960398317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16651649234678633306932211 24977473852017949960398317)
  ·
    refine ⟨9366552694506731235149369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24977473852017949960398317 9366552694506731235149369)
    ·
      refine ⟨7024914520880048426362027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9366552694506731235149369 7024914520880048426362027)
      ·
        refine ⟨10537371781320072639543041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7024914520880048426362027 10537371781320072639543041)
        ·
          refine ⟨7903028835990054479657281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10537371781320072639543041 7903028835990054479657281)
          ·
            refine ⟨5927271626992540859742961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7903028835990054479657281 5927271626992540859742961)
            ·
              refine ⟨4445453720244405644807221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5927271626992540859742961 4445453720244405644807221)
              ·
                refine ⟨416761286272913029200677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4445453720244405644807221 416761286272913029200677)
                ·
                  refine ⟨78142741176171192975127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 416761286272913029200677 78142741176171192975127)
                  ·
                    rfl

theorem cell22_684821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 4].length) (baseStart_684821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684821 prefixEnd_684821 := by exact prefixLift 684821
  have htrace : WordTrace (prefixWord ++ tailWord_684821) baseStart_684821 baseEnd_684821 := by
    simpa [prefixWord, tailWord_684821, baseEnd_684821] using wordTrace_append hprefix tailTrace_684821
  have hstable : (prefixWord ++ tailWord_684821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684821).length < 2 ^ (prefixWord ++ tailWord_684821).sum := by decide
  have hdescent : baseEnd_684821 < baseStart_684821 := by decide
  rcases family_descends (prefixWord ++ tailWord_684821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684853 : List Nat := [1, 3, 3, 1, 3, 1, 2, 3, 2, 3]
def baseStart_684853 : Nat := 118140960795 + 684853 * 2 ^ 59
def prefixEnd_684853 : Nat := 4983230072969 + 3 ^ 40 * 684853 * 2
def baseEnd_684853 : Nat := 234439177782476162125283

theorem tailTrace_684853 : CollatzResearch.WordTrace tailWord_684853 prefixEnd_684853 234439177782476162125283 := by
  unfold tailWord_684853
  simp only [CollatzResearch.WordTrace]
  refine ⟨24978640987902019425563213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16652427325268012950375475 24978640987902019425563213)
  ·
    refine ⟨9366990370463257284586205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24978640987902019425563213 9366990370463257284586205)
    ·
      refine ⟨3512621388923721481719827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9366990370463257284586205 3512621388923721481719827)
      ·
        refine ⟨5268932083385582222579741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3512621388923721481719827 5268932083385582222579741)
        ·
          refine ⟨1975849531269593333467403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5268932083385582222579741 1975849531269593333467403)
          ·
            refine ⟨2963774296904390000201105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1975849531269593333467403 2963774296904390000201105)
            ·
              refine ⟨2222830722678292500150829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2963774296904390000201105 2222830722678292500150829)
              ·
                refine ⟨833561521004359687556561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2222830722678292500150829 833561521004359687556561)
                ·
                  refine ⟨625171140753269765667421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 833561521004359687556561 625171140753269765667421)
                  ·
                    refine ⟨234439177782476162125283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 625171140753269765667421 234439177782476162125283)
                    ·
                      rfl

theorem cell22_684853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_684853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684853 prefixEnd_684853 := by exact prefixLift 684853
  have htrace : WordTrace (prefixWord ++ tailWord_684853) baseStart_684853 baseEnd_684853 := by
    simpa [prefixWord, tailWord_684853, baseEnd_684853] using wordTrace_append hprefix tailTrace_684853
  have hstable : (prefixWord ++ tailWord_684853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684853).length < 2 ^ (prefixWord ++ tailWord_684853).sum := by decide
  have hdescent : baseEnd_684853 < baseStart_684853 := by decide
  rcases family_descends (prefixWord ++ tailWord_684853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684924 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 2, 8]
def baseStart_684924 : Nat := 118140960795 + 684924 * 2 ^ 59
def prefixEnd_684924 : Nat := 4983230072969 + 3 ^ 40 * 684924 * 2
def baseEnd_684924 : Nat := 234463482533455643600065

theorem tailTrace_684924 : CollatzResearch.WordTrace tailWord_684924 prefixEnd_684924 234463482533455643600065 := by
  unfold tailWord_684924
  simp only [CollatzResearch.WordTrace]
  refine ⟨12490615285322399275698913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16654153713763199034265217 12490615285322399275698913)
  ·
    refine ⟨9367961463991799456774185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12490615285322399275698913 9367961463991799456774185)
    ·
      refine ⟨7025971097993849592580639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9367961463991799456774185 7025971097993849592580639)
      ·
        refine ⟨10538956646990774388870959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7025971097993849592580639 10538956646990774388870959)
        ·
          refine ⟨15808434970486161583306439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10538956646990774388870959 15808434970486161583306439)
          ·
            refine ⟨23712652455729242374959659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15808434970486161583306439 23712652455729242374959659)
            ·
              refine ⟨35568978683593863562439489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23712652455729242374959659 35568978683593863562439489)
              ·
                refine ⟨26676734012695397671829617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35568978683593863562439489 26676734012695397671829617)
                ·
                  refine ⟨20007550509521548253872213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26676734012695397671829617 20007550509521548253872213)
                  ·
                    refine ⟨234463482533455643600065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20007550509521548253872213 234463482533455643600065)
                    ·
                      rfl

theorem cell22_684924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_684924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684924 prefixEnd_684924 := by exact prefixLift 684924
  have htrace : WordTrace (prefixWord ++ tailWord_684924) baseStart_684924 baseEnd_684924 := by
    simpa [prefixWord, tailWord_684924, baseEnd_684924] using wordTrace_append hprefix tailTrace_684924
  have hstable : (prefixWord ++ tailWord_684924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684924).length < 2 ^ (prefixWord ++ tailWord_684924).sum := by decide
  have hdescent : baseEnd_684924 < baseStart_684924 := by decide
  rcases family_descends (prefixWord ++ tailWord_684924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684939 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 8]
def baseStart_684939 : Nat := 118140960795 + 684939 * 2 ^ 59
def prefixEnd_684939 : Nat := 4983230072969 + 3 ^ 40 * 684939 * 2
def baseEnd_684939 : Nat := 78156205780000201491673

theorem tailTrace_684939 : CollatzResearch.WordTrace tailWord_684939 prefixEnd_684939 78156205780000201491673 := by
  unfold tailWord_684939
  simp only [CollatzResearch.WordTrace]
  refine ⟨24981777665590456113193871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16654518443726970742129247 24981777665590456113193871)
  ·
    refine ⟨37472666498385684169790807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24981777665590456113193871 37472666498385684169790807)
    ·
      refine ⟨56208999747578526254686211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37472666498385684169790807 56208999747578526254686211)
      ·
        refine ⟨84313499621367789382029317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56208999747578526254686211 84313499621367789382029317)
        ·
          refine ⟨15808781179006460509130497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84313499621367789382029317 15808781179006460509130497)
          ·
            refine ⟨11856585884254845381847873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15808781179006460509130497 11856585884254845381847873)
            ·
              refine ⟨8892439413191134036385905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11856585884254845381847873 8892439413191134036385905)
              ·
                refine ⟨6669329559893350527289429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8892439413191134036385905 6669329559893350527289429)
                ·
                  refine ⟨78156205780000201491673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6669329559893350527289429 78156205780000201491673)
                  ·
                    rfl

theorem cell22_684939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 8].length) (baseStart_684939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_684939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_684939 prefixEnd_684939 := by exact prefixLift 684939
  have htrace : WordTrace (prefixWord ++ tailWord_684939) baseStart_684939 baseEnd_684939 := by
    simpa [prefixWord, tailWord_684939, baseEnd_684939] using wordTrace_append hprefix tailTrace_684939
  have hstable : (prefixWord ++ tailWord_684939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684939).length < 2 ^ (prefixWord ++ tailWord_684939).sum := by decide
  have hdescent : baseEnd_684939 < baseStart_684939 := by decide
  rcases family_descends (prefixWord ++ tailWord_684939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685018 : List Nat := [3, 1, 1, 2, 4, 3, 1, 7]
def baseStart_685018 : Nat := 118140960795 + 685018 * 2 ^ 59
def prefixEnd_685018 : Nat := 4983230072969 + 3 ^ 40 * 685018 * 2
def baseEnd_685018 : Nat := 26055073406052303527753

theorem tailTrace_685018 : CollatzResearch.WordTrace tailWord_685018 prefixEnd_685018 26055073406052303527753 := by
  unfold tailWord_685018
  simp only [CollatzResearch.WordTrace]
  refine ⟨6246164758076063151329927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16656439354869501736879805 6246164758076063151329927)
  ·
    refine ⟨9369247137114094726994891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6246164758076063151329927 9369247137114094726994891)
    ·
      refine ⟨14053870705671142090492337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9369247137114094726994891 14053870705671142090492337)
      ·
        refine ⟨10540403029253356567869253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14053870705671142090492337 10540403029253356567869253)
        ·
          refine ⟨1976325567985004356475485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10540403029253356567869253 1976325567985004356475485)
          ·
            refine ⟨741122087994376633678307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1976325567985004356475485 741122087994376633678307)
            ·
              refine ⟨1111683131991564950517461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741122087994376633678307 1111683131991564950517461)
              ·
                refine ⟨26055073406052303527753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1111683131991564950517461 26055073406052303527753)
                ·
                  rfl

theorem cell22_685018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 7].length) (baseStart_685018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685018 prefixEnd_685018 := by exact prefixLift 685018
  have htrace : WordTrace (prefixWord ++ tailWord_685018) baseStart_685018 baseEnd_685018 := by
    simpa [prefixWord, tailWord_685018, baseEnd_685018] using wordTrace_append hprefix tailTrace_685018
  have hstable : (prefixWord ++ tailWord_685018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685018).length < 2 ^ (prefixWord ++ tailWord_685018).sum := by decide
  have hdescent : baseEnd_685018 < baseStart_685018 := by decide
  rcases family_descends (prefixWord ++ tailWord_685018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685061 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 4, 5]
def baseStart_685061 : Nat := 118140960795 + 685061 * 2 ^ 59
def prefixEnd_685061 : Nat := 4983230072969 + 3 ^ 40 * 685061 * 2
def baseEnd_685061 : Nat := 234510380433232952924645

theorem tailTrace_685061 : CollatzResearch.WordTrace tailWord_685061 prefixEnd_685061 234510380433232952924645 := by
  unfold tailWord_685061
  simp only [CollatzResearch.WordTrace]
  refine ⟨24986227371148470949135037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16657484914098980632756691 24986227371148470949135037)
  ·
    refine ⟨9369835264180676605925639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24986227371148470949135037 9369835264180676605925639)
    ·
      refine ⟨14054752896271014908888459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9369835264180676605925639 14054752896271014908888459)
      ·
        refine ⟨21082129344406522363332689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14054752896271014908888459 21082129344406522363332689)
        ·
          refine ⟨15811597008304891772499517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21082129344406522363332689 15811597008304891772499517)
          ·
            refine ⟨5929348878114334414687319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15811597008304891772499517 5929348878114334414687319)
            ·
              refine ⟨8894023317171501622030979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5929348878114334414687319 8894023317171501622030979)
              ·
                refine ⟨13341034975757252433046469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8894023317171501622030979 13341034975757252433046469)
                ·
                  refine ⟨2501444057954484831196213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13341034975757252433046469 2501444057954484831196213)
                  ·
                    refine ⟨234510380433232952924645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2501444057954484831196213 234510380433232952924645)
                    ·
                      rfl

theorem cell22_685061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_685061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685061 prefixEnd_685061 := by exact prefixLift 685061
  have htrace : WordTrace (prefixWord ++ tailWord_685061) baseStart_685061 baseEnd_685061 := by
    simpa [prefixWord, tailWord_685061, baseEnd_685061] using wordTrace_append hprefix tailTrace_685061
  have hstable : (prefixWord ++ tailWord_685061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685061).length < 2 ^ (prefixWord ++ tailWord_685061).sum := by decide
  have hdescent : baseEnd_685061 < baseStart_685061 := by decide
  rcases family_descends (prefixWord ++ tailWord_685061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685080 : List Nat := [2, 1, 2, 3, 2, 3, 3, 1, 5]
def baseStart_685080 : Nat := 118140960795 + 685080 * 2 ^ 59
def prefixEnd_685080 : Nat := 4983230072969 + 3 ^ 40 * 685080 * 2
def baseEnd_685080 : Nat := 78172294840507745566529

theorem tailTrace_685080 : CollatzResearch.WordTrace tailWord_685080 prefixEnd_685080 78172294840507745566529 := by
  unfold tailWord_685080
  simp only [CollatzResearch.WordTrace]
  refine ⟨12493460179039818597038347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16657946905386424796051129 12493460179039818597038347)
  ·
    refine ⟨18740190268559727895557521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12493460179039818597038347 18740190268559727895557521)
    ·
      refine ⟨14055142701419795921668141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18740190268559727895557521 14055142701419795921668141)
      ·
        refine ⟨5270678513032423470625553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14055142701419795921668141 5270678513032423470625553)
        ·
          refine ⟨3953008884774317602969165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5270678513032423470625553 3953008884774317602969165)
          ·
            refine ⟨1482378331790369101113437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3953008884774317602969165 1482378331790369101113437)
            ·
              refine ⟨555891874421388412917539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1482378331790369101113437 555891874421388412917539)
              ·
                refine ⟨833837811632082619376309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 555891874421388412917539 833837811632082619376309)
                ·
                  refine ⟨78172294840507745566529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 833837811632082619376309 78172294840507745566529)
                  ·
                    rfl

theorem cell22_685080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 5].length) (baseStart_685080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685080 prefixEnd_685080 := by exact prefixLift 685080
  have htrace : WordTrace (prefixWord ++ tailWord_685080) baseStart_685080 baseEnd_685080 := by
    simpa [prefixWord, tailWord_685080, baseEnd_685080] using wordTrace_append hprefix tailTrace_685080
  have hstable : (prefixWord ++ tailWord_685080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685080).length < 2 ^ (prefixWord ++ tailWord_685080).sum := by decide
  have hdescent : baseEnd_685080 < baseStart_685080 := by decide
  rcases family_descends (prefixWord ++ tailWord_685080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685123 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 4, 3]
def baseStart_685123 : Nat := 118140960795 + 685123 * 2 ^ 59
def prefixEnd_685123 : Nat := 4983230072969 + 3 ^ 40 * 685123 * 2
def baseEnd_685123 : Nat := 234531604300285457874455

theorem tailTrace_685123 : CollatzResearch.WordTrace tailWord_685123 prefixEnd_685123 234531604300285457874455 := by
  unfold tailWord_685123
  simp only [CollatzResearch.WordTrace]
  refine ⟨24988488696923855537892023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16658992464615903691928015 24988488696923855537892023)
  ·
    refine ⟨37482733045385783306838035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24988488696923855537892023 37482733045385783306838035)
    ·
      refine ⟨56224099568078674960257053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37482733045385783306838035 56224099568078674960257053)
      ·
        refine ⟨21084037338029503110096395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56224099568078674960257053 21084037338029503110096395)
        ·
          refine ⟨31626056007044254665144593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21084037338029503110096395 31626056007044254665144593)
          ·
            refine ⟨23719542005283190998858445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31626056007044254665144593 23719542005283190998858445)
            ·
              refine ⟨8894828251981196624571917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23719542005283190998858445 8894828251981196624571917)
              ·
                refine ⟨3335560594492948734214469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8894828251981196624571917 3335560594492948734214469)
                ·
                  refine ⟨625417611467427887665213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3335560594492948734214469 625417611467427887665213)
                  ·
                    refine ⟨234531604300285457874455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 625417611467427887665213 234531604300285457874455)
                    ·
                      rfl

theorem cell22_685123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 3].length) (baseStart_685123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685123 prefixEnd_685123 := by exact prefixLift 685123
  have htrace : WordTrace (prefixWord ++ tailWord_685123) baseStart_685123 baseEnd_685123 := by
    simpa [prefixWord, tailWord_685123, baseEnd_685123] using wordTrace_append hprefix tailTrace_685123
  have hstable : (prefixWord ++ tailWord_685123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685123).length < 2 ^ (prefixWord ++ tailWord_685123).sum := by decide
  have hdescent : baseEnd_685123 < baseStart_685123 := by decide
  rcases family_descends (prefixWord ++ tailWord_685123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685202 : List Nat := [3, 2, 3, 1, 1, 3, 1, 2, 3, 3]
def baseStart_685202 : Nat := 118140960795 + 685202 * 2 ^ 59
def prefixEnd_685202 : Nat := 4983230072969 + 3 ^ 40 * 685202 * 2
def baseEnd_685202 : Nat := 234558647614755585149213

theorem tailTrace_685202 : CollatzResearch.WordTrace tailWord_685202 prefixEnd_685202 234558647614755585149213 := by
  unfold tailWord_685202
  simp only [CollatzResearch.WordTrace]
  refine ⟨6247842515909413007504465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16660913375758434686678573 6247842515909413007504465)
  ·
    refine ⟨4685881886932059755628349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6247842515909413007504465 4685881886932059755628349)
    ·
      refine ⟨1757205707599522408360631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4685881886932059755628349 1757205707599522408360631)
      ·
        refine ⟨2635808561399283612540947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1757205707599522408360631 2635808561399283612540947)
        ·
          refine ⟨3953712842098925418811421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2635808561399283612540947 3953712842098925418811421)
          ·
            refine ⟨1482642315787097032054283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3953712842098925418811421 1482642315787097032054283)
            ·
              refine ⟨2223963473680645548081425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1482642315787097032054283 2223963473680645548081425)
              ·
                refine ⟨1667972605260484161061069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2223963473680645548081425 1667972605260484161061069)
                ·
                  refine ⟨625489726972681560397901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1667972605260484161061069 625489726972681560397901)
                  ·
                    refine ⟨234558647614755585149213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 625489726972681560397901 234558647614755585149213)
                    ·
                      rfl

theorem cell22_685202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_685202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685202 prefixEnd_685202 := by exact prefixLift 685202
  have htrace : WordTrace (prefixWord ++ tailWord_685202) baseStart_685202 baseEnd_685202 := by
    simpa [prefixWord, tailWord_685202, baseEnd_685202] using wordTrace_append hprefix tailTrace_685202
  have hstable : (prefixWord ++ tailWord_685202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685202).length < 2 ^ (prefixWord ++ tailWord_685202).sum := by decide
  have hdescent : baseEnd_685202 < baseStart_685202 := by decide
  rcases family_descends (prefixWord ++ tailWord_685202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685213 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_685213 : Nat := 118140960795 + 685213 * 2 ^ 59
def prefixEnd_685213 : Nat := 4983230072969 + 3 ^ 40 * 685213 * 2
def baseEnd_685213 : Nat := 234562413139555223124179

theorem tailTrace_685213 : CollatzResearch.WordTrace tailWord_685213 prefixEnd_685213 234562413139555223124179 := by
  unfold tailWord_685213
  simp only [CollatzResearch.WordTrace]
  refine ⟨24991771266597800908668293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16661180844398533939112195 24991771266597800908668293)
  ·
    refine ⟨4685957112487087670375305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24991771266597800908668293 4685957112487087670375305)
    ·
      refine ⟨3514467834365315752781479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4685957112487087670375305 3514467834365315752781479)
      ·
        refine ⟨5271701751547973629172219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3514467834365315752781479 5271701751547973629172219)
        ·
          refine ⟨7907552627321960443758329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5271701751547973629172219 7907552627321960443758329)
          ·
            refine ⟨5930664470491470332818747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7907552627321960443758329 5930664470491470332818747)
            ·
              refine ⟨8895996705737205499228121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5930664470491470332818747 8895996705737205499228121)
              ·
                refine ⟨6671997529302904124421091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8895996705737205499228121 6671997529302904124421091)
                ·
                  refine ⟨10007996293954356186631637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6671997529302904124421091 10007996293954356186631637)
                  ·
                    refine ⟨234562413139555223124179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10007996293954356186631637 234562413139555223124179)
                    ·
                      rfl

theorem cell22_685213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_685213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685213 prefixEnd_685213 := by exact prefixLift 685213
  have htrace : WordTrace (prefixWord ++ tailWord_685213) baseStart_685213 baseEnd_685213 := by
    simpa [prefixWord, tailWord_685213, baseEnd_685213] using wordTrace_append hprefix tailTrace_685213
  have hstable : (prefixWord ++ tailWord_685213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685213).length < 2 ^ (prefixWord ++ tailWord_685213).sum := by decide
  have hdescent : baseEnd_685213 < baseStart_685213 := by decide
  rcases family_descends (prefixWord ++ tailWord_685213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685228 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 5, 4]
def baseStart_685228 : Nat := 118140960795 + 685228 * 2 ^ 59
def prefixEnd_685228 : Nat := 4983230072969 + 3 ^ 40 * 685228 * 2
def baseEnd_685228 : Nat := 234567547946100183999133

theorem tailTrace_685228 : CollatzResearch.WordTrace tailWord_685228 prefixEnd_685228 234567547946100183999133 := by
  unfold tailWord_685228
  simp only [CollatzResearch.WordTrace]
  refine ⟨12496159180771729235232169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16661545574362305646976225 12496159180771729235232169)
  ·
    refine ⟨9372119385578796926424127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12496159180771729235232169 9372119385578796926424127)
    ·
      refine ⟨14058179078368195389636191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9372119385578796926424127 14058179078368195389636191)
      ·
        refine ⟨21087268617552293084454287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14058179078368195389636191 21087268617552293084454287)
        ·
          refine ⟨31630902926328439626681431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21087268617552293084454287 31630902926328439626681431)
          ·
            refine ⟨47446354389492659440022147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31630902926328439626681431 47446354389492659440022147)
            ·
              refine ⟨71169531584238989160033221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47446354389492659440022147 71169531584238989160033221)
              ·
                refine ⟨13344287172044810467506229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71169531584238989160033221 13344287172044810467506229)
                ·
                  refine ⟨1251026922379200981328709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13344287172044810467506229 1251026922379200981328709)
                  ·
                    refine ⟨234567547946100183999133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1251026922379200981328709 234567547946100183999133)
                    ·
                      rfl

theorem cell22_685228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_685228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685228 prefixEnd_685228 := by exact prefixLift 685228
  have htrace : WordTrace (prefixWord ++ tailWord_685228) baseStart_685228 baseEnd_685228 := by
    simpa [prefixWord, tailWord_685228, baseEnd_685228] using wordTrace_append hprefix tailTrace_685228
  have hstable : (prefixWord ++ tailWord_685228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685228).length < 2 ^ (prefixWord ++ tailWord_685228).sum := by decide
  have hdescent : baseEnd_685228 < baseStart_685228 := by decide
  rcases family_descends (prefixWord ++ tailWord_685228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685249 : List Nat := [1, 2, 6, 1, 1, 2, 3, 1, 5]
def baseStart_685249 : Nat := 118140960795 + 685249 * 2 ^ 59
def prefixEnd_685249 : Nat := 4983230072969 + 3 ^ 40 * 685249 * 2
def baseEnd_685249 : Nat := 78191578891754376408023

theorem tailTrace_685249 : CollatzResearch.WordTrace tailWord_685249 prefixEnd_685249 78191578891754376408023 := by
  unfold tailWord_685249
  simp only [CollatzResearch.WordTrace]
  refine ⟨24993084294467379056978801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16662056196311586037985867 24993084294467379056978801)
  ·
    refine ⟨18744813220850534292734101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24993084294467379056978801 18744813220850534292734101)
    ·
      refine ⟨878663119727368794971911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18744813220850534292734101 878663119727368794971911)
      ·
        refine ⟨1317994679591053192457867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 878663119727368794971911 1317994679591053192457867)
        ·
          refine ⟨1976992019386579788686801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1317994679591053192457867 1976992019386579788686801)
          ·
            refine ⟨1482744014539934841515101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1976992019386579788686801 1482744014539934841515101)
            ·
              refine ⟨556029005452475565568163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1482744014539934841515101 556029005452475565568163)
              ·
                refine ⟨834043508178713348352245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 556029005452475565568163 834043508178713348352245)
                ·
                  refine ⟨78191578891754376408023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 834043508178713348352245 78191578891754376408023)
                  ·
                    rfl

theorem cell22_685249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 5].length) (baseStart_685249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685249 prefixEnd_685249 := by exact prefixLift 685249
  have htrace : WordTrace (prefixWord ++ tailWord_685249) baseStart_685249 baseEnd_685249 := by
    simpa [prefixWord, tailWord_685249, baseEnd_685249] using wordTrace_append hprefix tailTrace_685249
  have hstable : (prefixWord ++ tailWord_685249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685249).length < 2 ^ (prefixWord ++ tailWord_685249).sum := by decide
  have hdescent : baseEnd_685249 < baseStart_685249 := by decide
  rcases family_descends (prefixWord ++ tailWord_685249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685270 : List Nat := [5, 2, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_685270 : Nat := 118140960795 + 685270 * 2 ^ 59
def prefixEnd_685270 : Nat := 4983230072969 + 3 ^ 40 * 685270 * 2
def baseEnd_685270 : Nat := 234581925404426074449005

theorem tailTrace_685270 : CollatzResearch.WordTrace tailWord_685270 prefixEnd_685270 234581925404426074449005 := by
  unfold tailWord_685270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1562115639211956227718329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16662566818260866428995509 1562115639211956227718329)
  ·
    refine ⟨1171586729408967170788747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1562115639211956227718329 1171586729408967170788747)
    ·
      refine ⟨1757380094113450756183121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1171586729408967170788747 1757380094113450756183121)
      ·
        refine ⟨1318035070585088067137341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1757380094113450756183121 1318035070585088067137341)
        ·
          refine ⟨494263151469408025176503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1318035070585088067137341 494263151469408025176503)
          ·
            refine ⟨741394727204112037764755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494263151469408025176503 741394727204112037764755)
            ·
              refine ⟨1112092090806168056647133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741394727204112037764755 1112092090806168056647133)
              ·
                refine ⟨417034534052313021242675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1112092090806168056647133 417034534052313021242675)
                ·
                  refine ⟨625551801078469531864013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 417034534052313021242675 625551801078469531864013)
                  ·
                    refine ⟨234581925404426074449005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 625551801078469531864013 234581925404426074449005)
                    ·
                      rfl

theorem cell22_685270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_685270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685270 prefixEnd_685270 := by exact prefixLift 685270
  have htrace : WordTrace (prefixWord ++ tailWord_685270) baseStart_685270 baseEnd_685270 := by
    simpa [prefixWord, tailWord_685270, baseEnd_685270] using wordTrace_append hprefix tailTrace_685270
  have hstable : (prefixWord ++ tailWord_685270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685270).length < 2 ^ (prefixWord ++ tailWord_685270).sum := by decide
  have hdescent : baseEnd_685270 < baseStart_685270 := by decide
  rcases family_descends (prefixWord ++ tailWord_685270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685290 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 4, 4]
def baseStart_685290 : Nat := 118140960795 + 685290 * 2 ^ 59
def prefixEnd_685290 : Nat := 4983230072969 + 3 ^ 40 * 685290 * 2
def baseEnd_685290 : Nat := 234588771813152688948943

theorem tailTrace_685290 : CollatzResearch.WordTrace tailWord_685290 prefixEnd_685290 234588771813152688948943 := by
  unfold tailWord_685290
  simp only [CollatzResearch.WordTrace]
  refine ⟨6248644921829710764805331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16663053124879228706147549 6248644921829710764805331)
  ·
    refine ⟨9372967382744566147207997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6248644921829710764805331 9372967382744566147207997)
    ·
      refine ⟨3514862768529212305202999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9372967382744566147207997 3514862768529212305202999)
      ·
        refine ⟨5272294152793818457804499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3514862768529212305202999 5272294152793818457804499)
        ·
          refine ⟨7908441229190727686706749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5272294152793818457804499 7908441229190727686706749)
          ·
            refine ⟨2965665460946522882515031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7908441229190727686706749 2965665460946522882515031)
            ·
              refine ⟨4448498191419784323772547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2965665460946522882515031 4448498191419784323772547)
              ·
                refine ⟨6672747287129676485658821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4448498191419784323772547 6672747287129676485658821)
                ·
                  refine ⟨1251140116336814341061029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6672747287129676485658821 1251140116336814341061029)
                  ·
                    refine ⟨234588771813152688948943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1251140116336814341061029 234588771813152688948943)
                    ·
                      rfl

theorem cell22_685290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_685290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685290 prefixEnd_685290 := by exact prefixLift 685290
  have htrace : WordTrace (prefixWord ++ tailWord_685290) baseStart_685290 baseEnd_685290 := by
    simpa [prefixWord, tailWord_685290, baseEnd_685290] using wordTrace_append hprefix tailTrace_685290
  have hstable : (prefixWord ++ tailWord_685290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685290).length < 2 ^ (prefixWord ++ tailWord_685290).sum := by decide
  have hdescent : baseEnd_685290 < baseStart_685290 := by decide
  rcases family_descends (prefixWord ++ tailWord_685290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685300 : List Nat := [2, 6, 1, 2, 2, 1, 2, 1, 5]
def baseStart_685300 : Nat := 118140960795 + 685300 * 2 ^ 59
def prefixEnd_685300 : Nat := 4983230072969 + 3 ^ 40 * 685300 * 2
def baseEnd_685300 : Nat := 78197398339171998732971

theorem tailTrace_685300 : CollatzResearch.WordTrace tailWord_685300 prefixEnd_685300 78197398339171998732971 := by
  unfold tailWord_685300
  simp only [CollatzResearch.WordTrace]
  refine ⟨12497472208641307383542677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16663296278188409844723569 12497472208641307383542677)
  ·
    refine ⟨585819009780061283603563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12497472208641307383542677 585819009780061283603563)
    ·
      refine ⟨878728514670091925405345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 585819009780061283603563 878728514670091925405345)
      ·
        refine ⟨659046386002568944054009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 878728514670091925405345 659046386002568944054009)
        ·
          refine ⟨494284789501926708040507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 659046386002568944054009 494284789501926708040507)
          ·
            refine ⟨741427184252890062060761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494284789501926708040507 741427184252890062060761)
            ·
              refine ⟨556070388189667546545571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 741427184252890062060761 556070388189667546545571)
              ·
                refine ⟨834105582284501319818357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 556070388189667546545571 834105582284501319818357)
                ·
                  refine ⟨78197398339171998732971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 834105582284501319818357 78197398339171998732971)
                  ·
                    rfl

theorem cell22_685300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_685300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685300 prefixEnd_685300 := by exact prefixLift 685300
  have htrace : WordTrace (prefixWord ++ tailWord_685300) baseStart_685300 baseEnd_685300 := by
    simpa [prefixWord, tailWord_685300, baseEnd_685300] using wordTrace_append hprefix tailTrace_685300
  have hstable : (prefixWord ++ tailWord_685300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685300).length < 2 ^ (prefixWord ++ tailWord_685300).sum := by decide
  have hdescent : baseEnd_685300 < baseStart_685300 := by decide
  rcases family_descends (prefixWord ++ tailWord_685300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685365 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 1, 7]
def baseStart_685365 : Nat := 118140960795 + 685365 * 2 ^ 59
def prefixEnd_685365 : Nat := 4983230072969 + 3 ^ 40 * 685365 * 2
def baseEnd_685365 : Nat := 234614445845877493323713

theorem tailTrace_685365 : CollatzResearch.WordTrace tailWord_685365 prefixEnd_685365 234614445845877493323713 := by
  unfold tailWord_685365
  simp only [CollatzResearch.WordTrace]
  refine ⟨24997315162047130868201549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16664876774698087245467699 24997315162047130868201549)
  ·
    refine ⟨9373993185767674075575581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24997315162047130868201549 9373993185767674075575581)
    ·
      refine ⟨3515247444662877778340843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9373993185767674075575581 3515247444662877778340843)
      ·
        refine ⟨5272871166994316667511265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3515247444662877778340843 5272871166994316667511265)
        ·
          refine ⟨3954653375245737500633449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5272871166994316667511265 3954653375245737500633449)
          ·
            refine ⟨2965990031434303125475087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3954653375245737500633449 2965990031434303125475087)
            ·
              refine ⟨4448985047151454688212631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2965990031434303125475087 4448985047151454688212631)
              ·
                refine ⟨6673477570727182032318947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4448985047151454688212631 6673477570727182032318947)
                ·
                  refine ⟨10010216356090773048478421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6673477570727182032318947 10010216356090773048478421)
                  ·
                    refine ⟨234614445845877493323713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10010216356090773048478421 234614445845877493323713)
                    ·
                      rfl

theorem cell22_685365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_685365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685365 prefixEnd_685365 := by exact prefixLift 685365
  have htrace : WordTrace (prefixWord ++ tailWord_685365) baseStart_685365 baseEnd_685365 := by
    simpa [prefixWord, tailWord_685365, baseEnd_685365] using wordTrace_append hprefix tailTrace_685365
  have hstable : (prefixWord ++ tailWord_685365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685365).length < 2 ^ (prefixWord ++ tailWord_685365).sum := by decide
  have hdescent : baseEnd_685365 < baseStart_685365 := by decide
  rcases family_descends (prefixWord ++ tailWord_685365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685412 : List Nat := [2, 3, 1, 1, 3, 3, 2, 1, 6]
def baseStart_685412 : Nat := 118140960795 + 685412 * 2 ^ 59
def prefixEnd_685412 : Nat := 4983230072969 + 3 ^ 40 * 685412 * 2
def baseEnd_685412 : Nat := 78210178302128345799523

theorem tailTrace_685412 : CollatzResearch.WordTrace tailWord_685412 prefixEnd_685412 78210178302128345799523 := by
  unfold tailWord_685412
  simp only [CollatzResearch.WordTrace]
  refine ⟨12499514696438428947581245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16666019595251238596774993 12499514696438428947581245)
  ·
    refine ⟨4687318011164410855342967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12499514696438428947581245 4687318011164410855342967)
    ·
      refine ⟨7030977016746616283014451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4687318011164410855342967 7030977016746616283014451)
      ·
        refine ⟨10546465525119924424521677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7030977016746616283014451 10546465525119924424521677)
        ·
          refine ⟨3954924571919971659195629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10546465525119924424521677 3954924571919971659195629)
          ·
            refine ⟨1483096714469989372198361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3954924571919971659195629 1483096714469989372198361)
            ·
              refine ⟨1112322535852492029148771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1483096714469989372198361 1112322535852492029148771)
              ·
                refine ⟨1668483803778738043723157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112322535852492029148771 1668483803778738043723157)
                ·
                  refine ⟨78210178302128345799523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1668483803778738043723157 78210178302128345799523)
                  ·
                    rfl

theorem cell22_685412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_685412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685412 prefixEnd_685412 := by exact prefixLift 685412
  have htrace : WordTrace (prefixWord ++ tailWord_685412) baseStart_685412 baseEnd_685412 := by
    simpa [prefixWord, tailWord_685412, baseEnd_685412] using wordTrace_append hprefix tailTrace_685412
  have hstable : (prefixWord ++ tailWord_685412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685412).length < 2 ^ (prefixWord ++ tailWord_685412).sum := by decide
  have hdescent : baseEnd_685412 < baseStart_685412 := by decide
  rcases family_descends (prefixWord ++ tailWord_685412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685425 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 1, 6]
def baseStart_685425 : Nat := 118140960795 + 685425 * 2 ^ 59
def prefixEnd_685425 : Nat := 4983230072969 + 3 ^ 40 * 685425 * 2
def baseEnd_685425 : Nat := 234634985072057336823529

theorem tailTrace_685425 : CollatzResearch.WordTrace tailWord_685425 prefixEnd_685425 234634985072057336823529 := by
  unfold tailWord_685425
  simp only [CollatzResearch.WordTrace]
  refine ⟨24999503541829761115385729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16666335694553174076923819 24999503541829761115385729)
  ·
    refine ⟨18749627656372320836539297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24999503541829761115385729 18749627656372320836539297)
    ·
      refine ⟨14062220742279240627404473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18749627656372320836539297 14062220742279240627404473)
      ·
        refine ⟨10546665556709430470553355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14062220742279240627404473 10546665556709430470553355)
        ·
          refine ⟨15819998335064145705830033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10546665556709430470553355 15819998335064145705830033)
          ·
            refine ⟨11864998751298109279372525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15819998335064145705830033 11864998751298109279372525)
            ·
              refine ⟨4449374531736790979764697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11864998751298109279372525 4449374531736790979764697)
              ·
                refine ⟨3337030898802593234823523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4449374531736790979764697 3337030898802593234823523)
                ·
                  refine ⟨5005546348203889852235285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3337030898802593234823523 5005546348203889852235285)
                  ·
                    refine ⟨234634985072057336823529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5005546348203889852235285 234634985072057336823529)
                    ·
                      rfl

theorem cell22_685425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_685425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685425 prefixEnd_685425 := by exact prefixLift 685425
  have htrace : WordTrace (prefixWord ++ tailWord_685425) baseStart_685425 baseEnd_685425 := by
    simpa [prefixWord, tailWord_685425, baseEnd_685425] using wordTrace_append hprefix tailTrace_685425
  have hstable : (prefixWord ++ tailWord_685425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685425).length < 2 ^ (prefixWord ++ tailWord_685425).sum := by decide
  have hdescent : baseEnd_685425 < baseStart_685425 := by decide
  rcases family_descends (prefixWord ++ tailWord_685425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685562 : List Nat := [3, 1, 1, 1, 1, 2, 3, 4, 1, 5]
def baseStart_685562 : Nat := 118140960795 + 685562 * 2 ^ 59
def prefixEnd_685562 : Nat := 4983230072969 + 3 ^ 40 * 685562 * 2
def baseEnd_685562 : Nat := 234681882971834646148109

theorem tailTrace_685562 : CollatzResearch.WordTrace tailWord_685562 prefixEnd_685562 234681882971834646148109 := by
  unfold tailWord_685562
  simp only [CollatzResearch.WordTrace]
  refine ⟨6251125085583358378280735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16669666894888955675415293 6251125085583358378280735)
  ·
    refine ⟨9376687628375037567421103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6251125085583358378280735 9376687628375037567421103)
    ·
      refine ⟨14065031442562556351131655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9376687628375037567421103 14065031442562556351131655)
      ·
        refine ⟨21097547163843834526697483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14065031442562556351131655 21097547163843834526697483)
        ·
          refine ⟨31646320745765751790046225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21097547163843834526697483 31646320745765751790046225)
          ·
            refine ⟨23734740559324313842534669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31646320745765751790046225 23734740559324313842534669)
            ·
              refine ⟨8900527709746617690950501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23734740559324313842534669 8900527709746617690950501)
              ·
                refine ⟨1668848945577490817053219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8900527709746617690950501 1668848945577490817053219)
                ·
                  refine ⟨2503273418366236225579829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1668848945577490817053219 2503273418366236225579829)
                  ·
                    refine ⟨234681882971834646148109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2503273418366236225579829 234681882971834646148109)
                    ·
                      rfl

theorem cell22_685562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_685562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685562 prefixEnd_685562 := by exact prefixLift 685562
  have htrace : WordTrace (prefixWord ++ tailWord_685562) baseStart_685562 baseEnd_685562 := by
    simpa [prefixWord, tailWord_685562, baseEnd_685562] using wordTrace_append hprefix tailTrace_685562
  have hstable : (prefixWord ++ tailWord_685562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685562).length < 2 ^ (prefixWord ++ tailWord_685562).sum := by decide
  have hdescent : baseEnd_685562 < baseStart_685562 := by decide
  rcases family_descends (prefixWord ++ tailWord_685562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685564 : List Nat := [2, 2, 2, 1, 2, 1, 3, 5, 4]
def baseStart_685564 : Nat := 118140960795 + 685564 * 2 ^ 59
def prefixEnd_685564 : Nat := 4983230072969 + 3 ^ 40 * 685564 * 2
def baseEnd_685564 : Nat := 78227522537569102532701

theorem tailTrace_685564 : CollatzResearch.WordTrace tailWord_685564 prefixEnd_685564 78227522537569102532701 := by
  unfold tailWord_685564
  simp only [CollatzResearch.WordTrace]
  refine ⟨12502286644163093927347873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16669715525550791903130497 12502286644163093927347873)
  ·
    refine ⟨9376714983122320445510905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12502286644163093927347873 9376714983122320445510905)
    ·
      refine ⟨7032536237341740334133179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9376714983122320445510905 7032536237341740334133179)
      ·
        refine ⟨10548804356012610501199769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7032536237341740334133179 10548804356012610501199769)
        ·
          refine ⟨7911603267009457875899827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10548804356012610501199769 7911603267009457875899827)
          ·
            refine ⟨11867404900514186813849741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7911603267009457875899827 11867404900514186813849741)
            ·
              refine ⟨4450276837692820055193653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11867404900514186813849741 4450276837692820055193653)
              ·
                refine ⟨417213453533701880174405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4450276837692820055193653 417213453533701880174405)
                ·
                  refine ⟨78227522537569102532701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 417213453533701880174405 78227522537569102532701)
                  ·
                    rfl

theorem cell22_685564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 4].length) (baseStart_685564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685564 prefixEnd_685564 := by exact prefixLift 685564
  have htrace : WordTrace (prefixWord ++ tailWord_685564) baseStart_685564 baseEnd_685564 := by
    simpa [prefixWord, tailWord_685564, baseEnd_685564] using wordTrace_append hprefix tailTrace_685564
  have hstable : (prefixWord ++ tailWord_685564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685564).length < 2 ^ (prefixWord ++ tailWord_685564).sum := by decide
  have hdescent : baseEnd_685564 < baseStart_685564 := by decide
  rcases family_descends (prefixWord ++ tailWord_685564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685577 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 4, 4]
def baseStart_685577 : Nat := 118140960795 + 685577 * 2 ^ 59
def prefixEnd_685577 : Nat := 4983230072969 + 3 ^ 40 * 685577 * 2
def baseEnd_685577 : Nat := 234687017778379607023063

theorem tailTrace_685577 : CollatzResearch.WordTrace tailWord_685577 prefixEnd_685577 234687017778379607023063 := by
  unfold tailWord_685577
  simp only [CollatzResearch.WordTrace]
  refine ⟨25005047437279091074918985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16670031624852727383279323 25005047437279091074918985)
  ·
    refine ⟨18753785577959318306189239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25005047437279091074918985 18753785577959318306189239)
    ·
      refine ⟨28130678366938977459283859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18753785577959318306189239 28130678366938977459283859)
      ·
        refine ⟨42196017550408466188925789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28130678366938977459283859 42196017550408466188925789)
        ·
          refine ⟨15823506581403174820847171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42196017550408466188925789 15823506581403174820847171)
          ·
            refine ⟨23735259872104762231270757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15823506581403174820847171 23735259872104762231270757)
            ·
              refine ⟨4450361226019642918363267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23735259872104762231270757 4450361226019642918363267)
              ·
                refine ⟨6675541839029464377544901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4450361226019642918363267 6675541839029464377544901)
                ·
                  refine ⟨1251664094818024570789669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6675541839029464377544901 1251664094818024570789669)
                  ·
                    refine ⟨234687017778379607023063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1251664094818024570789669 234687017778379607023063)
                    ·
                      rfl

theorem cell22_685577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 4].length) (baseStart_685577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685577 prefixEnd_685577 := by exact prefixLift 685577
  have htrace : WordTrace (prefixWord ++ tailWord_685577) baseStart_685577 baseEnd_685577 := by
    simpa [prefixWord, tailWord_685577, baseEnd_685577] using wordTrace_append hprefix tailTrace_685577
  have hstable : (prefixWord ++ tailWord_685577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685577).length < 2 ^ (prefixWord ++ tailWord_685577).sum := by decide
  have hdescent : baseEnd_685577 < baseStart_685577 := by decide
  rcases family_descends (prefixWord ++ tailWord_685577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685637 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 7]
def baseStart_685637 : Nat := 118140960795 + 685637 * 2 ^ 59
def prefixEnd_685637 : Nat := 4983230072969 + 3 ^ 40 * 685637 * 2
def baseEnd_685637 : Nat := 78235852334853150174293

theorem tailTrace_685637 : CollatzResearch.WordTrace tailWord_685637 prefixEnd_685637 78235852334853150174293 := by
  unfold tailWord_685637
  simp only [CollatzResearch.WordTrace]
  refine ⟨25007235817061721322103165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16671490544707814214735443 25007235817061721322103165)
  ·
    refine ⟨9377713431398145495788687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25007235817061721322103165 9377713431398145495788687)
    ·
      refine ⟨14066570147097218243683031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9377713431398145495788687 14066570147097218243683031)
      ·
        refine ⟨21099855220645827365524547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14066570147097218243683031 21099855220645827365524547)
        ·
          refine ⟨31649782830968741048286821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21099855220645827365524547 31649782830968741048286821)
          ·
            refine ⟨5934334280806638946553779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31649782830968741048286821 5934334280806638946553779)
            ·
              refine ⟨8901501421209958419830669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5934334280806638946553779 8901501421209958419830669)
              ·
                refine ⟨3338063032953734407436501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8901501421209958419830669 3338063032953734407436501)
                ·
                  refine ⟨78235852334853150174293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3338063032953734407436501 78235852334853150174293)
                  ·
                    rfl

theorem cell22_685637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_685637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685637 prefixEnd_685637 := by exact prefixLift 685637
  have htrace : WordTrace (prefixWord ++ tailWord_685637) baseStart_685637 baseEnd_685637 := by
    simpa [prefixWord, tailWord_685637, baseEnd_685637] using wordTrace_append hprefix tailTrace_685637
  have hstable : (prefixWord ++ tailWord_685637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685637).length < 2 ^ (prefixWord ++ tailWord_685637).sum := by decide
  have hdescent : baseEnd_685637 < baseStart_685637 := by decide
  rcases family_descends (prefixWord ++ tailWord_685637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685641 : List Nat := [1, 2, 1, 1, 2, 2, 1, 8, 1, 3]
def baseStart_685641 : Nat := 118140960795 + 685641 * 2 ^ 59
def prefixEnd_685641 : Nat := 4983230072969 + 3 ^ 40 * 685641 * 2
def baseEnd_685641 : Nat := 234708926286304773422867

theorem tailTrace_685641 : CollatzResearch.WordTrace tailWord_685641 prefixEnd_685641 234708926286304773422867 := by
  unfold tailWord_685641
  simp only [CollatzResearch.WordTrace]
  refine ⟨25007381709047230005248777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16671587806031486670165851 25007381709047230005248777)
  ·
    refine ⟨18755536281785422503936583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25007381709047230005248777 18755536281785422503936583)
    ·
      refine ⟨28133304422678133755904875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18755536281785422503936583 28133304422678133755904875)
      ·
        refine ⟨42199956634017200633857313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28133304422678133755904875 42199956634017200633857313)
        ·
          refine ⟨31649967475512900475392985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42199956634017200633857313 31649967475512900475392985)
          ·
            refine ⟨23737475606634675356544739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31649967475512900475392985 23737475606634675356544739)
            ·
              refine ⟨35606213409952013034817109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23737475606634675356544739 35606213409952013034817109)
              ·
                refine ⟨417260313397875152751763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 35606213409952013034817109 417260313397875152751763)
                ·
                  refine ⟨625890470096812729127645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 417260313397875152751763 625890470096812729127645)
                  ·
                    refine ⟨234708926286304773422867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 625890470096812729127645 234708926286304773422867)
                    ·
                      rfl

theorem cell22_685641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 1, 3].length) (baseStart_685641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685641 prefixEnd_685641 := by exact prefixLift 685641
  have htrace : WordTrace (prefixWord ++ tailWord_685641) baseStart_685641 baseEnd_685641 := by
    simpa [prefixWord, tailWord_685641, baseEnd_685641] using wordTrace_append hprefix tailTrace_685641
  have hstable : (prefixWord ++ tailWord_685641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685641).length < 2 ^ (prefixWord ++ tailWord_685641).sum := by decide
  have hdescent : baseEnd_685641 < baseStart_685641 := by decide
  rcases family_descends (prefixWord ++ tailWord_685641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685750 : List Nat := [5, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_685750 : Nat := 118140960795 + 685750 * 2 ^ 59
def prefixEnd_685750 : Nat := 4983230072969 + 3 ^ 40 * 685750 * 2
def baseEnd_685750 : Nat := 78248746404621607482511

theorem tailTrace_685750 : CollatzResearch.WordTrace tailWord_685750 prefixEnd_685750 78248746404621607482511 := by
  unfold tailWord_685750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1563209829103271351310419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16674238177101561080644469 1563209829103271351310419)
  ·
    refine ⟨2344814743654907026965629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1563209829103271351310419 2344814743654907026965629)
    ·
      refine ⟨879305528870590135112111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2344814743654907026965629 879305528870590135112111)
      ·
        refine ⟨1318958293305885202668167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 879305528870590135112111 1318958293305885202668167)
        ·
          refine ⟨1978437439958827804002251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1318958293305885202668167 1978437439958827804002251)
          ·
            refine ⟨2967656159938241706003377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1978437439958827804002251 2967656159938241706003377)
            ·
              refine ⟨2225742119953681279502533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2967656159938241706003377 2225742119953681279502533)
              ·
                refine ⟨417326647491315239906725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2225742119953681279502533 417326647491315239906725)
                ·
                  refine ⟨78248746404621607482511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 417326647491315239906725 78248746404621607482511)
                  ·
                    rfl

theorem cell22_685750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_685750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685750 prefixEnd_685750 := by exact prefixLift 685750
  have htrace : WordTrace (prefixWord ++ tailWord_685750) baseStart_685750 baseEnd_685750 := by
    simpa [prefixWord, tailWord_685750, baseEnd_685750] using wordTrace_append hprefix tailTrace_685750
  have hstable : (prefixWord ++ tailWord_685750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685750).length < 2 ^ (prefixWord ++ tailWord_685750).sum := by decide
  have hdescent : baseEnd_685750 < baseStart_685750 := by decide
  rcases family_descends (prefixWord ++ tailWord_685750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685778 : List Nat := [3, 2, 2, 2, 2, 3, 2, 6]
def baseStart_685778 : Nat := 118140960795 + 685778 * 2 ^ 59
def prefixEnd_685778 : Nat := 4983230072969 + 3 ^ 40 * 685778 * 2
def baseEnd_685778 : Nat := 26083980465120231416383

theorem tailTrace_685778 : CollatzResearch.WordTrace tailWord_685778 prefixEnd_685778 26083980465120231416383 := by
  unfold tailWord_685778
  simp only [CollatzResearch.WordTrace]
  refine ⟨6253094627387725600746497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16674919006367268268657325 6253094627387725600746497)
  ·
    refine ⟨4689820970540794200559873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6253094627387725600746497 4689820970540794200559873)
    ·
      refine ⟨3517365727905595650419905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4689820970540794200559873 3517365727905595650419905)
      ·
        refine ⟨2638024295929196737814929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3517365727905595650419905 2638024295929196737814929)
        ·
          refine ⟨1978518221946897553361197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2638024295929196737814929 1978518221946897553361197)
          ·
            refine ⟨741944333230086582510449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1978518221946897553361197 741944333230086582510449)
            ·
              refine ⟨556458249922564936882837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 741944333230086582510449 556458249922564936882837)
              ·
                refine ⟨26083980465120231416383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 556458249922564936882837 26083980465120231416383)
                ·
                  rfl

theorem cell22_685778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 6].length) (baseStart_685778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685778 prefixEnd_685778 := by exact prefixLift 685778
  have htrace : WordTrace (prefixWord ++ tailWord_685778) baseStart_685778 baseEnd_685778 := by
    simpa [prefixWord, tailWord_685778, baseEnd_685778] using wordTrace_append hprefix tailTrace_685778
  have hstable : (prefixWord ++ tailWord_685778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685778).length < 2 ^ (prefixWord ++ tailWord_685778).sum := by decide
  have hdescent : baseEnd_685778 < baseStart_685778 := by decide
  rcases family_descends (prefixWord ++ tailWord_685778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685804 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 4, 5]
def baseStart_685804 : Nat := 118140960795 + 685804 * 2 ^ 59
def prefixEnd_685804 : Nat := 4983230072969 + 3 ^ 40 * 685804 * 2
def baseEnd_685804 : Nat := 234764724517426681597367

theorem tailTrace_685804 : CollatzResearch.WordTrace tailWord_685804 prefixEnd_685804 234764724517426681597367 := by
  unfold tailWord_685804
  simp only [CollatzResearch.WordTrace]
  refine ⟨12506663403728354421716233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16675551204971139228954977 12506663403728354421716233)
  ·
    refine ⟨9379997552796265816287175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12506663403728354421716233 9379997552796265816287175)
    ·
      refine ⟨14069996329194398724430763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9379997552796265816287175 14069996329194398724430763)
      ·
        refine ⟨21104994493791598086646145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14069996329194398724430763 21104994493791598086646145)
        ·
          refine ⟨15828745870343698564984609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21104994493791598086646145 15828745870343698564984609)
          ·
            refine ⟨11871559402757773923738457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15828745870343698564984609 11871559402757773923738457)
            ·
              refine ⟨8903669552068330442803843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11871559402757773923738457 8903669552068330442803843)
              ·
                refine ⟨13355504328102495664205765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8903669552068330442803843 13355504328102495664205765)
                ·
                  refine ⟨2504157061519217937038581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13355504328102495664205765 2504157061519217937038581)
                  ·
                    refine ⟨234764724517426681597367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2504157061519217937038581 234764724517426681597367)
                    ·
                      rfl

theorem cell22_685804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_685804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685804 prefixEnd_685804 := by exact prefixLift 685804
  have htrace : WordTrace (prefixWord ++ tailWord_685804) baseStart_685804 baseEnd_685804 := by
    simpa [prefixWord, tailWord_685804, baseEnd_685804] using wordTrace_append hprefix tailTrace_685804
  have hstable : (prefixWord ++ tailWord_685804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685804).length < 2 ^ (prefixWord ++ tailWord_685804).sum := by decide
  have hdescent : baseEnd_685804 < baseStart_685804 := by decide
  rcases family_descends (prefixWord ++ tailWord_685804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685806 : List Nat := [4, 1, 2, 1, 1, 2, 2, 4, 5]
def baseStart_685806 : Nat := 118140960795 + 685806 * 2 ^ 59
def prefixEnd_685806 : Nat := 4983230072969 + 3 ^ 40 * 685806 * 2
def baseEnd_685806 : Nat := 78255136386099781015787

theorem tailTrace_685806 : CollatzResearch.WordTrace tailWord_685806 prefixEnd_685806 78255136386099781015787 := by
  unfold tailWord_685806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3126674969181182898125659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16675599835632975456670181 3126674969181182898125659)
  ·
    refine ⟨4690012453771774347188489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3126674969181182898125659 4690012453771774347188489)
    ·
      refine ⟨3517509340328830760391367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4690012453771774347188489 3517509340328830760391367)
      ·
        refine ⟨5276264010493246140587051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3517509340328830760391367 5276264010493246140587051)
        ·
          refine ⟨7914396015739869210880577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5276264010493246140587051 7914396015739869210880577)
          ·
            refine ⟨5935797011804901908160433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7914396015739869210880577 5935797011804901908160433)
            ·
              refine ⟨4451847758853676431120325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5935797011804901908160433 4451847758853676431120325)
              ·
                refine ⟨834721454785064330835061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4451847758853676431120325 834721454785064330835061)
                ·
                  refine ⟨78255136386099781015787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 834721454785064330835061 78255136386099781015787)
                  ·
                    rfl

theorem cell22_685806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_685806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685806 prefixEnd_685806 := by exact prefixLift 685806
  have htrace : WordTrace (prefixWord ++ tailWord_685806) baseStart_685806 baseEnd_685806 := by
    simpa [prefixWord, tailWord_685806, baseEnd_685806] using wordTrace_append hprefix tailTrace_685806
  have hstable : (prefixWord ++ tailWord_685806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685806).length < 2 ^ (prefixWord ++ tailWord_685806).sum := by decide
  have hdescent : baseEnd_685806 < baseStart_685806 := by decide
  rcases family_descends (prefixWord ++ tailWord_685806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685868 : List Nat := [2, 2, 1, 1, 1, 6, 1, 4, 4]
def baseStart_685868 : Nat := 118140960795 + 685868 * 2 ^ 59
def prefixEnd_685868 : Nat := 4983230072969 + 3 ^ 40 * 685868 * 2
def baseEnd_685868 : Nat := 78262211008450615999057

theorem tailTrace_685868 : CollatzResearch.WordTrace tailWord_685868 prefixEnd_685868 78262211008450615999057 := by
  unfold tailWord_685868
  simp only [CollatzResearch.WordTrace]
  refine ⟨12507830539612423886881129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16677107386149898515841505 12507830539612423886881129)
  ·
    refine ⟨9380872904709317915160847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12507830539612423886881129 9380872904709317915160847)
    ·
      refine ⟨14071309357063976872741271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9380872904709317915160847 14071309357063976872741271)
      ·
        refine ⟨21106964035595965309111907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14071309357063976872741271 21106964035595965309111907)
        ·
          refine ⟨31660446053393947963667861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21106964035595965309111907 31660446053393947963667861)
          ·
            refine ⟨1484083408752841310796931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31660446053393947963667861 1484083408752841310796931)
            ·
              refine ⟨2226125113129261966195397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1484083408752841310796931 2226125113129261966195397)
              ·
                refine ⟨417398458711736618661637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2226125113129261966195397 417398458711736618661637)
                ·
                  refine ⟨78262211008450615999057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 417398458711736618661637 78262211008450615999057)
                  ·
                    rfl

theorem cell22_685868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 4].length) (baseStart_685868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685868 prefixEnd_685868 := by exact prefixLift 685868
  have htrace : WordTrace (prefixWord ++ tailWord_685868) baseStart_685868 baseEnd_685868 := by
    simpa [prefixWord, tailWord_685868, baseEnd_685868] using wordTrace_append hprefix tailTrace_685868
  have hstable : (prefixWord ++ tailWord_685868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685868).length < 2 ^ (prefixWord ++ tailWord_685868).sum := by decide
  have hdescent : baseEnd_685868 < baseStart_685868 := by decide
  rcases family_descends (prefixWord ++ tailWord_685868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685879 : List Nat := [1, 1, 3, 1, 2, 1, 2, 11]
def baseStart_685879 : Nat := 118140960795 + 685879 * 2 ^ 59
def prefixEnd_685879 : Nat := 4983230072969 + 3 ^ 40 * 685879 * 2
def baseEnd_685879 : Nat := 26087822061127942885793

theorem tailTrace_685879 : CollatzResearch.WordTrace tailWord_685879 prefixEnd_685879 26087822061127942885793 := by
  unfold tailWord_685879
  simp only [CollatzResearch.WordTrace]
  refine ⟨25016062282184996652412691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16677374854789997768275127 25016062282184996652412691)
  ·
    refine ⟨37524093423277494978619037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25016062282184996652412691 37524093423277494978619037)
    ·
      refine ⟨14071535033729060616982139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37524093423277494978619037 14071535033729060616982139)
      ·
        refine ⟨21107302550593590925473209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14071535033729060616982139 21107302550593590925473209)
        ·
          refine ⟨15830476912945193194104907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21107302550593590925473209 15830476912945193194104907)
          ·
            refine ⟨23745715369417789791157361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15830476912945193194104907 23745715369417789791157361)
            ·
              refine ⟨17809286527063342343368021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23745715369417789791157361 17809286527063342343368021)
              ·
                refine ⟨26087822061127942885793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 17809286527063342343368021 26087822061127942885793)
                ·
                  rfl

theorem cell22_685879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 11].length) (baseStart_685879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685879 prefixEnd_685879 := by exact prefixLift 685879
  have htrace : WordTrace (prefixWord ++ tailWord_685879) baseStart_685879 baseEnd_685879 := by
    simpa [prefixWord, tailWord_685879, baseEnd_685879] using wordTrace_append hprefix tailTrace_685879
  have hstable : (prefixWord ++ tailWord_685879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685879).length < 2 ^ (prefixWord ++ tailWord_685879).sum := by decide
  have hdescent : baseEnd_685879 < baseStart_685879 := by decide
  rcases family_descends (prefixWord ++ tailWord_685879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685956 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_685956 : Nat := 118140960795 + 685956 * 2 ^ 59
def prefixEnd_685956 : Nat := 4983230072969 + 3 ^ 40 * 685956 * 2
def baseEnd_685956 : Nat := 234816757223748951796901

theorem tailTrace_685956 : CollatzResearch.WordTrace tailWord_685956 prefixEnd_685956 234816757223748951796901 := by
  unfold tailWord_685956
  simp only [CollatzResearch.WordTrace]
  refine ⟨12509435351453019401482861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16679247135270692535310481 12509435351453019401482861)
  ·
    refine ⟨4691038256794882275556073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12509435351453019401482861 4691038256794882275556073)
    ·
      refine ⟨3518278692596161706667055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4691038256794882275556073 3518278692596161706667055)
      ·
        refine ⟨5277418038894242560000583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3518278692596161706667055 5277418038894242560000583)
        ·
          refine ⟨7916127058341363840000875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5277418038894242560000583 7916127058341363840000875)
          ·
            refine ⟨11874190587512045760001313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7916127058341363840000875 11874190587512045760001313)
            ·
              refine ⟨8905642940634034320000985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11874190587512045760001313 8905642940634034320000985)
              ·
                refine ⟨6679232205475525740000739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8905642940634034320000985 6679232205475525740000739)
                ·
                  refine ⟨10018848308213288610001109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6679232205475525740000739 10018848308213288610001109)
                  ·
                    refine ⟨234816757223748951796901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10018848308213288610001109 234816757223748951796901)
                    ·
                      rfl

theorem cell22_685956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_685956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685956 prefixEnd_685956 := by exact prefixLift 685956
  have htrace : WordTrace (prefixWord ++ tailWord_685956) baseStart_685956 baseEnd_685956 := by
    simpa [prefixWord, tailWord_685956, baseEnd_685956] using wordTrace_append hprefix tailTrace_685956
  have hstable : (prefixWord ++ tailWord_685956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685956).length < 2 ^ (prefixWord ++ tailWord_685956).sum := by decide
  have hdescent : baseEnd_685956 < baseStart_685956 := by decide
  rcases family_descends (prefixWord ++ tailWord_685956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685992 : List Nat := [2, 1, 6, 2, 1, 1, 1, 3, 5]
def baseStart_685992 : Nat := 118140960795 + 685992 * 2 ^ 59
def prefixEnd_685992 : Nat := 4983230072969 + 3 ^ 40 * 685992 * 2
def baseEnd_685992 : Nat := 78276360253152285965597

theorem tailTrace_685992 : CollatzResearch.WordTrace tailWord_685992 prefixEnd_685992 78276360253152285965597 := by
  unfold tailWord_685992
  simp only [CollatzResearch.WordTrace]
  refine ⟨12510091865387808475638115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16680122487183744634184153 12510091865387808475638115)
  ·
    refine ⟨18765137798081712713457173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12510091865387808475638115 18765137798081712713457173)
    ·
      refine ⟨879615834285080283443305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18765137798081712713457173 879615834285080283443305)
      ·
        refine ⟨659711875713810212582479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 879615834285080283443305 659711875713810212582479)
        ·
          refine ⟨989567813570715318873719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 659711875713810212582479 989567813570715318873719)
          ·
            refine ⟨1484351720356072978310579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989567813570715318873719 1484351720356072978310579)
            ·
              refine ⟨2226527580534109467465869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1484351720356072978310579 2226527580534109467465869)
              ·
                refine ⟨834947842700291050299701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2226527580534109467465869 834947842700291050299701)
                ·
                  refine ⟨78276360253152285965597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 834947842700291050299701 78276360253152285965597)
                  ·
                    rfl

theorem cell22_685992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 5].length) (baseStart_685992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_685992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_685992 prefixEnd_685992 := by exact prefixLift 685992
  have htrace : WordTrace (prefixWord ++ tailWord_685992) baseStart_685992 baseEnd_685992 := by
    simpa [prefixWord, tailWord_685992, baseEnd_685992] using wordTrace_append hprefix tailTrace_685992
  have hstable : (prefixWord ++ tailWord_685992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685992).length < 2 ^ (prefixWord ++ tailWord_685992).sum := by decide
  have hdescent : baseEnd_685992 < baseStart_685992 := by decide
  rcases family_descends (prefixWord ++ tailWord_685992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686005 : List Nat := [1, 3, 3, 2, 1, 2, 3, 2, 1, 4]
def baseStart_686005 : Nat := 118140960795 + 686005 * 2 ^ 59
def prefixEnd_686005 : Nat := 4983230072969 + 3 ^ 40 * 686005 * 2
def baseEnd_686005 : Nat := 234833530925129157321751

theorem tailTrace_686005 : CollatzResearch.WordTrace tailWord_686005 prefixEnd_686005 234833530925129157321751 := by
  unfold tailWord_686005
  simp only [CollatzResearch.WordTrace]
  refine ⟨25020657879728520171499469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16680438586485680114332979 25020657879728520171499469)
  ·
    refine ⟨9382746704898195064312301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25020657879728520171499469 9382746704898195064312301)
    ·
      refine ⟨3518530014336823149117113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9382746704898195064312301 3518530014336823149117113)
      ·
        refine ⟨2638897510752617361837835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3518530014336823149117113 2638897510752617361837835)
        ·
          refine ⟨3958346266128926042756753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2638897510752617361837835 3958346266128926042756753)
          ·
            refine ⟨2968759699596694532067565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3958346266128926042756753 2968759699596694532067565)
            ·
              refine ⟨1113284887348760449525337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2968759699596694532067565 1113284887348760449525337)
              ·
                refine ⟨834963665511570337144003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1113284887348760449525337 834963665511570337144003)
                ·
                  refine ⟨1252445498267355505716005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 834963665511570337144003 1252445498267355505716005)
                  ·
                    refine ⟨234833530925129157321751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1252445498267355505716005 234833530925129157321751)
                    ·
                      rfl

theorem cell22_686005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_686005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686005 prefixEnd_686005 := by exact prefixLift 686005
  have htrace : WordTrace (prefixWord ++ tailWord_686005) baseStart_686005 baseEnd_686005 := by
    simpa [prefixWord, tailWord_686005, baseEnd_686005] using wordTrace_append hprefix tailTrace_686005
  have hstable : (prefixWord ++ tailWord_686005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686005).length < 2 ^ (prefixWord ++ tailWord_686005).sum := by decide
  have hdescent : baseEnd_686005 < baseStart_686005 := by decide
  rcases family_descends (prefixWord ++ tailWord_686005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686037 : List Nat := [1, 3, 2, 3, 2, 1, 4, 2, 4]
def baseStart_686037 : Nat := 118140960795 + 686037 * 2 ^ 59
def prefixEnd_686037 : Nat := 4983230072969 + 3 ^ 40 * 686037 * 2
def baseEnd_686037 : Nat := 78281495059697246840551

theorem tailTrace_686037 : CollatzResearch.WordTrace tailWord_686037 prefixEnd_686037 78281495059697246840551 := by
  unfold tailWord_686037
  simp only [CollatzResearch.WordTrace]
  refine ⟨25021825015612589636664365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16681216677075059757776243 25021825015612589636664365)
  ·
    refine ⟨9383184380854721113749137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25021825015612589636664365 9383184380854721113749137)
    ·
      refine ⟨7037388285641040835311853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9383184380854721113749137 7037388285641040835311853)
      ·
        refine ⟨2639020607115390313241945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7037388285641040835311853 2639020607115390313241945)
        ·
          refine ⟨1979265455336542734931459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2639020607115390313241945 1979265455336542734931459)
          ·
            refine ⟨2968898183004814102397189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1979265455336542734931459 2968898183004814102397189)
            ·
              refine ⟨556668409313402644199473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2968898183004814102397189 556668409313402644199473)
              ·
                refine ⟨417501306985051983149605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 556668409313402644199473 417501306985051983149605)
                ·
                  refine ⟨78281495059697246840551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 417501306985051983149605 78281495059697246840551)
                  ·
                    rfl

theorem cell22_686037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 4].length) (baseStart_686037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686037 prefixEnd_686037 := by exact prefixLift 686037
  have htrace : WordTrace (prefixWord ++ tailWord_686037) baseStart_686037 baseEnd_686037 := by
    simpa [prefixWord, tailWord_686037, baseEnd_686037] using wordTrace_append hprefix tailTrace_686037
  have hstable : (prefixWord ++ tailWord_686037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686037).length < 2 ^ (prefixWord ++ tailWord_686037).sum := by decide
  have hdescent : baseEnd_686037 < baseStart_686037 := by decide
  rcases family_descends (prefixWord ++ tailWord_686037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686065 : List Nat := [1, 2, 2, 2, 5, 1, 3, 6]
def baseStart_686065 : Nat := 118140960795 + 686065 * 2 ^ 59
def prefixEnd_686065 : Nat := 4983230072969 + 3 ^ 40 * 686065 * 2
def baseEnd_686065 : Nat := 26094896683478777869063

theorem tailTrace_686065 : CollatzResearch.WordTrace tailWord_686065 prefixEnd_686065 26094896683478777869063 := by
  unfold tailWord_686065
  simp only [CollatzResearch.WordTrace]
  refine ⟨25022846259511150418683649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16681897506340766945789099 25022846259511150418683649)
  ·
    refine ⟨18767134694633362814012737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25022846259511150418683649 18767134694633362814012737)
    ·
      refine ⟨14075351020975022110509553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18767134694633362814012737 14075351020975022110509553)
      ·
        refine ⟨10556513265731266582882165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14075351020975022110509553 10556513265731266582882165)
        ·
          refine ⟨989673118662306242145203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10556513265731266582882165 989673118662306242145203)
          ·
            refine ⟨1484509677993459363217805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989673118662306242145203 1484509677993459363217805)
            ·
              refine ⟨556691129247547261206677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1484509677993459363217805 556691129247547261206677)
              ·
                refine ⟨26094896683478777869063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 556691129247547261206677 26094896683478777869063)
                ·
                  rfl

theorem cell22_686065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 6].length) (baseStart_686065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686065 prefixEnd_686065 := by exact prefixLift 686065
  have htrace : WordTrace (prefixWord ++ tailWord_686065) baseStart_686065 baseEnd_686065 := by
    simpa [prefixWord, tailWord_686065, baseEnd_686065] using wordTrace_append hprefix tailTrace_686065
  have hstable : (prefixWord ++ tailWord_686065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686065).length < 2 ^ (prefixWord ++ tailWord_686065).sum := by decide
  have hdescent : baseEnd_686065 < baseStart_686065 := by decide
  rcases family_descends (prefixWord ++ tailWord_686065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686140 : List Nat := [2, 2, 2, 2, 2, 1, 1, 5, 1, 4]
def baseStart_686140 : Nat := 118140960795 + 686140 * 2 ^ 59
def prefixEnd_686140 : Nat := 4983230072969 + 3 ^ 40 * 686140 * 2
def baseEnd_686140 : Nat := 234879744184033805196337

theorem tailTrace_686140 : CollatzResearch.WordTrace tailWord_686140 prefixEnd_686140 234879744184033805196337 := by
  unfold tailWord_686140
  simp only [CollatzResearch.WordTrace]
  refine ⟨12512790867119719113831937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16683721156159625485109249 12512790867119719113831937)
  ·
    refine ⟨9384593150339789335373953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12512790867119719113831937 9384593150339789335373953)
    ·
      refine ⟨7038444862754842001530465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9384593150339789335373953 7038444862754842001530465)
      ·
        refine ⟨5278833647066131501147849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7038444862754842001530465 5278833647066131501147849)
        ·
          refine ⟨3959125235299598625860887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5278833647066131501147849 3959125235299598625860887)
          ·
            refine ⟨5938687852949397938791331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3959125235299598625860887 5938687852949397938791331)
            ·
              refine ⟨8908031779424096908186997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5938687852949397938791331 8908031779424096908186997)
              ·
                refine ⟨835127979321009085142531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8908031779424096908186997 835127979321009085142531)
                ·
                  refine ⟨1252691968981513627713797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 835127979321009085142531 1252691968981513627713797)
                  ·
                    refine ⟨234879744184033805196337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1252691968981513627713797 234879744184033805196337)
                    ·
                      rfl

theorem cell22_686140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_686140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686140 prefixEnd_686140 := by exact prefixLift 686140
  have htrace : WordTrace (prefixWord ++ tailWord_686140) baseStart_686140 baseEnd_686140 := by
    simpa [prefixWord, tailWord_686140, baseEnd_686140] using wordTrace_append hprefix tailTrace_686140
  have hstable : (prefixWord ++ tailWord_686140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686140).length < 2 ^ (prefixWord ++ tailWord_686140).sum := by decide
  have hdescent : baseEnd_686140 < baseStart_686140 := by decide
  rcases family_descends (prefixWord ++ tailWord_686140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686183 : List Nat := [1, 1, 5, 1, 1, 2, 1, 10]
def baseStart_686183 : Nat := 118140960795 + 686183 * 2 ^ 59
def prefixEnd_686183 : Nat := 4983230072969 + 3 ^ 40 * 686183 * 2
def baseEnd_686183 : Nat := 26099384884755114041245

theorem tailTrace_686183 : CollatzResearch.WordTrace tailWord_686183 prefixEnd_686183 26099384884755114041245 := by
  unfold tailWord_686183
  simp only [CollatzResearch.WordTrace]
  refine ⟨25027150073083656571479203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16684766715389104380986135 25027150073083656571479203)
  ·
    refine ⟨37540725109625484857218805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25027150073083656571479203 37540725109625484857218805)
    ·
      refine ⟨3519442979027389205364263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37540725109625484857218805 3519442979027389205364263)
      ·
        refine ⟨5279164468541083808046395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3519442979027389205364263 5279164468541083808046395)
        ·
          refine ⟨7918746702811625712069593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5279164468541083808046395 7918746702811625712069593)
          ·
            refine ⟨5939060027108719284052195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7918746702811625712069593 5939060027108719284052195)
            ·
              refine ⟨8908590040663078926078293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5939060027108719284052195 8908590040663078926078293)
              ·
                refine ⟨26099384884755114041245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8908590040663078926078293 26099384884755114041245)
                ·
                  rfl

theorem cell22_686183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 10].length) (baseStart_686183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686183 prefixEnd_686183 := by exact prefixLift 686183
  have htrace : WordTrace (prefixWord ++ tailWord_686183) baseStart_686183 baseEnd_686183 := by
    simpa [prefixWord, tailWord_686183, baseEnd_686183] using wordTrace_append hprefix tailTrace_686183
  have hstable : (prefixWord ++ tailWord_686183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686183).length < 2 ^ (prefixWord ++ tailWord_686183).sum := by decide
  have hdescent : baseEnd_686183 < baseStart_686183 := by decide
  rcases family_descends (prefixWord ++ tailWord_686183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686185 : List Nat := [1, 2, 1, 1, 1, 5, 4, 1, 2, 4]
def baseStart_686185 : Nat := 118140960795 + 686185 * 2 ^ 59
def prefixEnd_686185 : Nat := 4983230072969 + 3 ^ 40 * 686185 * 2
def baseEnd_686185 : Nat := 234895148603668687821199

theorem tailTrace_686185 : CollatzResearch.WordTrace tailWord_686185 prefixEnd_686185 234895148603668687821199 := by
  unfold tailWord_686185
  simp only [CollatzResearch.WordTrace]
  refine ⟨25027223019076410913052009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16684815346050940608701339 25027223019076410913052009)
  ·
    refine ⟨18770417264307308184789007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25027223019076410913052009 18770417264307308184789007)
    ·
      refine ⟨28155625896460962277183511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18770417264307308184789007 28155625896460962277183511)
      ·
        refine ⟨42233438844691443415775267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28155625896460962277183511 42233438844691443415775267)
        ·
          refine ⟨63350158267037165123662901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42233438844691443415775267 63350158267037165123662901)
          ·
            refine ⟨5939077337534734230343397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63350158267037165123662901 5939077337534734230343397)
            ·
              refine ⟨1113577000787762668189387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5939077337534734230343397 1113577000787762668189387)
              ·
                refine ⟨1670365501181644002284081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1113577000787762668189387 1670365501181644002284081)
                ·
                  refine ⟨1252774125886233001713061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1670365501181644002284081 1252774125886233001713061)
                  ·
                    refine ⟨234895148603668687821199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1252774125886233001713061 234895148603668687821199)
                    ·
                      rfl

theorem cell22_686185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 4].length) (baseStart_686185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686185 prefixEnd_686185 := by exact prefixLift 686185
  have htrace : WordTrace (prefixWord ++ tailWord_686185) baseStart_686185 baseEnd_686185 := by
    simpa [prefixWord, tailWord_686185, baseEnd_686185] using wordTrace_append hprefix tailTrace_686185
  have hstable : (prefixWord ++ tailWord_686185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686185).length < 2 ^ (prefixWord ++ tailWord_686185).sum := by decide
  have hdescent : baseEnd_686185 < baseStart_686185 := by decide
  rcases family_descends (prefixWord ++ tailWord_686185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686300 : List Nat := [2, 2, 5, 2, 1, 2, 1, 3, 1, 3]
def baseStart_686300 : Nat := 118140960795 + 686300 * 2 ^ 59
def prefixEnd_686300 : Nat := 4983230072969 + 3 ^ 40 * 686300 * 2
def baseEnd_686300 : Nat := 234934515453846721195847

theorem tailTrace_686300 : CollatzResearch.WordTrace tailWord_686300 prefixEnd_686300 234934515453846721195847 := by
  unfold tailWord_686300
  simp only [CollatzResearch.WordTrace]
  refine ⟨12515708706829892776744177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16687611609106523702325569 12515708706829892776744177)
  ·
    refine ⟨9386781530122419582558133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12515708706829892776744177 9386781530122419582558133)
    ·
      refine ⟨880010768448976835864825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9386781530122419582558133 880010768448976835864825)
      ·
        refine ⟨660008076336732626898619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 880010768448976835864825 660008076336732626898619)
        ·
          refine ⟨990012114505098940347929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660008076336732626898619 990012114505098940347929)
          ·
            refine ⟨742509085878824205260947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 990012114505098940347929 742509085878824205260947)
            ·
              refine ⟨1113763628818236307891421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 742509085878824205260947 1113763628818236307891421)
              ·
                refine ⟨417661360806838615459283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1113763628818236307891421 417661360806838615459283)
                ·
                  refine ⟨626492041210257923188925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 417661360806838615459283 626492041210257923188925)
                  ·
                    refine ⟨234934515453846721195847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 626492041210257923188925 234934515453846721195847)
                    ·
                      rfl

theorem cell22_686300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_686300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686300 prefixEnd_686300 := by exact prefixLift 686300
  have htrace : WordTrace (prefixWord ++ tailWord_686300) baseStart_686300 baseEnd_686300 := by
    simpa [prefixWord, tailWord_686300, baseEnd_686300] using wordTrace_append hprefix tailTrace_686300
  have hstable : (prefixWord ++ tailWord_686300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686300).length < 2 ^ (prefixWord ++ tailWord_686300).sum := by decide
  have hdescent : baseEnd_686300 < baseStart_686300 := by decide
  rcases family_descends (prefixWord ++ tailWord_686300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686305 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 3, 5]
def baseStart_686305 : Nat := 118140960795 + 686305 * 2 ^ 59
def prefixEnd_686305 : Nat := 4983230072969 + 3 ^ 40 * 686305 * 2
def baseEnd_686305 : Nat := 234936227056028374820831

theorem tailTrace_686305 : CollatzResearch.WordTrace tailWord_686305 prefixEnd_686305 234936227056028374820831 := by
  unfold tailWord_686305
  simp only [CollatzResearch.WordTrace]
  refine ⟨25031599778641671407420369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16687733185761114271613579 25031599778641671407420369)
  ·
    refine ⟨18773699833981253555565277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25031599778641671407420369 18773699833981253555565277)
    ·
      refine ⟨7040137437742970083336979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18773699833981253555565277 7040137437742970083336979)
      ·
        refine ⟨10560206156614455125005469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7040137437742970083336979 10560206156614455125005469)
        ·
          refine ⟨3960077308730420671877051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10560206156614455125005469 3960077308730420671877051)
          ·
            refine ⟨5940115963095631007815577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3960077308730420671877051 5940115963095631007815577)
            ·
              refine ⟨4455086972321723255861683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5940115963095631007815577 4455086972321723255861683)
              ·
                refine ⟨6682630458482584883792525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4455086972321723255861683 6682630458482584883792525)
                ·
                  refine ⟨2505986421930969331422197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6682630458482584883792525 2505986421930969331422197)
                  ·
                    refine ⟨234936227056028374820831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2505986421930969331422197 234936227056028374820831)
                    ·
                      rfl

theorem cell22_686305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_686305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686305 prefixEnd_686305 := by exact prefixLift 686305
  have htrace : WordTrace (prefixWord ++ tailWord_686305) baseStart_686305 baseEnd_686305 := by
    simpa [prefixWord, tailWord_686305, baseEnd_686305] using wordTrace_append hprefix tailTrace_686305
  have hstable : (prefixWord ++ tailWord_686305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686305).length < 2 ^ (prefixWord ++ tailWord_686305).sum := by decide
  have hdescent : baseEnd_686305 < baseStart_686305 := by decide
  rcases family_descends (prefixWord ++ tailWord_686305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686335 : List Nat := [1, 1, 2, 2, 1, 4, 4, 7]
def baseStart_686335 : Nat := 118140960795 + 686335 * 2 ^ 59
def prefixEnd_686335 : Nat := 4983230072969 + 3 ^ 40 * 686335 * 2
def baseEnd_686335 : Nat := 26105166296568699618971

theorem tailTrace_686335 : CollatzResearch.WordTrace tailWord_686335 prefixEnd_686335 26105166296568699618971 := by
  unfold tailWord_686335
  simp only [CollatzResearch.WordTrace]
  refine ⟨25032693968532986531012459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16688462645688657687341639 25032693968532986531012459)
  ·
    refine ⟨37549040952799479796518689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25032693968532986531012459 37549040952799479796518689)
    ·
      refine ⟨28161780714599609847389017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37549040952799479796518689 28161780714599609847389017)
      ·
        refine ⟨21121335535949707385541763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28161780714599609847389017 21121335535949707385541763)
        ·
          refine ⟨31682003303924561078312645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21121335535949707385541763 31682003303924561078312645)
          ·
            refine ⟨5940375619485855202183621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31682003303924561078312645 5940375619485855202183621)
            ·
              refine ⟨1113820428653597850409429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5940375619485855202183621 1113820428653597850409429)
              ·
                refine ⟨26105166296568699618971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1113820428653597850409429 26105166296568699618971)
                ·
                  rfl

theorem cell22_686335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 7].length) (baseStart_686335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686335 prefixEnd_686335 := by exact prefixLift 686335
  have htrace : WordTrace (prefixWord ++ tailWord_686335) baseStart_686335 baseEnd_686335 := by
    simpa [prefixWord, tailWord_686335, baseEnd_686335] using wordTrace_append hprefix tailTrace_686335
  have hstable : (prefixWord ++ tailWord_686335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686335).length < 2 ^ (prefixWord ++ tailWord_686335).sum := by decide
  have hdescent : baseEnd_686335 < baseStart_686335 := by decide
  rcases family_descends (prefixWord ++ tailWord_686335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686343 : List Nat := [1, 1, 4, 5, 2, 1, 1, 2, 1, 4]
def baseStart_686343 : Nat := 118140960795 + 686343 * 2 ^ 59
def prefixEnd_686343 : Nat := 4983230072969 + 3 ^ 40 * 686343 * 2
def baseEnd_686343 : Nat := 234949235232608942370715

theorem tailTrace_686343 : CollatzResearch.WordTrace tailWord_686343 prefixEnd_686343 234949235232608942370715 := by
  unfold tailWord_686343
  simp only [CollatzResearch.WordTrace]
  refine ⟨25032985752504003897303683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16688657168336002598202455 25032985752504003897303683)
  ·
    refine ⟨37549478628756005845955525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25032985752504003897303683 37549478628756005845955525)
    ·
      refine ⟨7040527242891751096116661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37549478628756005845955525 7040527242891751096116661)
      ·
        refine ⟨660049429021101665260937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7040527242891751096116661 660049429021101665260937)
        ·
          refine ⟨495037071765826248945703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 660049429021101665260937 495037071765826248945703)
          ·
            refine ⟨742555607648739373418555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495037071765826248945703 742555607648739373418555)
            ·
              refine ⟨1113833411473109060127833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 742555607648739373418555 1113833411473109060127833)
              ·
                refine ⟨835375058604831795095875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1113833411473109060127833 835375058604831795095875)
                ·
                  refine ⟨1253062587907247692643813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 835375058604831795095875 1253062587907247692643813)
                  ·
                    refine ⟨234949235232608942370715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1253062587907247692643813 234949235232608942370715)
                    ·
                      rfl

theorem cell22_686343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_686343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686343 prefixEnd_686343 := by exact prefixLift 686343
  have htrace : WordTrace (prefixWord ++ tailWord_686343) baseStart_686343 baseEnd_686343 := by
    simpa [prefixWord, tailWord_686343, baseEnd_686343] using wordTrace_append hprefix tailTrace_686343
  have hstable : (prefixWord ++ tailWord_686343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686343).length < 2 ^ (prefixWord ++ tailWord_686343).sum := by decide
  have hdescent : baseEnd_686343 < baseStart_686343 := by decide
  rcases family_descends (prefixWord ++ tailWord_686343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686380 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 7]
def baseStart_686380 : Nat := 118140960795 + 686380 * 2 ^ 59
def prefixEnd_686380 : Nat := 4983230072969 + 3 ^ 40 * 686380 * 2
def baseEnd_686380 : Nat := 78320633696251059731867

theorem tailTrace_686380 : CollatzResearch.WordTrace tailWord_686380 prefixEnd_686380 78320633696251059731867 := by
  unfold tailWord_686380
  simp only [CollatzResearch.WordTrace]
  refine ⟨12517167626684979608200297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16689556835579972810933729 12517167626684979608200297)
  ·
    refine ⟨9387875720013734706150223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12517167626684979608200297 9387875720013734706150223)
    ·
      refine ⟨14081813580020602059225335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9387875720013734706150223 14081813580020602059225335)
      ·
        refine ⟨21122720370030903088838003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14081813580020602059225335 21122720370030903088838003)
        ·
          refine ⟨31684080555046354633257005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21122720370030903088838003 31684080555046354633257005)
          ·
            refine ⟨11881530208142382987471377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31684080555046354633257005 11881530208142382987471377)
            ·
              refine ⟨8911147656106787240603533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11881530208142382987471377 8911147656106787240603533)
              ·
                refine ⟨3341680371040045215226325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8911147656106787240603533 3341680371040045215226325)
                ·
                  refine ⟨78320633696251059731867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3341680371040045215226325 78320633696251059731867)
                  ·
                    rfl

theorem cell22_686380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_686380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686380 prefixEnd_686380 := by exact prefixLift 686380
  have htrace : WordTrace (prefixWord ++ tailWord_686380) baseStart_686380 baseEnd_686380 := by
    simpa [prefixWord, tailWord_686380, baseEnd_686380] using wordTrace_append hprefix tailTrace_686380
  have hstable : (prefixWord ++ tailWord_686380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686380).length < 2 ^ (prefixWord ++ tailWord_686380).sum := by decide
  have hdescent : baseEnd_686380 < baseStart_686380 := by decide
  rcases family_descends (prefixWord ++ tailWord_686380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686401 : List Nat := [1, 2, 5, 2, 2, 1, 1, 2, 3, 3]
def baseStart_686401 : Nat := 118140960795 + 686401 * 2 ^ 59
def prefixEnd_686401 : Nat := 4983230072969 + 3 ^ 40 * 686401 * 2
def baseEnd_686401 : Nat := 234969089817916124420537

theorem tailTrace_686401 : CollatzResearch.WordTrace tailWord_686401 prefixEnd_686401 234969089817916124420537 := by
  unfold tailWord_686401
  simp only [CollatzResearch.WordTrace]
  refine ⟨25035101186293879802915057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16690067457529253201943371 25035101186293879802915057)
  ·
    refine ⟨18776325889720409852186293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25035101186293879802915057 18776325889720409852186293)
    ·
      refine ⟨1760280552161288423642465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18776325889720409852186293 1760280552161288423642465)
      ·
        refine ⟨1320210414120966317731849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1760280552161288423642465 1320210414120966317731849)
        ·
          refine ⟨990157810590724738298887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1320210414120966317731849 990157810590724738298887)
          ·
            refine ⟨1485236715886087107448331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990157810590724738298887 1485236715886087107448331)
            ·
              refine ⟨2227855073829130661172497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1485236715886087107448331 2227855073829130661172497)
              ·
                refine ⟨1670891305371847995879373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2227855073829130661172497 1670891305371847995879373)
                ·
                  refine ⟨626584239514442998454765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1670891305371847995879373 626584239514442998454765)
                  ·
                    refine ⟨234969089817916124420537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 626584239514442998454765 234969089817916124420537)
                    ·
                      rfl

theorem cell22_686401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_686401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686401 prefixEnd_686401 := by exact prefixLift 686401
  have htrace : WordTrace (prefixWord ++ tailWord_686401) baseStart_686401 baseEnd_686401 := by
    simpa [prefixWord, tailWord_686401, baseEnd_686401] using wordTrace_append hprefix tailTrace_686401
  have hstable : (prefixWord ++ tailWord_686401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686401).length < 2 ^ (prefixWord ++ tailWord_686401).sum := by decide
  have hdescent : baseEnd_686401 < baseStart_686401 := by decide
  rcases family_descends (prefixWord ++ tailWord_686401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686425 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 10]
def baseStart_686425 : Nat := 118140960795 + 686425 * 2 ^ 59
def prefixEnd_686425 : Nat := 4983230072969 + 3 ^ 40 * 686425 * 2
def baseEnd_686425 : Nat := 78325768502796020606821

theorem tailTrace_686425 : CollatzResearch.WordTrace tailWord_686425 prefixEnd_686425 78325768502796020606821 := by
  unfold tailWord_686425
  simp only [CollatzResearch.WordTrace]
  refine ⟨25035976538206931901788729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16690651025471287934525819 25035976538206931901788729)
  ·
    refine ⟨18776982403655198926341547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25035976538206931901788729 18776982403655198926341547)
    ·
      refine ⟨28165473605482798389512321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18776982403655198926341547 28165473605482798389512321)
      ·
        refine ⟨21124105204112098792134241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28165473605482798389512321 21124105204112098792134241)
        ·
          refine ⟨15843078903084074094100681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21124105204112098792134241 15843078903084074094100681)
          ·
            refine ⟨11882309177313055570575511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15843078903084074094100681 11882309177313055570575511)
            ·
              refine ⟨17823463765969583355863267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11882309177313055570575511 17823463765969583355863267)
              ·
                refine ⟨26735195648954375033794901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17823463765969583355863267 26735195648954375033794901)
                ·
                  refine ⟨78325768502796020606821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 26735195648954375033794901 78325768502796020606821)
                  ·
                    rfl

theorem cell22_686425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 10].length) (baseStart_686425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686425 prefixEnd_686425 := by exact prefixLift 686425
  have htrace : WordTrace (prefixWord ++ tailWord_686425) baseStart_686425 baseEnd_686425 := by
    simpa [prefixWord, tailWord_686425, baseEnd_686425] using wordTrace_append hprefix tailTrace_686425
  have hstable : (prefixWord ++ tailWord_686425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686425).length < 2 ^ (prefixWord ++ tailWord_686425).sum := by decide
  have hdescent : baseEnd_686425 < baseStart_686425 := by decide
  rcases family_descends (prefixWord ++ tailWord_686425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686472 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 1, 6]
def baseStart_686472 : Nat := 118140960795 + 686472 * 2 ^ 59
def prefixEnd_686472 : Nat := 4983230072969 + 3 ^ 40 * 686472 * 2
def baseEnd_686472 : Nat := 234993394568895605895319

theorem tailTrace_686472 : CollatzResearch.WordTrace tailWord_686472 prefixEnd_686472 234993394568895605895319 := by
  unfold tailWord_686472
  simp only [CollatzResearch.WordTrace]
  refine ⟨12518845384518329464374835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16691793846024439285833113 12518845384518329464374835)
  ·
    refine ⟨18778268076777494196562253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12518845384518329464374835 18778268076777494196562253)
    ·
      refine ⟨7041850528791560323710845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18778268076777494196562253 7041850528791560323710845)
      ·
        refine ⟨2640693948296835121391567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7041850528791560323710845 2640693948296835121391567)
        ·
          refine ⟨3961040922445252682087351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2640693948296835121391567 3961040922445252682087351)
          ·
            refine ⟨5941561383667879023131027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3961040922445252682087351 5941561383667879023131027)
            ·
              refine ⟨8912342075501818534696541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5941561383667879023131027 8912342075501818534696541)
              ·
                refine ⟨3342128278313181950511203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8912342075501818534696541 3342128278313181950511203)
                ·
                  refine ⟨5013192417469772925766805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3342128278313181950511203 5013192417469772925766805)
                  ·
                    refine ⟨234993394568895605895319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5013192417469772925766805 234993394568895605895319)
                    ·
                      rfl

theorem cell22_686472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_686472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686472 prefixEnd_686472 := by exact prefixLift 686472
  have htrace : WordTrace (prefixWord ++ tailWord_686472) baseStart_686472 baseEnd_686472 := by
    simpa [prefixWord, tailWord_686472, baseEnd_686472] using wordTrace_append hprefix tailTrace_686472
  have hstable : (prefixWord ++ tailWord_686472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686472).length < 2 ^ (prefixWord ++ tailWord_686472).sum := by decide
  have hdescent : baseEnd_686472 < baseStart_686472 := by decide
  rcases family_descends (prefixWord ++ tailWord_686472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686476 : List Nat := [2, 2, 1, 2, 1, 6, 1, 3, 4]
def baseStart_686476 : Nat := 118140960795 + 686476 * 2 ^ 59
def prefixEnd_686476 : Nat := 4983230072969 + 3 ^ 40 * 686476 * 2
def baseEnd_686476 : Nat := 78331587950213642931769

theorem tailTrace_686476 : CollatzResearch.WordTrace tailWord_686476 prefixEnd_686476 78331587950213642931769 := by
  unfold tailWord_686476
  simp only [CollatzResearch.WordTrace]
  refine ⟨12518918330511083805947641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16691891107348111741263521 12518918330511083805947641)
  ·
    refine ⟨9389188747883312854460731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12518918330511083805947641 9389188747883312854460731)
    ·
      refine ⟨14083783121824969281691097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9389188747883312854460731 14083783121824969281691097)
      ·
        refine ⟨10562837341368726961268323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14083783121824969281691097 10562837341368726961268323)
        ·
          refine ⟨15844256012053090441902485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10562837341368726961268323 15844256012053090441902485)
          ·
            refine ⟨742699500564988614464179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15844256012053090441902485 742699500564988614464179)
            ·
              refine ⟨1114049250847482921696269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 742699500564988614464179 1114049250847482921696269)
              ·
                refine ⟨417768469067806095636101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1114049250847482921696269 417768469067806095636101)
                ·
                  refine ⟨78331587950213642931769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 417768469067806095636101 78331587950213642931769)
                  ·
                    rfl

theorem cell22_686476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 4].length) (baseStart_686476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686476 prefixEnd_686476 := by exact prefixLift 686476
  have htrace : WordTrace (prefixWord ++ tailWord_686476) baseStart_686476 baseEnd_686476 := by
    simpa [prefixWord, tailWord_686476, baseEnd_686476] using wordTrace_append hprefix tailTrace_686476
  have hstable : (prefixWord ++ tailWord_686476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686476).length < 2 ^ (prefixWord ++ tailWord_686476).sum := by decide
  have hdescent : baseEnd_686476 < baseStart_686476 := by decide
  rcases family_descends (prefixWord ++ tailWord_686476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686493 : List Nat := [1, 4, 2, 1, 4, 1, 3, 2, 4]
def baseStart_686493 : Nat := 118140960795 + 686493 * 2 ^ 59
def prefixEnd_686493 : Nat := 4983230072969 + 3 ^ 40 * 686493 * 2
def baseEnd_686493 : Nat := 78333527766019517040085

theorem tailTrace_686493 : CollatzResearch.WordTrace tailWord_686493 prefixEnd_686493 78333527766019517040085 := by
  unfold tailWord_686493
  simp only [CollatzResearch.WordTrace]
  refine ⟨25038456701960579515264133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16692304467973719676842755 25038456701960579515264133)
  ·
    refine ⟨4694710631617608659112025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25038456701960579515264133 4694710631617608659112025)
    ·
      refine ⟨3521032973713206494334019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4694710631617608659112025 3521032973713206494334019)
      ·
        refine ⟨5281549460569809741501029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3521032973713206494334019 5281549460569809741501029)
        ·
          refine ⟨990290523856839326531443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5281549460569809741501029 990290523856839326531443)
          ·
            refine ⟨1485435785785258989797165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990290523856839326531443 1485435785785258989797165)
            ·
              refine ⟨557038419669472121173937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1485435785785258989797165 557038419669472121173937)
              ·
                refine ⟨417778814752104090880453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557038419669472121173937 417778814752104090880453)
                ·
                  refine ⟨78333527766019517040085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 417778814752104090880453 78333527766019517040085)
                  ·
                    rfl

theorem cell22_686493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_686493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686493 prefixEnd_686493 := by exact prefixLift 686493
  have htrace : WordTrace (prefixWord ++ tailWord_686493) baseStart_686493 baseEnd_686493 := by
    simpa [prefixWord, tailWord_686493, baseEnd_686493] using wordTrace_append hprefix tailTrace_686493
  have hstable : (prefixWord ++ tailWord_686493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686493).length < 2 ^ (prefixWord ++ tailWord_686493).sum := by decide
  have hdescent : baseEnd_686493 < baseStart_686493 := by decide
  rcases family_descends (prefixWord ++ tailWord_686493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686504 : List Nat := [2, 1, 6, 1, 1, 1, 1, 9]
def baseStart_686504 : Nat := 118140960795 + 686504 * 2 ^ 59
def prefixEnd_686504 : Nat := 4983230072969 + 3 ^ 40 * 686504 * 2
def baseEnd_686504 : Nat := 26111594313650909899469

theorem tailTrace_686504 : CollatzResearch.WordTrace tailWord_686504 prefixEnd_686504 26111594313650909899469 := by
  unfold tailWord_686504
  simp only [CollatzResearch.WordTrace]
  refine ⟨12519428952460364196957283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16692571936613818929276377 12519428952460364196957283)
  ·
    refine ⟨18779143428690546295435925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12519428952460364196957283 18779143428690546295435925)
    ·
      refine ⟨880272348219869357598559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18779143428690546295435925 880272348219869357598559)
      ·
        refine ⟨1320408522329804036397839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 880272348219869357598559 1320408522329804036397839)
        ·
          refine ⟨1980612783494706054596759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1320408522329804036397839 1980612783494706054596759)
          ·
            refine ⟨2970919175242059081895139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1980612783494706054596759 2970919175242059081895139)
            ·
              refine ⟨4456378762863088622842709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2970919175242059081895139 4456378762863088622842709)
              ·
                refine ⟨26111594313650909899469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4456378762863088622842709 26111594313650909899469)
                ·
                  rfl

theorem cell22_686504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 9].length) (baseStart_686504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686504 prefixEnd_686504 := by exact prefixLift 686504
  have htrace : WordTrace (prefixWord ++ tailWord_686504) baseStart_686504 baseEnd_686504 := by
    simpa [prefixWord, tailWord_686504, baseEnd_686504] using wordTrace_append hprefix tailTrace_686504
  have hstable : (prefixWord ++ tailWord_686504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686504).length < 2 ^ (prefixWord ++ tailWord_686504).sum := by decide
  have hdescent : baseEnd_686504 < baseStart_686504 := by decide
  rcases family_descends (prefixWord ++ tailWord_686504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686549 : List Nat := [1, 3, 2, 3, 1, 2, 1, 4, 5]
def baseStart_686549 : Nat := 118140960795 + 686549 * 2 ^ 59
def prefixEnd_686549 : Nat := 4983230072969 + 3 ^ 40 * 686549 * 2
def baseEnd_686549 : Nat := 78339917747497690573361

theorem tailTrace_686549 : CollatzResearch.WordTrace tailWord_686549 prefixEnd_686549 78339917747497690573361 := by
  unfold tailWord_686549
  simp only [CollatzResearch.WordTrace]
  refine ⟨25040499189757701079302701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16693666126505134052868467 25040499189757701079302701)
  ·
    refine ⟨9390187196159137904738513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25040499189757701079302701 9390187196159137904738513)
    ·
      refine ⟨7042640397119353428553885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9390187196159137904738513 7042640397119353428553885)
      ·
        refine ⟨2640990148919757535707707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7042640397119353428553885 2640990148919757535707707)
        ·
          refine ⟨3961485223379636303561561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2640990148919757535707707 3961485223379636303561561)
          ·
            refine ⟨2971113917534727227671171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3961485223379636303561561 2971113917534727227671171)
            ·
              refine ⟨4456670876302090841506757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2971113917534727227671171 4456670876302090841506757)
              ·
                refine ⟨835625789306642032782517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4456670876302090841506757 835625789306642032782517)
                ·
                  refine ⟨78339917747497690573361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 835625789306642032782517 78339917747497690573361)
                  ·
                    rfl

theorem cell22_686549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_686549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686549 prefixEnd_686549 := by exact prefixLift 686549
  have htrace : WordTrace (prefixWord ++ tailWord_686549) baseStart_686549 baseEnd_686549 := by
    simpa [prefixWord, tailWord_686549, baseEnd_686549] using wordTrace_append hprefix tailTrace_686549
  have hstable : (prefixWord ++ tailWord_686549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686549).length < 2 ^ (prefixWord ++ tailWord_686549).sum := by decide
  have hdescent : baseEnd_686549 < baseStart_686549 := by decide
  rcases family_descends (prefixWord ++ tailWord_686549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686579 : List Nat := [1, 1, 1, 2, 2, 2, 4, 4, 1, 4]
def baseStart_686579 : Nat := 118140960795 + 686579 * 2 ^ 59
def prefixEnd_686579 : Nat := 4983230072969 + 3 ^ 40 * 686579 * 2
def baseEnd_686579 : Nat := 235030022855582993469991

theorem tailTrace_686579 : CollatzResearch.WordTrace tailWord_686579 prefixEnd_686579 235030022855582993469991 := by
  unfold tailWord_686579
  simp only [CollatzResearch.WordTrace]
  refine ⟨25041593379649016202894791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16694395586432677468596527 25041593379649016202894791)
  ·
    refine ⟨37562390069473524304342187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25041593379649016202894791 37562390069473524304342187)
    ·
      refine ⟨56343585104210286456513281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37562390069473524304342187 56343585104210286456513281)
      ·
        refine ⟨42257688828157714842384961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56343585104210286456513281 42257688828157714842384961)
        ·
          refine ⟨31693266621118286131788721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42257688828157714842384961 31693266621118286131788721)
          ·
            refine ⟨23769949965838714598841541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31693266621118286131788721 23769949965838714598841541)
            ·
              refine ⟨4456865618594758987282789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23769949965838714598841541 4456865618594758987282789)
              ·
                refine ⟨835662303486517310115523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4456865618594758987282789 835662303486517310115523)
                ·
                  refine ⟨1253493455229775965173285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 835662303486517310115523 1253493455229775965173285)
                  ·
                    refine ⟨235030022855582993469991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1253493455229775965173285 235030022855582993469991)
                    ·
                      rfl

theorem cell22_686579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 4].length) (baseStart_686579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686579 prefixEnd_686579 := by exact prefixLift 686579
  have htrace : WordTrace (prefixWord ++ tailWord_686579) baseStart_686579 baseEnd_686579 := by
    simpa [prefixWord, tailWord_686579, baseEnd_686579] using wordTrace_append hprefix tailTrace_686579
  have hstable : (prefixWord ++ tailWord_686579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686579).length < 2 ^ (prefixWord ++ tailWord_686579).sum := by decide
  have hdescent : baseEnd_686579 < baseStart_686579 := by decide
  rcases family_descends (prefixWord ++ tailWord_686579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686607 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 3, 6]
def baseStart_686607 : Nat := 118140960795 + 686607 * 2 ^ 59
def prefixEnd_686607 : Nat := 4983230072969 + 3 ^ 40 * 686607 * 2
def baseEnd_686607 : Nat := 235039607827800253769905

theorem tailTrace_686607 : CollatzResearch.WordTrace tailWord_686607 prefixEnd_686607 235039607827800253769905 := by
  unfold tailWord_686607
  simp only [CollatzResearch.WordTrace]
  refine ⟨25042614623547576984914075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16695076415698384656609383 25042614623547576984914075)
  ·
    refine ⟨37563921935321365477371113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25042614623547576984914075 37563921935321365477371113)
    ·
      refine ⟨28172941451491024108028335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37563921935321365477371113 28172941451491024108028335)
      ·
        refine ⟨42259412177236536162042503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28172941451491024108028335 42259412177236536162042503)
        ·
          refine ⟨63389118265854804243063755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42259412177236536162042503 63389118265854804243063755)
          ·
            refine ⟨95083677398782206364595633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63389118265854804243063755 95083677398782206364595633)
            ·
              refine ⟨71312758049086654773446725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95083677398782206364595633 71312758049086654773446725)
              ·
                refine ⟨13371142134203747770021261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71312758049086654773446725 13371142134203747770021261)
                ·
                  refine ⟨5014178300326405413757973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13371142134203747770021261 5014178300326405413757973)
                  ·
                    refine ⟨235039607827800253769905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5014178300326405413757973 235039607827800253769905)
                    ·
                      rfl

theorem cell22_686607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_686607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686607 prefixEnd_686607 := by exact prefixLift 686607
  have htrace : WordTrace (prefixWord ++ tailWord_686607) baseStart_686607 baseEnd_686607 := by
    simpa [prefixWord, tailWord_686607, baseEnd_686607] using wordTrace_append hprefix tailTrace_686607
  have hstable : (prefixWord ++ tailWord_686607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686607).length < 2 ^ (prefixWord ++ tailWord_686607).sum := by decide
  have hdescent : baseEnd_686607 < baseStart_686607 := by decide
  rcases family_descends (prefixWord ++ tailWord_686607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686662 : List Nat := [6, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_686662 : Nat := 118140960795 + 686662 * 2 ^ 59
def prefixEnd_686662 : Nat := 4983230072969 + 3 ^ 40 * 686662 * 2
def baseEnd_686662 : Nat := 78352811817266147881579

theorem tailTrace_686662 : CollatzResearch.WordTrace tailWord_686662 prefixEnd_686662 78352811817266147881579 := by
  unfold tailWord_686662
  simp only [CollatzResearch.WordTrace]
  refine ⟨782644394948385043067695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16696413758898880918777493 782644394948385043067695)
  ·
    refine ⟨1173966592422577564601543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 782644394948385043067695 1173966592422577564601543)
    ·
      refine ⟨1760949888633866346902315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1173966592422577564601543 1760949888633866346902315)
      ·
        refine ⟨2641424832950799520353473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1760949888633866346902315 2641424832950799520353473)
        ·
          refine ⟨1981068624713099640265105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2641424832950799520353473 1981068624713099640265105)
          ·
            refine ⟨1485801468534824730198829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1981068624713099640265105 1485801468534824730198829)
            ·
              refine ⟨557175550700559273824561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1485801468534824730198829 557175550700559273824561)
              ·
                refine ⟨417881663025419455368421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557175550700559273824561 417881663025419455368421)
                ·
                  refine ⟨78352811817266147881579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 417881663025419455368421 78352811817266147881579)
                  ·
                    rfl

theorem cell22_686662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_686662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686662 prefixEnd_686662 := by exact prefixLift 686662
  have htrace : WordTrace (prefixWord ++ tailWord_686662) baseStart_686662 baseEnd_686662 := by
    simpa [prefixWord, tailWord_686662, baseEnd_686662] using wordTrace_append hprefix tailTrace_686662
  have hstable : (prefixWord ++ tailWord_686662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686662).length < 2 ^ (prefixWord ++ tailWord_686662).sum := by decide
  have hdescent : baseEnd_686662 < baseStart_686662 := by decide
  rcases family_descends (prefixWord ++ tailWord_686662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686671 : List Nat := [1, 1, 2, 1, 1, 2, 7, 1, 3, 3]
def baseStart_686671 : Nat := 118140960795 + 686671 * 2 ^ 59
def prefixEnd_686671 : Nat := 4983230072969 + 3 ^ 40 * 686671 * 2
def baseEnd_686671 : Nat := 235061516335725420169709

theorem tailTrace_686671 : CollatzResearch.WordTrace tailWord_686671 prefixEnd_686671 235061516335725420169709 := by
  unfold tailWord_686671
  simp only [CollatzResearch.WordTrace]
  refine ⟨25044948895315715915243867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16696632596877143943495911 25044948895315715915243867)
  ·
    refine ⟨37567423342973573872865801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25044948895315715915243867 37567423342973573872865801)
    ·
      refine ⟨28175567507230180404649351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37567423342973573872865801 28175567507230180404649351)
      ·
        refine ⟨42263351260845270606974027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28175567507230180404649351 42263351260845270606974027)
        ·
          refine ⟨63395026891267905910461041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42263351260845270606974027 63395026891267905910461041)
          ·
            refine ⟨47546270168450929432845781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63395026891267905910461041 47546270168450929432845781)
            ·
              refine ⟨1114365707073068658582323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 47546270168450929432845781 1114365707073068658582323)
              ·
                refine ⟨1671548560609602987873485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114365707073068658582323 1671548560609602987873485)
                ·
                  refine ⟨626830710228601120452557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1671548560609602987873485 626830710228601120452557)
                  ·
                    refine ⟨235061516335725420169709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 626830710228601120452557 235061516335725420169709)
                    ·
                      rfl

theorem cell22_686671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 3].length) (baseStart_686671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686671 prefixEnd_686671 := by exact prefixLift 686671
  have htrace : WordTrace (prefixWord ++ tailWord_686671) baseStart_686671 baseEnd_686671 := by
    simpa [prefixWord, tailWord_686671, baseEnd_686671] using wordTrace_append hprefix tailTrace_686671
  have hstable : (prefixWord ++ tailWord_686671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686671).length < 2 ^ (prefixWord ++ tailWord_686671).sum := by decide
  have hdescent : baseEnd_686671 < baseStart_686671 := by decide
  rcases family_descends (prefixWord ++ tailWord_686671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686729 : List Nat := [1, 2, 1, 1, 4, 1, 1, 5, 6]
def baseStart_686729 : Nat := 118140960795 + 686729 * 2 ^ 59
def prefixEnd_686729 : Nat := 4983230072969 + 3 ^ 40 * 686729 * 2
def baseEnd_686729 : Nat := 78360456973677534073177

theorem tailTrace_686729 : CollatzResearch.WordTrace tailWord_686729 prefixEnd_686729 78360456973677534073177 := by
  unfold tailWord_686729
  simp only [CollatzResearch.WordTrace]
  refine ⟨25047064329105591820855241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16698042886070394547236827 25047064329105591820855241)
  ·
    refine ⟨18785298246829193865641431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25047064329105591820855241 18785298246829193865641431)
    ·
      refine ⟨28177947370243790798462147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18785298246829193865641431 28177947370243790798462147)
      ·
        refine ⟨42266921055365686197693221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28177947370243790798462147 42266921055365686197693221)
        ·
          refine ⟨7925047697881066162067479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42266921055365686197693221 7925047697881066162067479)
          ·
            refine ⟨11887571546821599243101219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7925047697881066162067479 11887571546821599243101219)
            ·
              refine ⟨17831357320232398864651829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11887571546821599243101219 17831357320232398864651829)
              ·
                refine ⟨1671689748771787393561109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17831357320232398864651829 1671689748771787393561109)
                ·
                  refine ⟨78360456973677534073177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1671689748771787393561109 78360456973677534073177)
                  ·
                    rfl

theorem cell22_686729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 6].length) (baseStart_686729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686729 prefixEnd_686729 := by exact prefixLift 686729
  have htrace : WordTrace (prefixWord ++ tailWord_686729) baseStart_686729 baseEnd_686729 := by
    simpa [prefixWord, tailWord_686729, baseEnd_686729] using wordTrace_append hprefix tailTrace_686729
  have hstable : (prefixWord ++ tailWord_686729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686729).length < 2 ^ (prefixWord ++ tailWord_686729).sum := by decide
  have hdescent : baseEnd_686729 < baseStart_686729 := by decide
  rcases family_descends (prefixWord ++ tailWord_686729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686765 : List Nat := [1, 5, 2, 1, 1, 2, 4, 1, 1, 4]
def baseStart_686765 : Nat := 118140960795 + 686765 * 2 ^ 59
def prefixEnd_686765 : Nat := 4983230072969 + 3 ^ 40 * 686765 * 2
def baseEnd_686765 : Nat := 235093694456740508319421

theorem tailTrace_686765 : CollatzResearch.WordTrace tailWord_686765 prefixEnd_686765 235093694456740508319421 := by
  unfold tailWord_686765
  simp only [CollatzResearch.WordTrace]
  refine ⟨25048377356975169969165749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16698918237983446646110499 25048377356975169969165749)
  ·
    refine ⟨2348285377216422184609289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25048377356975169969165749 2348285377216422184609289)
    ·
      refine ⟨1761214032912316638456967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2348285377216422184609289 1761214032912316638456967)
      ·
        refine ⟨2641821049368474957685451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1761214032912316638456967 2641821049368474957685451)
        ·
          refine ⟨3962731574052712436528177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2641821049368474957685451 3962731574052712436528177)
          ·
            refine ⟨2972048680539534327396133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3962731574052712436528177 2972048680539534327396133)
            ·
              refine ⟨557259127601162686386775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2972048680539534327396133 557259127601162686386775)
              ·
                refine ⟨835888691401744029580163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557259127601162686386775 835888691401744029580163)
                ·
                  refine ⟨1253833037102616044370245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 835888691401744029580163 1253833037102616044370245)
                  ·
                    refine ⟨235093694456740508319421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1253833037102616044370245 235093694456740508319421)
                    ·
                      rfl

theorem cell22_686765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_686765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686765 prefixEnd_686765 := by exact prefixLift 686765
  have htrace : WordTrace (prefixWord ++ tailWord_686765) baseStart_686765 baseEnd_686765 := by
    simpa [prefixWord, tailWord_686765, baseEnd_686765] using wordTrace_append hprefix tailTrace_686765
  have hstable : (prefixWord ++ tailWord_686765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686765).length < 2 ^ (prefixWord ++ tailWord_686765).sum := by decide
  have hdescent : baseEnd_686765 < baseStart_686765 := by decide
  rcases family_descends (prefixWord ++ tailWord_686765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686789 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 4, 7]
def baseStart_686789 : Nat := 118140960795 + 686789 * 2 ^ 59
def prefixEnd_686789 : Nat := 4983230072969 + 3 ^ 40 * 686789 * 2
def baseEnd_686789 : Nat := 235101910147212445719347

theorem tailTrace_686789 : CollatzResearch.WordTrace tailWord_686789 prefixEnd_686789 235101910147212445719347 := by
  unfold tailWord_686789
  simp only [CollatzResearch.WordTrace]
  refine ⟨25049252708888222068039421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16699501805925481378692947 25049252708888222068039421)
  ·
    refine ⟨9393469765833083275514783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25049252708888222068039421 9393469765833083275514783)
    ·
      refine ⟨14090204648749624913272175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9393469765833083275514783 14090204648749624913272175)
      ·
        refine ⟨21135306973124437369908263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14090204648749624913272175 21135306973124437369908263)
        ·
          refine ⟨31702960459686656054862395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21135306973124437369908263 31702960459686656054862395)
          ·
            refine ⟨47554440689529984082293593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31702960459686656054862395 47554440689529984082293593)
            ·
              refine ⟨35665830517147488061720195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47554440689529984082293593 35665830517147488061720195)
              ·
                refine ⟨53498745775721232092580293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35665830517147488061720195 53498745775721232092580293)
                ·
                  refine ⟨10031014832947731017358805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53498745775721232092580293 10031014832947731017358805)
                  ·
                    refine ⟨235101910147212445719347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10031014832947731017358805 235101910147212445719347)
                    ·
                      rfl

theorem cell22_686789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_686789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686789 prefixEnd_686789 := by exact prefixLift 686789
  have htrace : WordTrace (prefixWord ++ tailWord_686789) baseStart_686789 baseEnd_686789 := by
    simpa [prefixWord, tailWord_686789, baseEnd_686789] using wordTrace_append hprefix tailTrace_686789
  have hstable : (prefixWord ++ tailWord_686789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686789).length < 2 ^ (prefixWord ++ tailWord_686789).sum := by decide
  have hdescent : baseEnd_686789 < baseStart_686789 := by decide
  rcases family_descends (prefixWord ++ tailWord_686789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686808 : List Nat := [2, 1, 2, 2, 3, 4, 2, 6]
def baseStart_686808 : Nat := 118140960795 + 686808 * 2 ^ 59
def prefixEnd_686808 : Nat := 4983230072969 + 3 ^ 40 * 686808 * 2
def baseEnd_686808 : Nat := 26123157137278081054921

theorem tailTrace_686808 : CollatzResearch.WordTrace tailWord_686808 prefixEnd_686808 26123157137278081054921 := by
  unfold tailWord_686808
  simp only [CollatzResearch.WordTrace]
  refine ⟨12524972847909694156490539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16699963797212925541987385 12524972847909694156490539)
  ·
    refine ⟨18787459271864541234735809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12524972847909694156490539 18787459271864541234735809)
    ·
      refine ⟨14090594453898405926051857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18787459271864541234735809 14090594453898405926051857)
      ·
        refine ⟨10567945840423804444538893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14090594453898405926051857 10567945840423804444538893)
        ·
          refine ⟨3962979690158926666702085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10567945840423804444538893 3962979690158926666702085)
          ·
            refine ⟨743058691904798750006641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3962979690158926666702085 743058691904798750006641)
            ·
              refine ⟨557294018928599062504981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743058691904798750006641 557294018928599062504981)
              ·
                refine ⟨26123157137278081054921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 557294018928599062504981 26123157137278081054921)
                ·
                  rfl

theorem cell22_686808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 6].length) (baseStart_686808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686808 prefixEnd_686808 := by exact prefixLift 686808
  have htrace : WordTrace (prefixWord ++ tailWord_686808) baseStart_686808 baseEnd_686808 := by
    simpa [prefixWord, tailWord_686808, baseEnd_686808] using wordTrace_append hprefix tailTrace_686808
  have hstable : (prefixWord ++ tailWord_686808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686808).length < 2 ^ (prefixWord ++ tailWord_686808).sum := by decide
  have hdescent : baseEnd_686808 < baseStart_686808 := by decide
  rcases family_descends (prefixWord ++ tailWord_686808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686926 : List Nat := [4, 1, 1, 1, 1, 1, 1, 12]
def baseStart_686926 : Nat := 118140960795 + 686926 * 2 ^ 59
def prefixEnd_686926 : Nat := 4983230072969 + 3 ^ 40 * 686926 * 2
def baseEnd_686926 : Nat := 26127645338554417227103

theorem tailTrace_686926 : CollatzResearch.WordTrace tailWord_686926 prefixEnd_686926 26127645338554417227103 := by
  unfold tailWord_686926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3131781188673986808222079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16702833006261262977184421 3131781188673986808222079)
  ·
    refine ⟨4697671783010980212333119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3131781188673986808222079 4697671783010980212333119)
    ·
      refine ⟨7046507674516470318499679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4697671783010980212333119 7046507674516470318499679)
      ·
        refine ⟨10569761511774705477749519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7046507674516470318499679 10569761511774705477749519)
        ·
          refine ⟨15854642267662058216624279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10569761511774705477749519 15854642267662058216624279)
          ·
            refine ⟨23781963401493087324936419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15854642267662058216624279 23781963401493087324936419)
            ·
              refine ⟨35672945102239630987404629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23781963401493087324936419 35672945102239630987404629)
              ·
                refine ⟨26127645338554417227103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 35672945102239630987404629 26127645338554417227103)
                ·
                  rfl

theorem cell22_686926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_686926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686926 prefixEnd_686926 := by exact prefixLift 686926
  have htrace : WordTrace (prefixWord ++ tailWord_686926) baseStart_686926 baseEnd_686926 := by
    simpa [prefixWord, tailWord_686926, baseEnd_686926] using wordTrace_append hprefix tailTrace_686926
  have hstable : (prefixWord ++ tailWord_686926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686926).length < 2 ^ (prefixWord ++ tailWord_686926).sum := by decide
  have hdescent : baseEnd_686926 < baseStart_686926 := by decide
  rcases family_descends (prefixWord ++ tailWord_686926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686928 : List Nat := [2, 1, 1, 1, 1, 4, 5, 1, 2, 4]
def baseStart_686928 : Nat := 118140960795 + 686928 * 2 ^ 59
def prefixEnd_686928 : Nat := 4983230072969 + 3 ^ 40 * 686928 * 2
def baseEnd_686928 : Nat := 235149492687862416493921

theorem tailTrace_686928 : CollatzResearch.WordTrace tailWord_686928 prefixEnd_686928 235149492687862416493921 := by
  unfold tailWord_686928
  simp only [CollatzResearch.WordTrace]
  refine ⟨12527161227692324403674719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16702881636923099204899625 12527161227692324403674719)
  ·
    refine ⟨18790741841538486605512079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12527161227692324403674719 18790741841538486605512079)
    ·
      refine ⟨28186112762307729908268119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18790741841538486605512079 28186112762307729908268119)
      ·
        refine ⟨42279169143461594862402179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28186112762307729908268119 42279169143461594862402179)
        ·
          refine ⟨63418753715192392293603269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42279169143461594862402179 63418753715192392293603269)
          ·
            refine ⟨11891016321598573555050613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63418753715192392293603269 11891016321598573555050613)
            ·
              refine ⟨1114782780149866270785995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11891016321598573555050613 1114782780149866270785995)
              ·
                refine ⟨1672174170224799406178993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114782780149866270785995 1672174170224799406178993)
                ·
                  refine ⟨1254130627668599554634245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1672174170224799406178993 1254130627668599554634245)
                  ·
                    refine ⟨235149492687862416493921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1254130627668599554634245 235149492687862416493921)
                    ·
                      rfl

theorem cell22_686928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 2, 4].length) (baseStart_686928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686928 prefixEnd_686928 := by exact prefixLift 686928
  have htrace : WordTrace (prefixWord ++ tailWord_686928) baseStart_686928 baseEnd_686928 := by
    simpa [prefixWord, tailWord_686928, baseEnd_686928] using wordTrace_append hprefix tailTrace_686928
  have hstable : (prefixWord ++ tailWord_686928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686928).length < 2 ^ (prefixWord ++ tailWord_686928).sum := by decide
  have hdescent : baseEnd_686928 < baseStart_686928 := by decide
  rcases family_descends (prefixWord ++ tailWord_686928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686932 : List Nat := [2, 4, 1, 1, 4, 1, 2, 3, 4]
def baseStart_686932 : Nat := 118140960795 + 686932 * 2 ^ 59
def prefixEnd_686932 : Nat := 4983230072969 + 3 ^ 40 * 686932 * 2
def baseEnd_686932 : Nat := 78383620656535913131303

theorem tailTrace_686932 : CollatzResearch.WordTrace tailWord_686932 prefixEnd_686932 78383620656535913131303 := by
  unfold tailWord_686932
  simp only [CollatzResearch.WordTrace]
  refine ⟨12527234173685078745247525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16702978898246771660330033 12527234173685078745247525)
  ·
    refine ⟨2348856407565952264733911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12527234173685078745247525 2348856407565952264733911)
    ·
      refine ⟨3523284611348928397100867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2348856407565952264733911 3523284611348928397100867)
      ·
        refine ⟨5284926917023392595651301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3523284611348928397100867 5284926917023392595651301)
        ·
          refine ⟨990923796941886111684619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5284926917023392595651301 990923796941886111684619)
          ·
            refine ⟨1486385695412829167526929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990923796941886111684619 1486385695412829167526929)
            ·
              refine ⟨1114789271559621875645197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1486385695412829167526929 1114789271559621875645197)
              ·
                refine ⟨418045976834858203366949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1114789271559621875645197 418045976834858203366949)
                ·
                  refine ⟨78383620656535913131303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 418045976834858203366949 78383620656535913131303)
                  ·
                    rfl

theorem cell22_686932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_686932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686932 prefixEnd_686932 := by exact prefixLift 686932
  have htrace : WordTrace (prefixWord ++ tailWord_686932) baseStart_686932 baseEnd_686932 := by
    simpa [prefixWord, tailWord_686932, baseEnd_686932] using wordTrace_append hprefix tailTrace_686932
  have hstable : (prefixWord ++ tailWord_686932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686932).length < 2 ^ (prefixWord ++ tailWord_686932).sum := by decide
  have hdescent : baseEnd_686932 < baseStart_686932 := by decide
  rcases family_descends (prefixWord ++ tailWord_686932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686947 : List Nat := [1, 1, 1, 5, 3, 3, 1, 2, 2, 3]
def baseStart_686947 : Nat := 118140960795 + 686947 * 2 ^ 59
def prefixEnd_686947 : Nat := 4983230072969 + 3 ^ 40 * 686947 * 2
def baseEnd_686947 : Nat := 235155996776152700268863

theorem tailTrace_686947 : CollatzResearch.WordTrace tailWord_686947 prefixEnd_686947 235155996776152700268863 := by
  unfold tailWord_686947
  simp only [CollatzResearch.WordTrace]
  refine ⟨25055015442315815052291095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16703343628210543368194063 25055015442315815052291095)
  ·
    refine ⟨37582523163473722578436643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25055015442315815052291095 37582523163473722578436643)
    ·
      refine ⟨56373784745210583867654965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37582523163473722578436643 56373784745210583867654965)
      ·
        refine ⟨5285042319863492237592653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56373784745210583867654965 5285042319863492237592653)
        ·
          refine ⟨1981890869948809589097245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5285042319863492237592653 1981890869948809589097245)
          ·
            refine ⟨743209076230803595911467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1981890869948809589097245 743209076230803595911467)
            ·
              refine ⟨1114813614346205393867201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743209076230803595911467 1114813614346205393867201)
              ·
                refine ⟨836110210759654045400401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1114813614346205393867201 836110210759654045400401)
                ·
                  refine ⟨627082658069740534050301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 836110210759654045400401 627082658069740534050301)
                  ·
                    refine ⟨235155996776152700268863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 627082658069740534050301 235155996776152700268863)
                    ·
                      rfl

theorem cell22_686947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 3].length) (baseStart_686947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_686947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_686947 prefixEnd_686947 := by exact prefixLift 686947
  have htrace : WordTrace (prefixWord ++ tailWord_686947) baseStart_686947 baseEnd_686947 := by
    simpa [prefixWord, tailWord_686947, baseEnd_686947] using wordTrace_append hprefix tailTrace_686947
  have hstable : (prefixWord ++ tailWord_686947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686947).length < 2 ^ (prefixWord ++ tailWord_686947).sum := by decide
  have hdescent : baseEnd_686947 < baseStart_686947 := by decide
  rcases family_descends (prefixWord ++ tailWord_686947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687050 : List Nat := [3, 1, 2, 1, 2, 1, 1, 7, 4]
def baseStart_687050 : Nat := 118140960795 + 687050 * 2 ^ 59
def prefixEnd_687050 : Nat := 4983230072969 + 3 ^ 40 * 687050 * 2
def baseEnd_687050 : Nat := 78397085260364921647849

theorem tailTrace_687050 : CollatzResearch.WordTrace tailWord_687050 prefixEnd_687050 78397085260364921647849 := by
  unfold tailWord_687050
  simp only [CollatzResearch.WordTrace]
  refine ⟨6264693040235665910822651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16705848107295109095527069 6264693040235665910822651)
  ·
    refine ⟨9397039560353498866233977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6264693040235665910822651 9397039560353498866233977)
    ·
      refine ⟨7047779670265124149675483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9397039560353498866233977 7047779670265124149675483)
      ·
        refine ⟨10571669505397686224513225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7047779670265124149675483 10571669505397686224513225)
        ·
          refine ⟨7928752129048264668384919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10571669505397686224513225 7928752129048264668384919)
          ·
            refine ⟨11893128193572397002577379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7928752129048264668384919 11893128193572397002577379)
            ·
              refine ⟨17839692290358595503866069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11893128193572397002577379 17839692290358595503866069)
              ·
                refine ⟨418117788055279582121861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17839692290358595503866069 418117788055279582121861)
                ·
                  refine ⟨78397085260364921647849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 418117788055279582121861 78397085260364921647849)
                  ·
                    rfl

theorem cell22_687050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 4].length) (baseStart_687050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687050 prefixEnd_687050 := by exact prefixLift 687050
  have htrace : WordTrace (prefixWord ++ tailWord_687050) baseStart_687050 baseEnd_687050 := by
    simpa [prefixWord, tailWord_687050, baseEnd_687050] using wordTrace_append hprefix tailTrace_687050
  have hstable : (prefixWord ++ tailWord_687050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687050).length < 2 ^ (prefixWord ++ tailWord_687050).sum := by decide
  have hdescent : baseEnd_687050 < baseStart_687050 := by decide
  rcases family_descends (prefixWord ++ tailWord_687050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687052 : List Nat := [2, 2, 1, 4, 1, 1, 5, 1, 1, 4]
def baseStart_687052 : Nat := 118140960795 + 687052 * 2 ^ 59
def prefixEnd_687052 : Nat := 4983230072969 + 3 ^ 40 * 687052 * 2
def baseEnd_687052 : Nat := 235191940421967426393541

theorem tailTrace_687052 : CollatzResearch.WordTrace tailWord_687052 prefixEnd_687052 235191940421967426393541 := by
  unfold tailWord_687052
  simp only [CollatzResearch.WordTrace]
  refine ⟨12529422553467708992431705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16705896737956945323242273 12529422553467708992431705)
  ·
    refine ⟨9397066915100781744323779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12529422553467708992431705 9397066915100781744323779)
    ·
      refine ⟨14095600372651172616485669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9397066915100781744323779 14095600372651172616485669)
      ·
        refine ⟨2642925069872094865591063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14095600372651172616485669 2642925069872094865591063)
        ·
          refine ⟨3964387604808142298386595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2642925069872094865591063 3964387604808142298386595)
          ·
            refine ⟨5946581407212213447579893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3964387604808142298386595 5946581407212213447579893)
            ·
              refine ⟨557492006926145010710615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5946581407212213447579893 557492006926145010710615)
              ·
                refine ⟨836238010389217516065923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557492006926145010710615 836238010389217516065923)
                ·
                  refine ⟨1254357015583826274098885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 836238010389217516065923 1254357015583826274098885)
                  ·
                    refine ⟨235191940421967426393541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1254357015583826274098885 235191940421967426393541)
                    ·
                      rfl

theorem cell22_687052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 1, 4].length) (baseStart_687052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687052 prefixEnd_687052 := by exact prefixLift 687052
  have htrace : WordTrace (prefixWord ++ tailWord_687052) baseStart_687052 baseEnd_687052 := by
    simpa [prefixWord, tailWord_687052, baseEnd_687052] using wordTrace_append hprefix tailTrace_687052
  have hstable : (prefixWord ++ tailWord_687052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687052).length < 2 ^ (prefixWord ++ tailWord_687052).sum := by decide
  have hdescent : baseEnd_687052 < baseStart_687052 := by decide
  rcases family_descends (prefixWord ++ tailWord_687052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687063 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 4, 4]
def baseStart_687063 : Nat := 118140960795 + 687063 * 2 ^ 59
def prefixEnd_687063 : Nat := 4983230072969 + 3 ^ 40 * 687063 * 2
def baseEnd_687063 : Nat := 235195705946767064368507

theorem tailTrace_687063 : CollatzResearch.WordTrace tailWord_687063 prefixEnd_687063 235195705946767064368507 := by
  unfold tailWord_687063
  simp only [CollatzResearch.WordTrace]
  refine ⟨25059246309895566863513843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16706164206597044575675895 25059246309895566863513843)
  ·
    refine ⟨37588869464843350295270765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25059246309895566863513843 37588869464843350295270765)
    ·
      refine ⟨14095826049316256360726537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37588869464843350295270765 14095826049316256360726537)
      ·
        refine ⟨10571869536987192270544903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14095826049316256360726537 10571869536987192270544903)
        ·
          refine ⟨15857804305480788405817355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10571869536987192270544903 15857804305480788405817355)
          ·
            refine ⟨23786706458221182608726033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15857804305480788405817355 23786706458221182608726033)
            ·
              refine ⟨17840029843665886956544525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23786706458221182608726033 17840029843665886956544525)
              ·
                refine ⟨6690011191374707608704197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17840029843665886956544525 6690011191374707608704197)
                ·
                  refine ⟨1254377098382757676632037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6690011191374707608704197 1254377098382757676632037)
                  ·
                    refine ⟨235195705946767064368507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1254377098382757676632037 235195705946767064368507)
                    ·
                      rfl

theorem cell22_687063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_687063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687063 prefixEnd_687063 := by exact prefixLift 687063
  have htrace : WordTrace (prefixWord ++ tailWord_687063) baseStart_687063 baseEnd_687063 := by
    simpa [prefixWord, tailWord_687063, baseEnd_687063] using wordTrace_append hprefix tailTrace_687063
  have hstable : (prefixWord ++ tailWord_687063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687063).length < 2 ^ (prefixWord ++ tailWord_687063).sum := by decide
  have hdescent : baseEnd_687063 < baseStart_687063 := by decide
  rcases family_descends (prefixWord ++ tailWord_687063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687082 : List Nat := [3, 1, 3, 1, 2, 2, 2, 3, 2, 3]
def baseStart_687082 : Nat := 118140960795 + 687082 * 2 ^ 59
def prefixEnd_687082 : Nat := 4983230072969 + 3 ^ 40 * 687082 * 2
def baseEnd_687082 : Nat := 235202210035057348143449

theorem tailTrace_687082 : CollatzResearch.WordTrace tailWord_687082 prefixEnd_687082 235202210035057348143449 := by
  unfold tailWord_687082
  simp only [CollatzResearch.WordTrace]
  refine ⟨6264984824206683277113875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16706626197884488738970333 6264984824206683277113875)
  ·
    refine ⟨9397477236310024915670813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6264984824206683277113875 9397477236310024915670813)
    ·
      refine ⟨3524053963616259343376555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9397477236310024915670813 3524053963616259343376555)
      ·
        refine ⟨5286080945424389015064833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3524053963616259343376555 5286080945424389015064833)
        ·
          refine ⟨3964560709068291761298625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5286080945424389015064833 3964560709068291761298625)
          ·
            refine ⟨2973420531801218820973969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3964560709068291761298625 2973420531801218820973969)
            ·
              refine ⟨2230065398850914115730477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2973420531801218820973969 2230065398850914115730477)
              ·
                refine ⟨836274524569092793398929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2230065398850914115730477 836274524569092793398929)
                ·
                  refine ⟨627205893426819595049197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 836274524569092793398929 627205893426819595049197)
                  ·
                    refine ⟨235202210035057348143449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 627205893426819595049197 235202210035057348143449)
                    ·
                      rfl

theorem cell22_687082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_687082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687082 prefixEnd_687082 := by exact prefixLift 687082
  have htrace : WordTrace (prefixWord ++ tailWord_687082) baseStart_687082 baseEnd_687082 := by
    simpa [prefixWord, tailWord_687082, baseEnd_687082] using wordTrace_append hprefix tailTrace_687082
  have hstable : (prefixWord ++ tailWord_687082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687082).length < 2 ^ (prefixWord ++ tailWord_687082).sum := by decide
  have hdescent : baseEnd_687082 < baseStart_687082 := by decide
  rcases family_descends (prefixWord ++ tailWord_687082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687127 : List Nat := [1, 1, 3, 5, 1, 1, 1, 3, 3, 3]
def baseStart_687127 : Nat := 118140960795 + 687127 * 2 ^ 59
def prefixEnd_687127 : Nat := 4983230072969 + 3 ^ 40 * 687127 * 2
def baseEnd_687127 : Nat := 235217614454692230768311

theorem tailTrace_687127 : CollatzResearch.WordTrace tailWord_687127 prefixEnd_687127 235217614454692230768311 := by
  unfold tailWord_687127
  simp only [CollatzResearch.WordTrace]
  refine ⟨25061580581663705793843635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16707720387775803862562423 25061580581663705793843635)
  ·
    refine ⟨37592370872495558690765453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25061580581663705793843635 37592370872495558690765453)
    ·
      refine ⟨14097139077185834509037045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37592370872495558690765453 14097139077185834509037045)
      ·
        refine ⟨1321606788486171985222223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14097139077185834509037045 1321606788486171985222223)
        ·
          refine ⟨1982410182729257977833335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1321606788486171985222223 1982410182729257977833335)
          ·
            refine ⟨2973615274093886966750003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982410182729257977833335 2973615274093886966750003)
            ·
              refine ⟨4460422911140830450125005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2973615274093886966750003 4460422911140830450125005)
              ·
                refine ⟨1672658591677811418796877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4460422911140830450125005 1672658591677811418796877)
                ·
                  refine ⟨627246971879179282048829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1672658591677811418796877 627246971879179282048829)
                  ·
                    refine ⟨235217614454692230768311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 627246971879179282048829 235217614454692230768311)
                    ·
                      rfl

theorem cell22_687127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_687127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687127 prefixEnd_687127 := by exact prefixLift 687127
  have htrace : WordTrace (prefixWord ++ tailWord_687127) baseStart_687127 baseEnd_687127 := by
    simpa [prefixWord, tailWord_687127, baseEnd_687127] using wordTrace_append hprefix tailTrace_687127
  have hstable : (prefixWord ++ tailWord_687127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687127).length < 2 ^ (prefixWord ++ tailWord_687127).sum := by decide
  have hdescent : baseEnd_687127 < baseStart_687127 := by decide
  rcases family_descends (prefixWord ++ tailWord_687127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687161 : List Nat := [1, 2, 1, 5, 2, 3, 1, 3, 1, 3]
def baseStart_687161 : Nat := 118140960795 + 687161 * 2 ^ 59
def prefixEnd_687161 : Nat := 4983230072969 + 3 ^ 40 * 687161 * 2
def baseEnd_687161 : Nat := 235229253349527475418207

theorem tailTrace_687161 : CollatzResearch.WordTrace tailWord_687161 prefixEnd_687161 235229253349527475418207 := by
  unfold tailWord_687161
  simp only [CollatzResearch.WordTrace]
  refine ⟨25062820663540529600581337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16708547109027019733720891 25062820663540529600581337)
  ·
    refine ⟨18797115497655397200436003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25062820663540529600581337 18797115497655397200436003)
    ·
      refine ⟨28195673246483095800654005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18797115497655397200436003 28195673246483095800654005)
      ·
        refine ⟨2643344366857790231311313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28195673246483095800654005 2643344366857790231311313)
        ·
          refine ⟨1982508275143342673483485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2643344366857790231311313 1982508275143342673483485)
          ·
            refine ⟨743440603178753502556307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1982508275143342673483485 743440603178753502556307)
            ·
              refine ⟨1115160904768130253834461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743440603178753502556307 1115160904768130253834461)
              ·
                refine ⟨418185339288048845187923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1115160904768130253834461 418185339288048845187923)
                ·
                  refine ⟨627278008932073267781885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 418185339288048845187923 627278008932073267781885)
                  ·
                    refine ⟨235229253349527475418207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 627278008932073267781885 235229253349527475418207)
                    ·
                      rfl

theorem cell22_687161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 1, 3].length) (baseStart_687161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687161 prefixEnd_687161 := by exact prefixLift 687161
  have htrace : WordTrace (prefixWord ++ tailWord_687161) baseStart_687161 baseEnd_687161 := by
    simpa [prefixWord, tailWord_687161, baseEnd_687161] using wordTrace_append hprefix tailTrace_687161
  have hstable : (prefixWord ++ tailWord_687161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687161).length < 2 ^ (prefixWord ++ tailWord_687161).sum := by decide
  have hdescent : baseEnd_687161 < baseStart_687161 := by decide
  rcases family_descends (prefixWord ++ tailWord_687161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687183 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 2, 9]
def baseStart_687183 : Nat := 118140960795 + 687183 * 2 ^ 59
def prefixEnd_687183 : Nat := 4983230072969 + 3 ^ 40 * 687183 * 2
def baseEnd_687183 : Nat := 235236784399126751368139

theorem tailTrace_687183 : CollatzResearch.WordTrace tailWord_687183 prefixEnd_687183 235236784399126751368139 := by
  unfold tailWord_687183
  simp only [CollatzResearch.WordTrace]
  refine ⟨25063623069460827357882203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16709082046307218238588135 25063623069460827357882203)
  ·
    refine ⟨37595434604191241036823305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25063623069460827357882203 37595434604191241036823305)
    ·
      refine ⟨28196575953143430777617479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37595434604191241036823305 28196575953143430777617479)
      ·
        refine ⟨42294863929715146166426219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28196575953143430777617479 42294863929715146166426219)
        ·
          refine ⟨63442295894572719249639329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42294863929715146166426219 63442295894572719249639329)
          ·
            refine ⟨47581721920929539437229497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63442295894572719249639329 47581721920929539437229497)
            ·
              refine ⟨35686291440697154577922123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47581721920929539437229497 35686291440697154577922123)
              ·
                refine ⟨53529437161045731866883185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35686291440697154577922123 53529437161045731866883185)
                ·
                  refine ⟨40147077870784298900162389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53529437161045731866883185 40147077870784298900162389)
                  ·
                    refine ⟨235236784399126751368139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 40147077870784298900162389 235236784399126751368139)
                    ·
                      rfl

theorem cell22_687183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_687183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687183 prefixEnd_687183 := by exact prefixLift 687183
  have htrace : WordTrace (prefixWord ++ tailWord_687183) baseStart_687183 baseEnd_687183 := by
    simpa [prefixWord, tailWord_687183, baseEnd_687183] using wordTrace_append hprefix tailTrace_687183
  have hstable : (prefixWord ++ tailWord_687183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687183).length < 2 ^ (prefixWord ++ tailWord_687183).sum := by decide
  have hdescent : baseEnd_687183 < baseStart_687183 := by decide
  rcases family_descends (prefixWord ++ tailWord_687183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687185 : List Nat := [1, 2, 2, 1, 3, 1, 5, 1, 6]
def baseStart_687185 : Nat := 118140960795 + 687185 * 2 ^ 59
def prefixEnd_687185 : Nat := 4983230072969 + 3 ^ 40 * 687185 * 2
def baseEnd_687185 : Nat := 78412489679999804272711

theorem tailTrace_687185 : CollatzResearch.WordTrace tailWord_687185 prefixEnd_687185 78412489679999804272711 := by
  unfold tailWord_687185
  simp only [CollatzResearch.WordTrace]
  refine ⟨25063696015453581699455009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16709130676969054466303339 25063696015453581699455009)
  ·
    refine ⟨18797772011590186274591257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25063696015453581699455009 18797772011590186274591257)
    ·
      refine ⟨14098329008692639705943443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18797772011590186274591257 14098329008692639705943443)
      ·
        refine ⟨21147493513038959558915165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14098329008692639705943443 21147493513038959558915165)
        ·
          refine ⟨7930310067389609834593187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21147493513038959558915165 7930310067389609834593187)
          ·
            refine ⟨11895465101084414751889781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7930310067389609834593187 11895465101084414751889781)
            ·
              refine ⟨1115199853226663882989667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11895465101084414751889781 1115199853226663882989667)
              ·
                refine ⟨1672799779839995824484501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1115199853226663882989667 1672799779839995824484501)
                ·
                  refine ⟨78412489679999804272711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1672799779839995824484501 78412489679999804272711)
                  ·
                    rfl

theorem cell22_687185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 6].length) (baseStart_687185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687185 prefixEnd_687185 := by exact prefixLift 687185
  have htrace : WordTrace (prefixWord ++ tailWord_687185) baseStart_687185 baseEnd_687185 := by
    simpa [prefixWord, tailWord_687185, baseEnd_687185] using wordTrace_append hprefix tailTrace_687185
  have hstable : (prefixWord ++ tailWord_687185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687185).length < 2 ^ (prefixWord ++ tailWord_687185).sum := by decide
  have hdescent : baseEnd_687185 < baseStart_687185 := by decide
  rcases family_descends (prefixWord ++ tailWord_687185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687200 : List Nat := [2, 1, 1, 3, 2, 2, 2, 3, 1, 5]
def baseStart_687200 : Nat := 118140960795 + 687200 * 2 ^ 59
def prefixEnd_687200 : Nat := 4983230072969 + 3 ^ 40 * 687200 * 2
def baseEnd_687200 : Nat := 235242603846544373693087

theorem tailTrace_687200 : CollatzResearch.WordTrace tailWord_687200 prefixEnd_687200 235242603846544373693087 := by
  unfold tailWord_687200
  simp only [CollatzResearch.WordTrace]
  refine ⟨12532121555199619630625527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16709495406932826174167369 12532121555199619630625527)
  ·
    refine ⟨18798182332799429445938291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12532121555199619630625527 18798182332799429445938291)
    ·
      refine ⟨28197273499199144168907437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18798182332799429445938291 28197273499199144168907437)
      ·
        refine ⟨10573977562199679063340289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28197273499199144168907437 10573977562199679063340289)
        ·
          refine ⟨7930483171649759297505217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10573977562199679063340289 7930483171649759297505217)
          ·
            refine ⟨5947862378737319473128913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7930483171649759297505217 5947862378737319473128913)
            ·
              refine ⟨4460896784052989604846685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5947862378737319473128913 4460896784052989604846685)
              ·
                refine ⟨1672836294019871101817507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4460896784052989604846685 1672836294019871101817507)
                ·
                  refine ⟨2509254441029806652726261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1672836294019871101817507 2509254441029806652726261)
                  ·
                    refine ⟨235242603846544373693087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2509254441029806652726261 235242603846544373693087)
                    ·
                      rfl

theorem cell22_687200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 1, 5].length) (baseStart_687200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687200 prefixEnd_687200 := by exact prefixLift 687200
  have htrace : WordTrace (prefixWord ++ tailWord_687200) baseStart_687200 baseEnd_687200 := by
    simpa [prefixWord, tailWord_687200, baseEnd_687200] using wordTrace_append hprefix tailTrace_687200
  have hstable : (prefixWord ++ tailWord_687200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687200).length < 2 ^ (prefixWord ++ tailWord_687200).sum := by decide
  have hdescent : baseEnd_687200 < baseStart_687200 := by decide
  rcases family_descends (prefixWord ++ tailWord_687200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687236 : List Nat := [2, 3, 2, 1, 2, 4, 2, 2, 4]
def baseStart_687236 : Nat := 118140960795 + 687236 * 2 ^ 59
def prefixEnd_687236 : Nat := 4983230072969 + 3 ^ 40 * 687236 * 2
def baseEnd_687236 : Nat := 78418309127417426597659

theorem tailTrace_687236 : CollatzResearch.WordTrace tailWord_687236 prefixEnd_687236 78418309127417426597659 := by
  unfold tailWord_687236
  simp only [CollatzResearch.WordTrace]
  refine ⟨12532778069134408704780781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16710370758845878273041041 12532778069134408704780781)
  ·
    refine ⟨4699791775925403264292793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12532778069134408704780781 4699791775925403264292793)
    ·
      refine ⟨3524843831944052448219595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4699791775925403264292793 3524843831944052448219595)
      ·
        refine ⟨5287265747916078672329393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3524843831944052448219595 5287265747916078672329393)
        ·
          refine ⟨3965449310937059004247045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5287265747916078672329393 3965449310937059004247045)
          ·
            refine ⟨743521745800698563296321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3965449310937059004247045 743521745800698563296321)
            ·
              refine ⟨557641309350523922472241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743521745800698563296321 557641309350523922472241)
              ·
                refine ⟨418230982012892941854181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557641309350523922472241 418230982012892941854181)
                ·
                  refine ⟨78418309127417426597659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 418230982012892941854181 78418309127417426597659)
                  ·
                    rfl

theorem cell22_687236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_687236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687236 prefixEnd_687236 := by exact prefixLift 687236
  have htrace : WordTrace (prefixWord ++ tailWord_687236) baseStart_687236 baseEnd_687236 := by
    simpa [prefixWord, tailWord_687236, baseEnd_687236] using wordTrace_append hprefix tailTrace_687236
  have hstable : (prefixWord ++ tailWord_687236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687236).length < 2 ^ (prefixWord ++ tailWord_687236).sum := by decide
  have hdescent : baseEnd_687236 < baseStart_687236 := by decide
  rcases family_descends (prefixWord ++ tailWord_687236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687266 : List Nat := [3, 3, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_687266 : Nat := 118140960795 + 687266 * 2 ^ 59
def prefixEnd_687266 : Nat := 4983230072969 + 3 ^ 40 * 687266 * 2
def baseEnd_687266 : Nat := 235265196995342201542885

theorem tailTrace_687266 : CollatzResearch.WordTrace tailWord_687266 prefixEnd_687266 235265196995342201542885 := by
  unfold tailWord_687266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6266662582040033133288413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16711100218773421688769101 6266662582040033133288413)
  ·
    refine ⟨2349998468265012424983155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6266662582040033133288413 2349998468265012424983155)
    ·
      refine ⟨3524997702397518637474733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2349998468265012424983155 3524997702397518637474733)
      ·
        refine ⟨1321874138399069489053025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3524997702397518637474733 1321874138399069489053025)
        ·
          refine ⟨991405603799302116789769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1321874138399069489053025 991405603799302116789769)
          ·
            refine ⟨743554202849476587592327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 991405603799302116789769 743554202849476587592327)
            ·
              refine ⟨1115331304274214881388491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743554202849476587592327 1115331304274214881388491)
              ·
                refine ⟨1672996956411322322082737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1115331304274214881388491 1672996956411322322082737)
                ·
                  refine ⟨1254747717308491741562053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1672996956411322322082737 1254747717308491741562053)
                  ·
                    refine ⟨235265196995342201542885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1254747717308491741562053 235265196995342201542885)
                    ·
                      rfl

theorem cell22_687266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_687266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687266 prefixEnd_687266 := by exact prefixLift 687266
  have htrace : WordTrace (prefixWord ++ tailWord_687266) baseStart_687266 baseEnd_687266 := by
    simpa [prefixWord, tailWord_687266, baseEnd_687266] using wordTrace_append hprefix tailTrace_687266
  have hstable : (prefixWord ++ tailWord_687266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687266).length < 2 ^ (prefixWord ++ tailWord_687266).sum := by decide
  have hdescent : baseEnd_687266 < baseStart_687266 := by decide
  rcases family_descends (prefixWord ++ tailWord_687266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687279 : List Nat := [1, 1, 2, 1, 2, 3, 3, 5, 1, 3]
def baseStart_687279 : Nat := 118140960795 + 687279 * 2 ^ 59
def prefixEnd_687279 : Nat := 4983230072969 + 3 ^ 40 * 687279 * 2
def baseEnd_687279 : Nat := 235269647161014500967845

theorem tailTrace_687279 : CollatzResearch.WordTrace tailWord_687279 prefixEnd_687279 235269647161014500967845 := by
  unfold tailWord_687279
  simp only [CollatzResearch.WordTrace]
  refine ⟨25067124477113035753376891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16711416318075357168917927 25067124477113035753376891)
  ·
    refine ⟨37600686715669553630065337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25067124477113035753376891 37600686715669553630065337)
    ·
      refine ⟨28200515036752165222549003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37600686715669553630065337 28200515036752165222549003)
      ·
        refine ⟨42300772555128247833823505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28200515036752165222549003 42300772555128247833823505)
        ·
          refine ⟨31725579416346185875367629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42300772555128247833823505 31725579416346185875367629)
          ·
            refine ⟨11897092281129819703262861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31725579416346185875367629 11897092281129819703262861)
            ·
              refine ⟨4461409605423682388723573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11897092281129819703262861 4461409605423682388723573)
              ·
                refine ⟨418257150508470223942835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4461409605423682388723573 418257150508470223942835)
                ·
                  refine ⟨627385725762705335914253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 418257150508470223942835 627385725762705335914253)
                  ·
                    refine ⟨235269647161014500967845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 627385725762705335914253 235269647161014500967845)
                    ·
                      rfl

theorem cell22_687279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 1, 3].length) (baseStart_687279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687279 prefixEnd_687279 := by exact prefixLift 687279
  have htrace : WordTrace (prefixWord ++ tailWord_687279) baseStart_687279 baseEnd_687279 := by
    simpa [prefixWord, tailWord_687279, baseEnd_687279] using wordTrace_append hprefix tailTrace_687279
  have hstable : (prefixWord ++ tailWord_687279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687279).length < 2 ^ (prefixWord ++ tailWord_687279).sum := by decide
  have hdescent : baseEnd_687279 < baseStart_687279 := by decide
  rcases family_descends (prefixWord ++ tailWord_687279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687292 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 7]
def baseStart_687292 : Nat := 118140960795 + 687292 * 2 ^ 59
def prefixEnd_687292 : Nat := 4983230072969 + 3 ^ 40 * 687292 * 2
def baseEnd_687292 : Nat := 78424699108895600130935

theorem tailTrace_687292 : CollatzResearch.WordTrace tailWord_687292 prefixEnd_687292 78424699108895600130935 := by
  unfold tailWord_687292
  simp only [CollatzResearch.WordTrace]
  refine ⟨12533799313032969486800065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16711732417377292649066753 12533799313032969486800065)
  ·
    refine ⟨9400349484774727115100049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12533799313032969486800065 9400349484774727115100049)
    ·
      refine ⟨7050262113581045336325037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9400349484774727115100049 7050262113581045336325037)
      ·
        refine ⟨2643848292592892001121889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7050262113581045336325037 2643848292592892001121889)
        ·
          refine ⟨1982886219444669000841417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2643848292592892001121889 1982886219444669000841417)
          ·
            refine ⟨1487164664583501750631063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1982886219444669000841417 1487164664583501750631063)
            ·
              refine ⟨2230746996875252625946595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1487164664583501750631063 2230746996875252625946595)
              ·
                refine ⟨3346120495312878938919893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2230746996875252625946595 3346120495312878938919893)
                ·
                  refine ⟨78424699108895600130935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3346120495312878938919893 78424699108895600130935)
                  ·
                    rfl

theorem cell22_687292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_687292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687292 prefixEnd_687292 := by exact prefixLift 687292
  have htrace : WordTrace (prefixWord ++ tailWord_687292) baseStart_687292 baseEnd_687292 := by
    simpa [prefixWord, tailWord_687292, baseEnd_687292] using wordTrace_append hprefix tailTrace_687292
  have hstable : (prefixWord ++ tailWord_687292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687292).length < 2 ^ (prefixWord ++ tailWord_687292).sum := by decide
  have hdescent : baseEnd_687292 < baseStart_687292 := by decide
  rcases family_descends (prefixWord ++ tailWord_687292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687302 : List Nat := [6, 1, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_687302 : Nat := 118140960795 + 687302 * 2 ^ 59
def prefixEnd_687302 : Nat := 4983230072969 + 3 ^ 40 * 687302 * 2
def baseEnd_687302 : Nat := 235277520531050107642775

theorem tailTrace_687302 : CollatzResearch.WordTrace tailWord_687302 prefixEnd_687302 235277520531050107642775 := by
  unfold tailWord_687302
  simp only [CollatzResearch.WordTrace]
  refine ⟨783373854875928458795755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16711975570686473787642773 783373854875928458795755)
  ·
    refine ⟨1175060782313892688193633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 783373854875928458795755 1175060782313892688193633)
    ·
      refine ⟨881295586735419516145225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1175060782313892688193633 881295586735419516145225)
      ·
        refine ⟨660971690051564637108919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 881295586735419516145225 660971690051564637108919)
        ·
          refine ⟨991457535077346955663379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660971690051564637108919 991457535077346955663379)
          ·
            refine ⟨1487186302616020433495069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 991457535077346955663379 1487186302616020433495069)
            ·
              refine ⟨557694863481007662560651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1487186302616020433495069 557694863481007662560651)
              ·
                refine ⟨836542295221511493840977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557694863481007662560651 836542295221511493840977)
                ·
                  refine ⟨627406721416133620380733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 836542295221511493840977 627406721416133620380733)
                  ·
                    refine ⟨235277520531050107642775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 627406721416133620380733 235277520531050107642775)
                    ·
                      rfl

theorem cell22_687302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_687302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687302 prefixEnd_687302 := by exact prefixLift 687302
  have htrace : WordTrace (prefixWord ++ tailWord_687302) baseStart_687302 baseEnd_687302 := by
    simpa [prefixWord, tailWord_687302, baseEnd_687302] using wordTrace_append hprefix tailTrace_687302
  have hstable : (prefixWord ++ tailWord_687302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687302).length < 2 ^ (prefixWord ++ tailWord_687302).sum := by decide
  have hdescent : baseEnd_687302 < baseStart_687302 := by decide
  rcases family_descends (prefixWord ++ tailWord_687302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687369 : List Nat := [1, 2, 1, 1, 3, 3, 3, 3, 2, 3]
def baseStart_687369 : Nat := 118140960795 + 687369 * 2 ^ 59
def prefixEnd_687369 : Nat := 4983230072969 + 3 ^ 40 * 687369 * 2
def baseEnd_687369 : Nat := 235300456000284266217569

theorem tailTrace_687369 : CollatzResearch.WordTrace tailWord_687369 prefixEnd_687369 235300456000284266217569 := by
  unfold tailWord_687369
  simp only [CollatzResearch.WordTrace]
  refine ⟨25070407046786981124153161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16713604697857987416102107 25070407046786981124153161)
  ·
    refine ⟨18802805285090235843114871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25070407046786981124153161 18802805285090235843114871)
    ·
      refine ⟨28204207927635353764672307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18802805285090235843114871 28204207927635353764672307)
      ·
        refine ⟨42306311891453030647008461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28204207927635353764672307 42306311891453030647008461)
        ·
          refine ⟨15864866959294886492628173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42306311891453030647008461 15864866959294886492628173)
          ·
            refine ⟨5949325109735582434735565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15864866959294886492628173 5949325109735582434735565)
            ·
              refine ⟨2230996916150843413025837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5949325109735582434735565 2230996916150843413025837)
              ·
                refine ⟨836623843556566279884689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2230996916150843413025837 836623843556566279884689)
                ·
                  refine ⟨627467882667424709913517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 836623843556566279884689 627467882667424709913517)
                  ·
                    refine ⟨235300456000284266217569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 627467882667424709913517 235300456000284266217569)
                    ·
                      rfl

theorem cell22_687369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 3].length) (baseStart_687369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687369 prefixEnd_687369 := by exact prefixLift 687369
  have htrace : WordTrace (prefixWord ++ tailWord_687369) baseStart_687369 baseEnd_687369 := by
    simpa [prefixWord, tailWord_687369, baseEnd_687369] using wordTrace_append hprefix tailTrace_687369
  have hstable : (prefixWord ++ tailWord_687369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687369).length < 2 ^ (prefixWord ++ tailWord_687369).sum := by decide
  have hdescent : baseEnd_687369 < baseStart_687369 := by decide
  rcases family_descends (prefixWord ++ tailWord_687369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687384 : List Nat := [2, 1, 2, 3, 1, 4, 2, 1, 2, 4]
def baseStart_687384 : Nat := 118140960795 + 687384 * 2 ^ 59
def prefixEnd_687384 : Nat := 4983230072969 + 3 ^ 40 * 687384 * 2
def baseEnd_687384 : Nat := 235305590806829227092523

theorem tailTrace_687384 : CollatzResearch.WordTrace tailWord_687384 prefixEnd_687384 235305590806829227092523 := by
  unfold tailWord_687384
  simp only [CollatzResearch.WordTrace]
  refine ⟨12535477070866319342974603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16713969427821759123966137 12535477070866319342974603)
  ·
    refine ⟨18803215606299479014461905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12535477070866319342974603 18803215606299479014461905)
    ·
      refine ⟨14102411704724609260846429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18803215606299479014461905 14102411704724609260846429)
      ·
        refine ⟨5288404389271728472817411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14102411704724609260846429 5288404389271728472817411)
        ·
          refine ⟨7932606583907592709226117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5288404389271728472817411 7932606583907592709226117)
          ·
            refine ⟨1487363734482673632979897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7932606583907592709226117 1487363734482673632979897)
            ·
              refine ⟨1115522800862005224734923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1487363734482673632979897 1115522800862005224734923)
              ·
                refine ⟨1673284201293007837102385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1115522800862005224734923 1673284201293007837102385)
                ·
                  refine ⟨1254963150969755877826789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1673284201293007837102385 1254963150969755877826789)
                  ·
                    refine ⟨235305590806829227092523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1254963150969755877826789 235305590806829227092523)
                    ·
                      rfl

theorem cell22_687384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_687384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687384 prefixEnd_687384 := by exact prefixLift 687384
  have htrace : WordTrace (prefixWord ++ tailWord_687384) baseStart_687384 baseEnd_687384 := by
    simpa [prefixWord, tailWord_687384, baseEnd_687384] using wordTrace_append hprefix tailTrace_687384
  have hstable : (prefixWord ++ tailWord_687384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687384).length < 2 ^ (prefixWord ++ tailWord_687384).sum := by decide
  have hdescent : baseEnd_687384 < baseStart_687384 := by decide
  rcases family_descends (prefixWord ++ tailWord_687384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687390 : List Nat := [4, 3, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_687390 : Nat := 118140960795 + 687390 * 2 ^ 59
def prefixEnd_687390 : Nat := 4983230072969 + 3 ^ 40 * 687390 * 2
def baseEnd_687390 : Nat := 235307644729447211442505

theorem tailTrace_687390 : CollatzResearch.WordTrace tailWord_687390 prefixEnd_687390 235307644729447211442505 := by
  unfold tailWord_687390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3133896622463862713833453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16714115319807267807111749 3133896622463862713833453)
  ·
    refine ⟨1175211233423948517687545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3133896622463862713833453 1175211233423948517687545)
    ·
      refine ⟨881408425067961388265659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1175211233423948517687545 881408425067961388265659)
      ·
        refine ⟨1322112637601942082398489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 881408425067961388265659 1322112637601942082398489)
        ·
          refine ⟨991584478201456561798867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1322112637601942082398489 991584478201456561798867)
          ·
            refine ⟨1487376717302184842698301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 991584478201456561798867 1487376717302184842698301)
            ·
              refine ⟨557766268988319316011863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1487376717302184842698301 557766268988319316011863)
              ·
                refine ⟨836649403482478974017795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557766268988319316011863 836649403482478974017795)
                ·
                  refine ⟨1254974105223718461026693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 836649403482478974017795 1254974105223718461026693)
                  ·
                    refine ⟨235307644729447211442505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1254974105223718461026693 235307644729447211442505)
                    ·
                      rfl

theorem cell22_687390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_687390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687390 prefixEnd_687390 := by exact prefixLift 687390
  have htrace : WordTrace (prefixWord ++ tailWord_687390) baseStart_687390 baseEnd_687390 := by
    simpa [prefixWord, tailWord_687390, baseEnd_687390] using wordTrace_append hprefix tailTrace_687390
  have hstable : (prefixWord ++ tailWord_687390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687390).length < 2 ^ (prefixWord ++ tailWord_687390).sum := by decide
  have hdescent : baseEnd_687390 < baseStart_687390 := by decide
  rcases family_descends (prefixWord ++ tailWord_687390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687405 : List Nat := [1, 5, 3, 1, 1, 3, 2, 2, 4]
def baseStart_687405 : Nat := 118140960795 + 687405 * 2 ^ 59
def prefixEnd_687405 : Nat := 4983230072969 + 3 ^ 40 * 687405 * 2
def baseEnd_687405 : Nat := 78437593178664057439153

theorem tailTrace_687405 : CollatzResearch.WordTrace tailWord_687405 prefixEnd_687405 78437593178664057439153 := by
  unfold tailWord_687405
  simp only [CollatzResearch.WordTrace]
  refine ⟨25071720074656559272463669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16714480049771039514975779 25071720074656559272463669)
  ·
    refine ⟨2350473756999052431793469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25071720074656559272463669 2350473756999052431793469)
    ·
      refine ⟨881427658874644661922551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2350473756999052431793469 881427658874644661922551)
      ·
        refine ⟨1322141488311966992883827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 881427658874644661922551 1322141488311966992883827)
        ·
          refine ⟨1983212232467950489325741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1322141488311966992883827 1983212232467950489325741)
          ·
            refine ⟨743704587175481433497153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1983212232467950489325741 743704587175481433497153)
            ·
              refine ⟨557778440381611075122865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743704587175481433497153 557778440381611075122865)
              ·
                refine ⟨418333830286208306342149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557778440381611075122865 418333830286208306342149)
                ·
                  refine ⟨78437593178664057439153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 418333830286208306342149 78437593178664057439153)
                  ·
                    rfl

theorem cell22_687405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_687405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687405 prefixEnd_687405 := by exact prefixLift 687405
  have htrace : WordTrace (prefixWord ++ tailWord_687405) baseStart_687405 baseEnd_687405 := by
    simpa [prefixWord, tailWord_687405, baseEnd_687405] using wordTrace_append hprefix tailTrace_687405
  have hstable : (prefixWord ++ tailWord_687405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687405).length < 2 ^ (prefixWord ++ tailWord_687405).sum := by decide
  have hdescent : baseEnd_687405 < baseStart_687405 := by decide
  rcases family_descends (prefixWord ++ tailWord_687405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687442 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_687442 : Nat := 118140960795 + 687442 * 2 ^ 59
def prefixEnd_687442 : Nat := 4983230072969 + 3 ^ 40 * 687442 * 2
def baseEnd_687442 : Nat := 235325445392136409142345

theorem tailTrace_687442 : CollatzResearch.WordTrace tailWord_687442 prefixEnd_687442 235325445392136409142345 := by
  unfold tailWord_687442
  simp only [CollatzResearch.WordTrace]
  refine ⟨6268267393880628647890145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16715379717015009727707053 6268267393880628647890145)
  ·
    refine ⟨4701200545410471485917609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6268267393880628647890145 4701200545410471485917609)
    ·
      refine ⟨3525900409057853614438207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4701200545410471485917609 3525900409057853614438207)
      ·
        refine ⟨5288850613586780421657311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3525900409057853614438207 5288850613586780421657311)
        ·
          refine ⟨7933275920380170632485967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5288850613586780421657311 7933275920380170632485967)
          ·
            refine ⟨11899913880570255948728951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7933275920380170632485967 11899913880570255948728951)
            ·
              refine ⟨17849870820855383923093427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11899913880570255948728951 17849870820855383923093427)
              ·
                refine ⟨26774806231283075884640141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17849870820855383923093427 26774806231283075884640141)
                ·
                  refine ⟨10040552336731153456740053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26774806231283075884640141 10040552336731153456740053)
                  ·
                    refine ⟨235325445392136409142345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10040552336731153456740053 235325445392136409142345)
                    ·
                      rfl

theorem cell22_687442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_687442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687442 prefixEnd_687442 := by exact prefixLift 687442
  have htrace : WordTrace (prefixWord ++ tailWord_687442) baseStart_687442 baseEnd_687442 := by
    simpa [prefixWord, tailWord_687442, baseEnd_687442] using wordTrace_append hprefix tailTrace_687442
  have hstable : (prefixWord ++ tailWord_687442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687442).length < 2 ^ (prefixWord ++ tailWord_687442).sum := by decide
  have hdescent : baseEnd_687442 < baseStart_687442 := by decide
  rcases family_descends (prefixWord ++ tailWord_687442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687491 : List Nat := [1, 1, 1, 3, 5, 2, 2, 2, 1, 4]
def baseStart_687491 : Nat := 118140960795 + 687491 * 2 ^ 59
def prefixEnd_687491 : Nat := 4983230072969 + 3 ^ 40 * 687491 * 2
def baseEnd_687491 : Nat := 235342219093516614667195

theorem tailTrace_687491 : CollatzResearch.WordTrace tailWord_687491 prefixEnd_687491 235342219093516614667195 := by
  unfold tailWord_687491
  simp only [CollatzResearch.WordTrace]
  refine ⟨25074856752344995960094327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16716571168229997306729551 25074856752344995960094327)
  ·
    refine ⟨37612285128517493940141491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25074856752344995960094327 37612285128517493940141491)
    ·
      refine ⟨56418427692776240910212237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37612285128517493940141491 56418427692776240910212237)
      ·
        refine ⟨21156910384791090341329589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56418427692776240910212237 21156910384791090341329589)
        ·
          refine ⟨1983460348574164719499649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21156910384791090341329589 1983460348574164719499649)
          ·
            refine ⟨1487595261430623539624737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1983460348574164719499649 1487595261430623539624737)
            ·
              refine ⟨1115696446072967654718553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1487595261430623539624737 1115696446072967654718553)
              ·
                refine ⟨836772334554725741038915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1115696446072967654718553 836772334554725741038915)
                ·
                  refine ⟨1255158501832088611558373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 836772334554725741038915 1255158501832088611558373)
                  ·
                    refine ⟨235342219093516614667195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1255158501832088611558373 235342219093516614667195)
                    ·
                      rfl

theorem cell22_687491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 4].length) (baseStart_687491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687491 prefixEnd_687491 := by exact prefixLift 687491
  have htrace : WordTrace (prefixWord ++ tailWord_687491) baseStart_687491 baseEnd_687491 := by
    simpa [prefixWord, tailWord_687491, baseEnd_687491] using wordTrace_append hprefix tailTrace_687491
  have hstable : (prefixWord ++ tailWord_687491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687491).length < 2 ^ (prefixWord ++ tailWord_687491).sum := by decide
  have hdescent : baseEnd_687491 < baseStart_687491 := by decide
  rcases family_descends (prefixWord ++ tailWord_687491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687519 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 4, 4]
def baseStart_687519 : Nat := 118140960795 + 687519 * 2 ^ 59
def prefixEnd_687519 : Nat := 4983230072969 + 3 ^ 40 * 687519 * 2
def baseEnd_687519 : Nat := 235351804065733874967109

theorem tailTrace_687519 : CollatzResearch.WordTrace tailWord_687519 prefixEnd_687519 235351804065733874967109 := by
  unfold tailWord_687519
  simp only [CollatzResearch.WordTrace]
  refine ⟨25075877996243556742113611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16717251997495704494742407 25075877996243556742113611)
  ·
    refine ⟨37613816994365335113170417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25075877996243556742113611 37613816994365335113170417)
    ·
      refine ⟨28210362745774001334877813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37613816994365335113170417 28210362745774001334877813)
      ·
        refine ⟨2644721507416312625144795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28210362745774001334877813 2644721507416312625144795)
        ·
          refine ⟨3967082261124468937717193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2644721507416312625144795 3967082261124468937717193)
          ·
            refine ⟨2975311695843351703287895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3967082261124468937717193 2975311695843351703287895)
            ·
              refine ⟨4462967543765027554931843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2975311695843351703287895 4462967543765027554931843)
              ·
                refine ⟨6694451315647541332397765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4462967543765027554931843 6694451315647541332397765)
                ·
                  refine ⟨1255209621683913999824581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6694451315647541332397765 1255209621683913999824581)
                  ·
                    refine ⟨235351804065733874967109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1255209621683913999824581 235351804065733874967109)
                    ·
                      rfl

theorem cell22_687519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 4].length) (baseStart_687519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687519 prefixEnd_687519 := by exact prefixLift 687519
  have htrace : WordTrace (prefixWord ++ tailWord_687519) baseStart_687519 baseEnd_687519 := by
    simpa [prefixWord, tailWord_687519, baseEnd_687519] using wordTrace_append hprefix tailTrace_687519
  have hstable : (prefixWord ++ tailWord_687519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687519).length < 2 ^ (prefixWord ++ tailWord_687519).sum := by decide
  have hdescent : baseEnd_687519 < baseStart_687519 := by decide
  rcases family_descends (prefixWord ++ tailWord_687519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687583 : List Nat := [1, 1, 2, 3, 3, 1, 3, 4, 1, 3]
def baseStart_687583 : Nat := 118140960795 + 687583 * 2 ^ 59
def prefixEnd_687583 : Nat := 4983230072969 + 3 ^ 40 * 687583 * 2
def baseEnd_687583 : Nat := 235373712573659041366913

theorem tailTrace_687583 : CollatzResearch.WordTrace tailWord_687583 prefixEnd_687583 235373712573659041366913 := by
  unfold tailWord_687583
  simp only [CollatzResearch.WordTrace]
  refine ⟨25078212268011695672443403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16718808178674463781628935 25078212268011695672443403)
  ·
    refine ⟨37617318402017543508665105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25078212268011695672443403 37617318402017543508665105)
    ·
      refine ⟨28212988801513157631498829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37617318402017543508665105 28212988801513157631498829)
      ·
        refine ⟨10579870800567434111812061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28212988801513157631498829 10579870800567434111812061)
        ·
          refine ⟨3967451550212787791929523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10579870800567434111812061 3967451550212787791929523)
          ·
            refine ⟨5951177325319181687894285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3967451550212787791929523 5951177325319181687894285)
            ·
              refine ⟨2231691496994693132960357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5951177325319181687894285 2231691496994693132960357)
              ·
                refine ⟨418442155686504962430067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2231691496994693132960357 418442155686504962430067)
                ·
                  refine ⟨627663233529757443645101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 418442155686504962430067 627663233529757443645101)
                  ·
                    refine ⟨235373712573659041366913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 627663233529757443645101 235373712573659041366913)
                    ·
                      rfl

theorem cell22_687583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 1, 3].length) (baseStart_687583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687583 prefixEnd_687583 := by exact prefixLift 687583
  have htrace : WordTrace (prefixWord ++ tailWord_687583) baseStart_687583 baseEnd_687583 := by
    simpa [prefixWord, tailWord_687583, baseEnd_687583] using wordTrace_append hprefix tailTrace_687583
  have hstable : (prefixWord ++ tailWord_687583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687583).length < 2 ^ (prefixWord ++ tailWord_687583).sum := by decide
  have hdescent : baseEnd_687583 < baseStart_687583 := by decide
  rcases family_descends (prefixWord ++ tailWord_687583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687630 : List Nat := [4, 1, 1, 2, 5, 1, 1, 2, 5]
def baseStart_687630 : Nat := 118140960795 + 687630 * 2 ^ 59
def prefixEnd_687630 : Nat := 4983230072969 + 3 ^ 40 * 687630 * 2
def baseEnd_687630 : Nat := 78463267211388861813923

theorem tailTrace_687630 : CollatzResearch.WordTrace tailWord_687630 prefixEnd_687630 78463267211388861813923 := by
  unfold tailWord_687630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3134990812355177837425543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16719950999227615132936229 3134990812355177837425543)
  ·
    refine ⟨4702486218532766756138315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3134990812355177837425543 4702486218532766756138315)
    ·
      refine ⟨7053729327799150134207473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4702486218532766756138315 7053729327799150134207473)
      ·
        refine ⟨5290296995849362600655605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7053729327799150134207473 5290296995849362600655605)
        ·
          refine ⟨495965343360877743811463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5290296995849362600655605 495965343360877743811463)
          ·
            refine ⟨743948015041316615717195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495965343360877743811463 743948015041316615717195)
            ·
              refine ⟨1115922022561974923575793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743948015041316615717195 1115922022561974923575793)
              ·
                refine ⟨836941516921481192681845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1115922022561974923575793 836941516921481192681845)
                ·
                  refine ⟨78463267211388861813923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 836941516921481192681845 78463267211388861813923)
                  ·
                    rfl

theorem cell22_687630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_687630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687630 prefixEnd_687630 := by exact prefixLift 687630
  have htrace : WordTrace (prefixWord ++ tailWord_687630) baseStart_687630 baseEnd_687630 := by
    simpa [prefixWord, tailWord_687630, baseEnd_687630] using wordTrace_append hprefix tailTrace_687630
  have hstable : (prefixWord ++ tailWord_687630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687630).length < 2 ^ (prefixWord ++ tailWord_687630).sum := by decide
  have hdescent : baseEnd_687630 < baseStart_687630 := by decide
  rcases family_descends (prefixWord ++ tailWord_687630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687776 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 8]
def baseStart_687776 : Nat := 118140960795 + 687776 * 2 ^ 59
def prefixEnd_687776 : Nat := 4983230072969 + 3 ^ 40 * 687776 * 2
def baseEnd_687776 : Nat := 78479926805956957097107

theorem tailTrace_687776 : CollatzResearch.WordTrace tailWord_687776 prefixEnd_687776 78479926805956957097107 := by
  unfold tailWord_687776
  simp only [CollatzResearch.WordTrace]
  refine ⟨12542625778156244817109591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16723501037541659756146121 12542625778156244817109591)
  ·
    refine ⟨18813938667234367225664387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12542625778156244817109591 18813938667234367225664387)
    ·
      refine ⟨28220908000851550838496581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18813938667234367225664387 28220908000851550838496581)
      ·
        refine ⟨5291420250159665782218109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28220908000851550838496581 5291420250159665782218109)
        ·
          refine ⟨1984282593809874668331791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5291420250159665782218109 1984282593809874668331791)
          ·
            refine ⟨2976423890714812002497687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1984282593809874668331791 2976423890714812002497687)
            ·
              refine ⟨4464635836072218003746531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2976423890714812002497687 4464635836072218003746531)
              ·
                refine ⟨6696953754108327005619797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4464635836072218003746531 6696953754108327005619797)
                ·
                  refine ⟨78479926805956957097107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6696953754108327005619797 78479926805956957097107)
                  ·
                    rfl

theorem cell22_687776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 8].length) (baseStart_687776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687776 prefixEnd_687776 := by exact prefixLift 687776
  have htrace : WordTrace (prefixWord ++ tailWord_687776) baseStart_687776 baseEnd_687776 := by
    simpa [prefixWord, tailWord_687776, baseEnd_687776] using wordTrace_append hprefix tailTrace_687776
  have hstable : (prefixWord ++ tailWord_687776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687776).length < 2 ^ (prefixWord ++ tailWord_687776).sum := by decide
  have hdescent : baseEnd_687776 < baseStart_687776 := by decide
  rcases family_descends (prefixWord ++ tailWord_687776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687791 : List Nat := [1, 1, 2, 1, 2, 4, 1, 4, 1, 5]
def baseStart_687791 : Nat := 118140960795 + 687791 * 2 ^ 59
def prefixEnd_687791 : Nat := 4983230072969 + 3 ^ 40 * 687791 * 2
def baseEnd_687791 : Nat := 235444915224415832166275

theorem tailTrace_687791 : CollatzResearch.WordTrace tailWord_687791 prefixEnd_687791 235444915224415832166275 := by
  unfold tailWord_687791
  simp only [CollatzResearch.WordTrace]
  refine ⟨25085798651258147196015227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16723865767505431464010151 25085798651258147196015227)
  ·
    refine ⟨37628697976887220794022841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25085798651258147196015227 37628697976887220794022841)
    ·
      refine ⟨28221523482665415595517131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37628697976887220794022841 28221523482665415595517131)
      ·
        refine ⟨42332285223998123393275697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28221523482665415595517131 42332285223998123393275697)
        ·
          refine ⟨31749213917998592544956773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42332285223998123393275697 31749213917998592544956773)
          ·
            refine ⟨5952977609624736102179395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31749213917998592544956773 5952977609624736102179395)
            ·
              refine ⟨8929466414437104153269093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5952977609624736102179395 8929466414437104153269093)
              ·
                refine ⟨1674274952706957028737955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8929466414437104153269093 1674274952706957028737955)
                ·
                  refine ⟨2511412429060435543106933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1674274952706957028737955 2511412429060435543106933)
                  ·
                    refine ⟨235444915224415832166275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2511412429060435543106933 235444915224415832166275)
                    ·
                      rfl

theorem cell22_687791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 5].length) (baseStart_687791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687791 prefixEnd_687791 := by exact prefixLift 687791
  have htrace : WordTrace (prefixWord ++ tailWord_687791) baseStart_687791 baseEnd_687791 := by
    simpa [prefixWord, tailWord_687791, baseEnd_687791] using wordTrace_append hprefix tailTrace_687791
  have hstable : (prefixWord ++ tailWord_687791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687791).length < 2 ^ (prefixWord ++ tailWord_687791).sum := by decide
  have hdescent : baseEnd_687791 < baseStart_687791 := by decide
  rcases family_descends (prefixWord ++ tailWord_687791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687808 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 4, 3]
def baseStart_687808 : Nat := 118140960795 + 687808 * 2 ^ 59
def prefixEnd_687808 : Nat := 4983230072969 + 3 ^ 40 * 687808 * 2
def baseEnd_687808 : Nat := 235450734671833454491223

theorem tailTrace_687808 : CollatzResearch.WordTrace tailWord_687808 prefixEnd_687808 235450734671833454491223 := by
  unfold tailWord_687808
  simp only [CollatzResearch.WordTrace]
  refine ⟨12543209346098279549692039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16724279128131039399589385 12543209346098279549692039)
  ·
    refine ⟨18814814019147419324538059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12543209346098279549692039 18814814019147419324538059)
    ·
      refine ⟨28222221028721128986807089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18814814019147419324538059 28222221028721128986807089)
      ·
        refine ⟨21166665771540846740105317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28222221028721128986807089 21166665771540846740105317)
        ·
          refine ⟨3968749832163908763769747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21166665771540846740105317 3968749832163908763769747)
          ·
            refine ⟨5953124748245863145654621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3968749832163908763769747 5953124748245863145654621)
            ·
              refine ⟨2232421780592198679620483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5953124748245863145654621 2232421780592198679620483)
              ·
                refine ⟨3348632670888298019430725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2232421780592198679620483 3348632670888298019430725)
                ·
                  refine ⟨627868625791555878643261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3348632670888298019430725 627868625791555878643261)
                  ·
                    refine ⟨235450734671833454491223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 627868625791555878643261 235450734671833454491223)
                    ·
                      rfl

theorem cell22_687808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 4, 3].length) (baseStart_687808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687808 prefixEnd_687808 := by exact prefixLift 687808
  have htrace : WordTrace (prefixWord ++ tailWord_687808) baseStart_687808 baseEnd_687808 := by
    simpa [prefixWord, tailWord_687808, baseEnd_687808] using wordTrace_append hprefix tailTrace_687808
  have hstable : (prefixWord ++ tailWord_687808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687808).length < 2 ^ (prefixWord ++ tailWord_687808).sum := by decide
  have hdescent : baseEnd_687808 < baseStart_687808 := by decide
  rcases family_descends (prefixWord ++ tailWord_687808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687881 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 1, 7]
def baseStart_687881 : Nat := 118140960795 + 687881 * 2 ^ 59
def prefixEnd_687881 : Nat := 4983230072969 + 3 ^ 40 * 687881 * 2
def baseEnd_687881 : Nat := 235475724063685597415999

theorem tailTrace_687881 : CollatzResearch.WordTrace tailWord_687881 prefixEnd_687881 235475724063685597415999 := by
  unfold tailWord_687881
  simp only [CollatzResearch.WordTrace]
  refine ⟨25089081220932092566791497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16726054147288061711194331 25089081220932092566791497)
  ·
    refine ⟨18816810915699069425093623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25089081220932092566791497 18816810915699069425093623)
    ·
      refine ⟨28225216373548604137640435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18816810915699069425093623 28225216373548604137640435)
      ·
        refine ⟨42337824560322906206460653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28225216373548604137640435 42337824560322906206460653)
        ·
          refine ⟨15876684210121089827422745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42337824560322906206460653 15876684210121089827422745)
          ·
            refine ⟨11907513157590817370567059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15876684210121089827422745 11907513157590817370567059)
            ·
              refine ⟨17861269736386226055850589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11907513157590817370567059 17861269736386226055850589)
              ·
                refine ⟨6697976151144834770943971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17861269736386226055850589 6697976151144834770943971)
                ·
                  refine ⟨10046964226717252156415957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6697976151144834770943971 10046964226717252156415957)
                  ·
                    refine ⟨235475724063685597415999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10046964226717252156415957 235475724063685597415999)
                    ·
                      rfl

theorem cell22_687881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_687881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687881 prefixEnd_687881 := by exact prefixLift 687881
  have htrace : WordTrace (prefixWord ++ tailWord_687881) baseStart_687881 baseEnd_687881 := by
    simpa [prefixWord, tailWord_687881, baseEnd_687881] using wordTrace_append hprefix tailTrace_687881
  have hstable : (prefixWord ++ tailWord_687881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687881).length < 2 ^ (prefixWord ++ tailWord_687881).sum := by decide
  have hdescent : baseEnd_687881 < baseStart_687881 := by decide
  rcases family_descends (prefixWord ++ tailWord_687881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687943 : List Nat := [1, 1, 4, 1, 2, 1, 3, 3, 1, 5]
def baseStart_687943 : Nat := 118140960795 + 687943 * 2 ^ 59
def prefixEnd_687943 : Nat := 4983230072969 + 3 ^ 40 * 687943 * 2
def baseEnd_687943 : Nat := 235496947930738102365809

theorem tailTrace_687943 : CollatzResearch.WordTrace tailWord_687943 prefixEnd_687943 235496947930738102365809 := by
  unfold tailWord_687943
  simp only [CollatzResearch.WordTrace]
  refine ⟨25091342546707477155548483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16727561697804984770365655 25091342546707477155548483)
  ·
    refine ⟨37637013820061215733322725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25091342546707477155548483 37637013820061215733322725)
    ·
      refine ⟨7056940091261477949998011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37637013820061215733322725 7056940091261477949998011)
      ·
        refine ⟨10585410136892216924997017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7056940091261477949998011 10585410136892216924997017)
        ·
          refine ⟨7939057602669162693747763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10585410136892216924997017 7939057602669162693747763)
          ·
            refine ⟨11908586404003744040621645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7939057602669162693747763 11908586404003744040621645)
            ·
              refine ⟨4465719901501404015233117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11908586404003744040621645 4465719901501404015233117)
              ·
                refine ⟨1674644963063026505712419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4465719901501404015233117 1674644963063026505712419)
                ·
                  refine ⟨2511967444594539758568629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1674644963063026505712419 2511967444594539758568629)
                  ·
                    refine ⟨235496947930738102365809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2511967444594539758568629 235496947930738102365809)
                    ·
                      rfl

theorem cell22_687943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_687943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_687943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_687943 prefixEnd_687943 := by exact prefixLift 687943
  have htrace : WordTrace (prefixWord ++ tailWord_687943) baseStart_687943 baseEnd_687943 := by
    simpa [prefixWord, tailWord_687943, baseEnd_687943] using wordTrace_append hprefix tailTrace_687943
  have hstable : (prefixWord ++ tailWord_687943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687943).length < 2 ^ (prefixWord ++ tailWord_687943).sum := by decide
  have hdescent : baseEnd_687943 < baseStart_687943 := by decide
  rcases family_descends (prefixWord ++ tailWord_687943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688005 : List Nat := [1, 3, 1, 1, 3, 2, 1, 4, 3, 3]
def baseStart_688005 : Nat := 118140960795 + 688005 * 2 ^ 59
def prefixEnd_688005 : Nat := 4983230072969 + 3 ^ 40 * 688005 * 2
def baseEnd_688005 : Nat := 235518171797790607315619

theorem tailTrace_688005 : CollatzResearch.WordTrace tailWord_688005 prefixEnd_688005 235518171797790607315619 := by
  unfold tailWord_688005
  simp only [CollatzResearch.WordTrace]
  refine ⟨25093603872482861744305469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16729069248321907829536979 25093603872482861744305469)
  ·
    refine ⟨9410101452181073154114551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25093603872482861744305469 9410101452181073154114551)
    ·
      refine ⟨14115152178271609731171827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9410101452181073154114551 14115152178271609731171827)
      ·
        refine ⟨21172728267407414596757741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14115152178271609731171827 21172728267407414596757741)
        ·
          refine ⟨7939773100277780473784153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21172728267407414596757741 7939773100277780473784153)
          ·
            refine ⟨5954829825208335355338115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7939773100277780473784153 5954829825208335355338115)
            ·
              refine ⟨8932244737812503033007173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5954829825208335355338115 8932244737812503033007173)
              ·
                refine ⟨1674795888339844318688845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8932244737812503033007173 1674795888339844318688845)
                ·
                  refine ⟨628048458127441619508317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1674795888339844318688845 628048458127441619508317)
                  ·
                    refine ⟨235518171797790607315619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 628048458127441619508317 235518171797790607315619)
                    ·
                      rfl

theorem cell22_688005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_688005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688005 prefixEnd_688005 := by exact prefixLift 688005
  have htrace : WordTrace (prefixWord ++ tailWord_688005) baseStart_688005 baseEnd_688005 := by
    simpa [prefixWord, tailWord_688005, baseEnd_688005] using wordTrace_append hprefix tailTrace_688005
  have hstable : (prefixWord ++ tailWord_688005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688005).length < 2 ^ (prefixWord ++ tailWord_688005).sum := by decide
  have hdescent : baseEnd_688005 < baseStart_688005 := by decide
  rcases family_descends (prefixWord ++ tailWord_688005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688007 : List Nat := [1, 1, 4, 2, 4, 2, 2, 6]
def baseStart_688007 : Nat := 118140960795 + 688007 * 2 ^ 59
def prefixEnd_688007 : Nat := 4983230072969 + 3 ^ 40 * 688007 * 2
def baseEnd_688007 : Nat := 26168761826518140973957

theorem tailTrace_688007 : CollatzResearch.WordTrace tailWord_688007 prefixEnd_688007 26168761826518140973957 := by
  unfold tailWord_688007
  simp only [CollatzResearch.WordTrace]
  refine ⟨25093676818475616085878275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16729117878983744057252183 25093676818475616085878275)
  ·
    refine ⟨37640515227713424128817413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25093676818475616085878275 37640515227713424128817413)
    ·
      refine ⟨7057596605196267024153265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37640515227713424128817413 7057596605196267024153265)
      ·
        refine ⟨5293197453897200268114949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7057596605196267024153265 5293197453897200268114949)
        ·
          refine ⟨992474522605725050271553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5293197453897200268114949 992474522605725050271553)
          ·
            refine ⟨744355891954293787703665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 992474522605725050271553 744355891954293787703665)
            ·
              refine ⟨558266918965720340777749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 744355891954293787703665 558266918965720340777749)
              ·
                refine ⟨26168761826518140973957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 558266918965720340777749 26168761826518140973957)
                ·
                  rfl

theorem cell22_688007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 6].length) (baseStart_688007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688007 prefixEnd_688007 := by exact prefixLift 688007
  have htrace : WordTrace (prefixWord ++ tailWord_688007) baseStart_688007 baseEnd_688007 := by
    simpa [prefixWord, tailWord_688007, baseEnd_688007] using wordTrace_append hprefix tailTrace_688007
  have hstable : (prefixWord ++ tailWord_688007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688007).length < 2 ^ (prefixWord ++ tailWord_688007).sum := by decide
  have hdescent : baseEnd_688007 < baseStart_688007 := by decide
  rcases family_descends (prefixWord ++ tailWord_688007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688039 : List Nat := [1, 1, 6, 1, 2, 3, 1, 1, 3, 3]
def baseStart_688039 : Nat := 118140960795 + 688039 * 2 ^ 59
def prefixEnd_688039 : Nat := 4983230072969 + 3 ^ 40 * 688039 * 2
def baseEnd_688039 : Nat := 235529810692625851965515

theorem tailTrace_688039 : CollatzResearch.WordTrace tailWord_688039 prefixEnd_688039 235529810692625851965515 := by
  unfold tailWord_688039
  simp only [CollatzResearch.WordTrace]
  refine ⟨25094843954359685551043171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16729895969573123700695447 25094843954359685551043171)
  ·
    refine ⟨37642265931539528326564757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25094843954359685551043171 37642265931539528326564757)
    ·
      refine ⟨1764481215540915390307723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37642265931539528326564757 1764481215540915390307723)
      ·
        refine ⟨2646721823311373085461585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1764481215540915390307723 2646721823311373085461585)
        ·
          refine ⟨1985041367483529814096189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2646721823311373085461585 1985041367483529814096189)
          ·
            refine ⟨744390512806323680286071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1985041367483529814096189 744390512806323680286071)
            ·
              refine ⟨1116585769209485520429107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 744390512806323680286071 1116585769209485520429107)
              ·
                refine ⟨1674878653814228280643661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1116585769209485520429107 1674878653814228280643661)
                ·
                  refine ⟨628079495180335605241373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1674878653814228280643661 628079495180335605241373)
                  ·
                    refine ⟨235529810692625851965515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 628079495180335605241373 235529810692625851965515)
                    ·
                      rfl

theorem cell22_688039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_688039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688039 prefixEnd_688039 := by exact prefixLift 688039
  have htrace : WordTrace (prefixWord ++ tailWord_688039) baseStart_688039 baseEnd_688039 := by
    simpa [prefixWord, tailWord_688039, baseEnd_688039] using wordTrace_append hprefix tailTrace_688039
  have hstable : (prefixWord ++ tailWord_688039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688039).length < 2 ^ (prefixWord ++ tailWord_688039).sum := by decide
  have hdescent : baseEnd_688039 < baseStart_688039 := by decide
  rcases family_descends (prefixWord ++ tailWord_688039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688063 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 8]
def baseStart_688063 : Nat := 118140960795 + 688063 * 2 ^ 59
def prefixEnd_688063 : Nat := 4983230072969 + 3 ^ 40 * 688063 * 2
def baseEnd_688063 : Nat := 78512675461032596455147

theorem tailTrace_688063 : CollatzResearch.WordTrace tailWord_688063 prefixEnd_688063 78512675461032596455147 := by
  unfold tailWord_688063
  simp only [CollatzResearch.WordTrace]
  refine ⟨25095719306272737649916843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16730479537515158433277895 25095719306272737649916843)
  ·
    refine ⟨37643578959409106474875265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25095719306272737649916843 37643578959409106474875265)
    ·
      refine ⟨28232684219556829856156449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37643578959409106474875265 28232684219556829856156449)
      ·
        refine ⟨21174513164667622392117337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28232684219556829856156449 21174513164667622392117337)
        ·
          refine ⟨15880884873500716794088003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21174513164667622392117337 15880884873500716794088003)
          ·
            refine ⟨23821327310251075191132005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15880884873500716794088003 23821327310251075191132005)
            ·
              refine ⟨4466498870672076598337251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23821327310251075191132005 4466498870672076598337251)
              ·
                refine ⟨6699748306008114897505877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4466498870672076598337251 6699748306008114897505877)
                ·
                  refine ⟨78512675461032596455147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6699748306008114897505877 78512675461032596455147)
                  ·
                    rfl

theorem cell22_688063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 8].length) (baseStart_688063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688063 prefixEnd_688063 := by exact prefixLift 688063
  have htrace : WordTrace (prefixWord ++ tailWord_688063) baseStart_688063 baseEnd_688063 := by
    simpa [prefixWord, tailWord_688063, baseEnd_688063] using wordTrace_append hprefix tailTrace_688063
  have hstable : (prefixWord ++ tailWord_688063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688063).length < 2 ^ (prefixWord ++ tailWord_688063).sum := by decide
  have hdescent : baseEnd_688063 < baseStart_688063 := by decide
  rcases family_descends (prefixWord ++ tailWord_688063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688112 : List Nat := [2, 1, 1, 1, 3, 2, 4, 3, 2, 3]
def baseStart_688112 : Nat := 118140960795 + 688112 * 2 ^ 59
def prefixEnd_688112 : Nat := 4983230072969 + 3 ^ 40 * 688112 * 2
def baseEnd_688112 : Nat := 235554800084477994890291

theorem tailTrace_688112 : CollatzResearch.WordTrace tailWord_688112 prefixEnd_688112 235554800084477994890291 := by
  unfold tailWord_688112
  simp only [CollatzResearch.WordTrace]
  refine ⟨12548753241547609509225295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16731670988730146012300393 12548753241547609509225295)
  ·
    refine ⟨18823129862321414263837943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12548753241547609509225295 18823129862321414263837943)
    ·
      refine ⟨28234694793482121395756915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18823129862321414263837943 28234694793482121395756915)
      ·
        refine ⟨42352042190223182093635373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28234694793482121395756915 42352042190223182093635373)
        ·
          refine ⟨15882015821333693285113265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42352042190223182093635373 15882015821333693285113265)
          ·
            refine ⟨11911511866000269963834949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15882015821333693285113265 11911511866000269963834949)
            ·
              refine ⟨2233408474875050618219053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11911511866000269963834949 2233408474875050618219053)
              ·
                refine ⟨837528178078143981832145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2233408474875050618219053 837528178078143981832145)
                ·
                  refine ⟨628146133558607986374109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 837528178078143981832145 628146133558607986374109)
                  ·
                    refine ⟨235554800084477994890291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 628146133558607986374109 235554800084477994890291)
                    ·
                      rfl

theorem cell22_688112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 2, 3].length) (baseStart_688112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688112 prefixEnd_688112 := by exact prefixLift 688112
  have htrace : WordTrace (prefixWord ++ tailWord_688112) baseStart_688112 baseEnd_688112 := by
    simpa [prefixWord, tailWord_688112, baseEnd_688112] using wordTrace_append hprefix tailTrace_688112
  have hstable : (prefixWord ++ tailWord_688112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688112).length < 2 ^ (prefixWord ++ tailWord_688112).sum := by decide
  have hdescent : baseEnd_688112 < baseStart_688112 := by decide
  rcases family_descends (prefixWord ++ tailWord_688112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688174 : List Nat := [4, 1, 3, 1, 1, 2, 2, 2, 3, 3]
def baseStart_688174 : Nat := 118140960795 + 688174 * 2 ^ 59
def prefixEnd_688174 : Nat := 4983230072969 + 3 ^ 40 * 688174 * 2
def baseEnd_688174 : Nat := 235576023951530499840101

theorem tailTrace_688174 : CollatzResearch.WordTrace tailWord_688174 prefixEnd_688174 235576023951530499840101 := by
  unfold tailWord_688174
  simp only [CollatzResearch.WordTrace]
  refine ⟨3137470976108825450900947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16733178539247069071471717 3137470976108825450900947)
  ·
    refine ⟨4706206464163238176351421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3137470976108825450900947 4706206464163238176351421)
    ·
      refine ⟨1764827424061214316131783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4706206464163238176351421 1764827424061214316131783)
      ·
        refine ⟨2647241136091821474197675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1764827424061214316131783 2647241136091821474197675)
        ·
          refine ⟨3970861704137732211296513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2647241136091821474197675 3970861704137732211296513)
          ·
            refine ⟨2978146278103299158472385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3970861704137732211296513 2978146278103299158472385)
            ·
              refine ⟨2233609708577474368854289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2978146278103299158472385 2233609708577474368854289)
              ·
                refine ⟨1675207281433105776640717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2233609708577474368854289 1675207281433105776640717)
                ·
                  refine ⟨628202730537414666240269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1675207281433105776640717 628202730537414666240269)
                  ·
                    refine ⟨235576023951530499840101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 628202730537414666240269 235576023951530499840101)
                    ·
                      rfl

theorem cell22_688174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_688174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688174 prefixEnd_688174 := by exact prefixLift 688174
  have htrace : WordTrace (prefixWord ++ tailWord_688174) baseStart_688174 baseEnd_688174 := by
    simpa [prefixWord, tailWord_688174, baseEnd_688174] using wordTrace_append hprefix tailTrace_688174
  have hstable : (prefixWord ++ tailWord_688174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688174).length < 2 ^ (prefixWord ++ tailWord_688174).sum := by decide
  have hdescent : baseEnd_688174 < baseStart_688174 := by decide
  rcases family_descends (prefixWord ++ tailWord_688174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688221 : List Nat := [1, 4, 4, 1, 1, 1, 4, 1, 5]
def baseStart_688221 : Nat := 118140960795 + 688221 * 2 ^ 59
def prefixEnd_688221 : Nat := 4983230072969 + 3 ^ 40 * 688221 * 2
def baseEnd_688221 : Nat := 78530704337346014638319

theorem tailTrace_688221 : CollatzResearch.WordTrace tailWord_688221 prefixEnd_688221 78530704337346014638319 := by
  unfold tailWord_688221
  simp only [CollatzResearch.WordTrace]
  refine ⟨25101482039700330634168517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16734321359800220422779011 25101482039700330634168517)
  ·
    refine ⟨4706527882443811993906597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25101482039700330634168517 4706527882443811993906597)
    ·
      refine ⟨882473977958214748857487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4706527882443811993906597 882473977958214748857487)
      ·
        refine ⟨1323710966937322123286231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 882473977958214748857487 1323710966937322123286231)
        ·
          refine ⟨1985566450405983184929347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1323710966937322123286231 1985566450405983184929347)
          ·
            refine ⟨2978349675608974777394021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1985566450405983184929347 2978349675608974777394021)
            ·
              refine ⟨558440564176682770761379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2978349675608974777394021 558440564176682770761379)
              ·
                refine ⟨837660846265024156142069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 558440564176682770761379 837660846265024156142069)
                ·
                  refine ⟨78530704337346014638319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 837660846265024156142069 78530704337346014638319)
                  ·
                    rfl

theorem cell22_688221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_688221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688221 prefixEnd_688221 := by exact prefixLift 688221
  have htrace : WordTrace (prefixWord ++ tailWord_688221) baseStart_688221 baseEnd_688221 := by
    simpa [prefixWord, tailWord_688221, baseEnd_688221] using wordTrace_append hprefix tailTrace_688221
  have hstable : (prefixWord ++ tailWord_688221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688221).length < 2 ^ (prefixWord ++ tailWord_688221).sum := by decide
  have hdescent : baseEnd_688221 < baseStart_688221 := by decide
  rcases family_descends (prefixWord ++ tailWord_688221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688234 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 3, 4]
def baseStart_688234 : Nat := 118140960795 + 688234 * 2 ^ 59
def prefixEnd_688234 : Nat := 4983230072969 + 3 ^ 40 * 688234 * 2
def baseEnd_688234 : Nat := 235596563177710343339917

theorem tailTrace_688234 : CollatzResearch.WordTrace tailWord_688234 prefixEnd_688234 235596563177710343339917 := by
  unfold tailWord_688234
  simp only [CollatzResearch.WordTrace]
  refine ⟨6275489047163308463597939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16734637459102155902927837 6275489047163308463597939)
  ·
    refine ⟨9413233570744962695396909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6275489047163308463597939 9413233570744962695396909)
    ·
      refine ⟨3529962589029361010773841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9413233570744962695396909 3529962589029361010773841)
      ·
        refine ⟨2647471941772020758080381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3529962589029361010773841 2647471941772020758080381)
        ·
          refine ⟨992801978164507784280143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2647471941772020758080381 992801978164507784280143)
          ·
            refine ⟨1489202967246761676420215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 992801978164507784280143 1489202967246761676420215)
            ·
              refine ⟨2233804450870142514630323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1489202967246761676420215 2233804450870142514630323)
              ·
                refine ⟨3350706676305213771945485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2233804450870142514630323 3350706676305213771945485)
                ·
                  refine ⟨1256515003614455164479557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3350706676305213771945485 1256515003614455164479557)
                  ·
                    refine ⟨235596563177710343339917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1256515003614455164479557 235596563177710343339917)
                    ·
                      rfl

theorem cell22_688234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_688234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688234 prefixEnd_688234 := by exact prefixLift 688234
  have htrace : WordTrace (prefixWord ++ tailWord_688234) baseStart_688234 baseEnd_688234 := by
    simpa [prefixWord, tailWord_688234, baseEnd_688234] using wordTrace_append hprefix tailTrace_688234
  have hstable : (prefixWord ++ tailWord_688234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688234).length < 2 ^ (prefixWord ++ tailWord_688234).sum := by decide
  have hdescent : baseEnd_688234 < baseStart_688234 := by decide
  rcases family_descends (prefixWord ++ tailWord_688234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688247 : List Nat := [1, 1, 3, 1, 1, 6, 1, 2, 1, 5]
def baseStart_688247 : Nat := 118140960795 + 688247 * 2 ^ 59
def prefixEnd_688247 : Nat := 4983230072969 + 3 ^ 40 * 688247 * 2
def baseEnd_688247 : Nat := 235601013343382642764877

theorem tailTrace_688247 : CollatzResearch.WordTrace tailWord_688247 prefixEnd_688247 235601013343382642764877 := by
  unfold tailWord_688247
  simp only [CollatzResearch.WordTrace]
  refine ⟨25102430337606137074614995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16734953558404091383076663 25102430337606137074614995)
  ·
    refine ⟨37653645506409205611922493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25102430337606137074614995 37653645506409205611922493)
    ·
      refine ⟨14120117064903452104470935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37653645506409205611922493 14120117064903452104470935)
      ·
        refine ⟨21180175597355178156706403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14120117064903452104470935 21180175597355178156706403)
        ·
          refine ⟨31770263396032767235059605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21180175597355178156706403 31770263396032767235059605)
          ·
            refine ⟨1489231096689035964143419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31770263396032767235059605 1489231096689035964143419)
            ·
              refine ⟨2233846645033553946215129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1489231096689035964143419 2233846645033553946215129)
              ·
                refine ⟨1675384983775165459661347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2233846645033553946215129 1675384983775165459661347)
                ·
                  refine ⟨2513077475662748189492021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1675384983775165459661347 2513077475662748189492021)
                  ·
                    refine ⟨235601013343382642764877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2513077475662748189492021 235601013343382642764877)
                    ·
                      rfl

theorem cell22_688247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_688247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688247 prefixEnd_688247 := by exact prefixLift 688247
  have htrace : WordTrace (prefixWord ++ tailWord_688247) baseStart_688247 baseEnd_688247 := by
    simpa [prefixWord, tailWord_688247, baseEnd_688247] using wordTrace_append hprefix tailTrace_688247
  have hstable : (prefixWord ++ tailWord_688247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688247).length < 2 ^ (prefixWord ++ tailWord_688247).sum := by decide
  have hdescent : baseEnd_688247 < baseStart_688247 := by decide
  rcases family_descends (prefixWord ++ tailWord_688247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688266 : List Nat := [3, 1, 2, 3, 1, 2, 4, 2, 4]
def baseStart_688266 : Nat := 118140960795 + 688266 * 2 ^ 59
def prefixEnd_688266 : Nat := 4983230072969 + 3 ^ 40 * 688266 * 2
def baseEnd_688266 : Nat := 78535839143890975513273

theorem tailTrace_688266 : CollatzResearch.WordTrace tailWord_688266 prefixEnd_688266 78535839143890975513273 := by
  unfold tailWord_688266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6275780831134325829889163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16735415549691535546371101 6275780831134325829889163)
  ·
    refine ⟨9413671246701488744833745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6275780831134325829889163 9413671246701488744833745)
    ·
      refine ⟨7060253435026116558625309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9413671246701488744833745 7060253435026116558625309)
      ·
        refine ⟨2647595038134793709484491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7060253435026116558625309 2647595038134793709484491)
        ·
          refine ⟨3971392557202190564226737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2647595038134793709484491 3971392557202190564226737)
          ·
            refine ⟨2978544417901642923170053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3971392557202190564226737 2978544417901642923170053)
            ·
              refine ⟨558477078356558048094385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2978544417901642923170053 558477078356558048094385)
              ·
                refine ⟨418857808767418536070789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558477078356558048094385 418857808767418536070789)
                ·
                  refine ⟨78535839143890975513273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 418857808767418536070789 78535839143890975513273)
                  ·
                    rfl

theorem cell22_688266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 4].length) (baseStart_688266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688266 prefixEnd_688266 := by exact prefixLift 688266
  have htrace : WordTrace (prefixWord ++ tailWord_688266) baseStart_688266 baseEnd_688266 := by
    simpa [prefixWord, tailWord_688266, baseEnd_688266] using wordTrace_append hprefix tailTrace_688266
  have hstable : (prefixWord ++ tailWord_688266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688266).length < 2 ^ (prefixWord ++ tailWord_688266).sum := by decide
  have hdescent : baseEnd_688266 < baseStart_688266 := by decide
  rcases family_descends (prefixWord ++ tailWord_688266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688275 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 2, 7]
def baseStart_688275 : Nat := 118140960795 + 688275 * 2 ^ 59
def prefixEnd_688275 : Nat := 4983230072969 + 3 ^ 40 * 688275 * 2
def baseEnd_688275 : Nat := 235610598315599903064791

theorem tailTrace_688275 : CollatzResearch.WordTrace tailWord_688275 prefixEnd_688275 235610598315599903064791 := by
  unfold tailWord_688275
  simp only [CollatzResearch.WordTrace]
  refine ⟨25103451581504697856634279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16735634387669798571089519 25103451581504697856634279)
  ·
    refine ⟨37655177372257046784951419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25103451581504697856634279 37655177372257046784951419)
    ·
      refine ⟨56482766058385570177427129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37655177372257046784951419 56482766058385570177427129)
      ·
        refine ⟨42362074543789177633070347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56482766058385570177427129 42362074543789177633070347)
        ·
          refine ⟨63543111815683766449605521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42362074543789177633070347 63543111815683766449605521)
          ·
            refine ⟨47657333861762824837204141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63543111815683766449605521 47657333861762824837204141)
            ·
              refine ⟨17871500198161059313951553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47657333861762824837204141 17871500198161059313951553)
              ·
                refine ⟨13403625148620794485463665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17871500198161059313951553 13403625148620794485463665)
                ·
                  refine ⟨10052718861465595864097749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13403625148620794485463665 10052718861465595864097749)
                  ·
                    refine ⟨235610598315599903064791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10052718861465595864097749 235610598315599903064791)
                    ·
                      rfl

theorem cell22_688275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 7].length) (baseStart_688275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688275 prefixEnd_688275 := by exact prefixLift 688275
  have htrace : WordTrace (prefixWord ++ tailWord_688275) baseStart_688275 baseEnd_688275 := by
    simpa [prefixWord, tailWord_688275, baseEnd_688275] using wordTrace_append hprefix tailTrace_688275
  have hstable : (prefixWord ++ tailWord_688275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688275).length < 2 ^ (prefixWord ++ tailWord_688275).sum := by decide
  have hdescent : baseEnd_688275 < baseStart_688275 := by decide
  rcases family_descends (prefixWord ++ tailWord_688275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688302 : List Nat := [4, 1, 4, 2, 2, 1, 2, 1, 1, 4]
def baseStart_688302 : Nat := 118140960795 + 688302 * 2 ^ 59
def prefixEnd_688302 : Nat := 4983230072969 + 3 ^ 40 * 688302 * 2
def baseEnd_688302 : Nat := 235619840967380832639709

theorem tailTrace_688302 : CollatzResearch.WordTrace tailWord_688302 prefixEnd_688302 235619840967380832639709 := by
  unfold tailWord_688302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3138054544050860183483395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16736290901604587645244773 3138054544050860183483395)
  ·
    refine ⟨4707081816076290275225093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3138054544050860183483395 4707081816076290275225093)
    ·
      refine ⟨882577840514304426604705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4707081816076290275225093 882577840514304426604705)
      ·
        refine ⟨661933380385728319953529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 882577840514304426604705 661933380385728319953529)
        ·
          refine ⟨496450035289296239965147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 661933380385728319953529 496450035289296239965147)
          ·
            refine ⟨744675052933944359947721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496450035289296239965147 744675052933944359947721)
            ·
              refine ⟨558506289700458269960791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 744675052933944359947721 558506289700458269960791)
              ·
                refine ⟨837759434550687404941187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 558506289700458269960791 837759434550687404941187)
                ·
                  refine ⟨1256639151826031107411781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 837759434550687404941187 1256639151826031107411781)
                  ·
                    refine ⟨235619840967380832639709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1256639151826031107411781 235619840967380832639709)
                    ·
                      rfl

theorem cell22_688302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_688302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688302 prefixEnd_688302 := by exact prefixLift 688302
  have htrace : WordTrace (prefixWord ++ tailWord_688302) baseStart_688302 baseEnd_688302 := by
    simpa [prefixWord, tailWord_688302, baseEnd_688302] using wordTrace_append hprefix tailTrace_688302
  have hstable : (prefixWord ++ tailWord_688302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688302).length < 2 ^ (prefixWord ++ tailWord_688302).sum := by decide
  have hdescent : baseEnd_688302 < baseStart_688302 := by decide
  rcases family_descends (prefixWord ++ tailWord_688302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688337 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 2, 5]
def baseStart_688337 : Nat := 118140960795 + 688337 * 2 ^ 59
def prefixEnd_688337 : Nat := 4983230072969 + 3 ^ 40 * 688337 * 2
def baseEnd_688337 : Nat := 235631822182652408014601

theorem tailTrace_688337 : CollatzResearch.WordTrace tailWord_688337 prefixEnd_688337 235631822182652408014601 := by
  unfold tailWord_688337
  simp only [CollatzResearch.WordTrace]
  refine ⟨25105712907280082445391265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16737141938186721630260843 25105712907280082445391265)
  ·
    refine ⟨18829284680460061834043449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25105712907280082445391265 18829284680460061834043449)
    ·
      refine ⟨14121963510345046375532587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18829284680460061834043449 14121963510345046375532587)
      ·
        refine ⟨21182945265517569563298881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14121963510345046375532587 21182945265517569563298881)
        ·
          refine ⟨15887208949138177172474161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21182945265517569563298881 15887208949138177172474161)
          ·
            refine ⟨11915406711853632879355621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15887208949138177172474161 11915406711853632879355621)
            ·
              refine ⟨2234138758472556164879179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11915406711853632879355621 2234138758472556164879179)
              ·
                refine ⟨3351208137708834247318769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2234138758472556164879179 3351208137708834247318769)
                ·
                  refine ⟨2513406103281625685489077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3351208137708834247318769 2513406103281625685489077)
                  ·
                    refine ⟨235631822182652408014601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2513406103281625685489077 235631822182652408014601)
                    ·
                      rfl

theorem cell22_688337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_688337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688337 prefixEnd_688337 := by exact prefixLift 688337
  have htrace : WordTrace (prefixWord ++ tailWord_688337) baseStart_688337 baseEnd_688337 := by
    simpa [prefixWord, tailWord_688337, baseEnd_688337] using wordTrace_append hprefix tailTrace_688337
  have hstable : (prefixWord ++ tailWord_688337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688337).length < 2 ^ (prefixWord ++ tailWord_688337).sum := by decide
  have hdescent : baseEnd_688337 < baseStart_688337 := by decide
  rcases family_descends (prefixWord ++ tailWord_688337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688369 : List Nat := [1, 2, 2, 2, 2, 1, 4, 3, 1, 4]
def baseStart_688369 : Nat := 118140960795 + 688369 * 2 ^ 59
def prefixEnd_688369 : Nat := 4983230072969 + 3 ^ 40 * 688369 * 2
def baseEnd_688369 : Nat := 235642776436614991214503

theorem tailTrace_688369 : CollatzResearch.WordTrace tailWord_688369 prefixEnd_688369 235642776436614991214503 := by
  unfold tailWord_688369
  simp only [CollatzResearch.WordTrace]
  refine ⟨25106880043164151910556161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16737920028776101273704107 25106880043164151910556161)
  ·
    refine ⟨18830160032373113932917121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25106880043164151910556161 18830160032373113932917121)
    ·
      refine ⟨14122620024279835449687841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18830160032373113932917121 14122620024279835449687841)
      ·
        refine ⟨10591965018209876587265881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14122620024279835449687841 10591965018209876587265881)
        ·
          refine ⟨7943973763657407440449411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10591965018209876587265881 7943973763657407440449411)
          ·
            refine ⟨11915960645486111160674117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7943973763657407440449411 11915960645486111160674117)
            ·
              refine ⟨2234242621028645842626397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11915960645486111160674117 2234242621028645842626397)
              ·
                refine ⟨837840982885742190984899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2234242621028645842626397 837840982885742190984899)
                ·
                  refine ⟨1256761474328613286477349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 837840982885742190984899 1256761474328613286477349)
                  ·
                    refine ⟨235642776436614991214503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1256761474328613286477349 235642776436614991214503)
                    ·
                      rfl

theorem cell22_688369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_688369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688369 prefixEnd_688369 := by exact prefixLift 688369
  have htrace : WordTrace (prefixWord ++ tailWord_688369) baseStart_688369 baseEnd_688369 := by
    simpa [prefixWord, tailWord_688369, baseEnd_688369] using wordTrace_append hprefix tailTrace_688369
  have hstable : (prefixWord ++ tailWord_688369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688369).length < 2 ^ (prefixWord ++ tailWord_688369).sum := by decide
  have hdescent : baseEnd_688369 < baseStart_688369 := by decide
  rcases family_descends (prefixWord ++ tailWord_688369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688384 : List Nat := [2, 1, 1, 2, 1, 1, 4, 6, 4]
def baseStart_688384 : Nat := 118140960795 + 688384 * 2 ^ 59
def prefixEnd_688384 : Nat := 4983230072969 + 3 ^ 40 * 688384 * 2
def baseEnd_688384 : Nat := 78549303747719984029819

theorem tailTrace_688384 : CollatzResearch.WordTrace tailWord_688384 prefixEnd_688384 78549303747719984029819 := by
  unfold tailWord_688384
  simp only [CollatzResearch.WordTrace]
  refine ⟨12553713569054904736176103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16738284758739872981568137 12553713569054904736176103)
  ·
    refine ⟨18830570353582357104264155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12553713569054904736176103 18830570353582357104264155)
    ·
      refine ⟨28245855530373535656396233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18830570353582357104264155 28245855530373535656396233)
      ·
        refine ⟨21184391647780151742297175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28245855530373535656396233 21184391647780151742297175)
        ·
          refine ⟨31776587471670227613445763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21184391647780151742297175 31776587471670227613445763)
          ·
            refine ⟨47664881207505341420168645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31776587471670227613445763 47664881207505341420168645)
            ·
              refine ⟨8937165226407251516281621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47664881207505341420168645 8937165226407251516281621)
              ·
                refine ⟨418929619987839914825701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8937165226407251516281621 418929619987839914825701)
                ·
                  refine ⟨78549303747719984029819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 418929619987839914825701 78549303747719984029819)
                  ·
                    rfl

theorem cell22_688384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 4].length) (baseStart_688384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688384 prefixEnd_688384 := by exact prefixLift 688384
  have htrace : WordTrace (prefixWord ++ tailWord_688384) baseStart_688384 baseEnd_688384 := by
    simpa [prefixWord, tailWord_688384, baseEnd_688384] using wordTrace_append hprefix tailTrace_688384
  have hstable : (prefixWord ++ tailWord_688384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688384).length < 2 ^ (prefixWord ++ tailWord_688384).sum := by decide
  have hdescent : baseEnd_688384 < baseStart_688384 := by decide
  rcases family_descends (prefixWord ++ tailWord_688384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688429 : List Nat := [1, 5, 3, 1, 12]
def baseStart_688429 : Nat := 118140960795 + 688429 * 2 ^ 59
def prefixEnd_688429 : Nat := 4983230072969 + 3 ^ 40 * 688429 * 2
def baseEnd_688429 : Nat := 969807883385986974133

theorem tailTrace_688429 : CollatzResearch.WordTrace tailWord_688429 prefixEnd_688429 969807883385986974133 := by
  unfold tailWord_688429
  simp only [CollatzResearch.WordTrace]
  refine ⟨25109068422946782157740341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16739378948631188105160227 25109068422946782157740341)
  ·
    refine ⟨2353975164651260827288157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25109068422946782157740341 2353975164651260827288157)
    ·
      refine ⟨882740686744222810233059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2353975164651260827288157 882740686744222810233059)
      ·
        refine ⟨1324111030116334215349589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 882740686744222810233059 1324111030116334215349589)
        ·
          refine ⟨969807883385986974133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1324111030116334215349589 969807883385986974133)
          ·
            rfl

theorem cell22_688429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 12].length) (baseStart_688429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688429 prefixEnd_688429 := by exact prefixLift 688429
  have htrace : WordTrace (prefixWord ++ tailWord_688429) baseStart_688429 baseEnd_688429 := by
    simpa [prefixWord, tailWord_688429, baseEnd_688429] using wordTrace_append hprefix tailTrace_688429
  have hstable : (prefixWord ++ tailWord_688429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688429).length < 2 ^ (prefixWord ++ tailWord_688429).sum := by decide
  have hdescent : baseEnd_688429 < baseStart_688429 := by decide
  rcases family_descends (prefixWord ++ tailWord_688429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688433 : List Nat := [1, 2, 2, 3, 4, 1, 2, 2, 2, 3]
def baseStart_688433 : Nat := 118140960795 + 688433 * 2 ^ 59
def prefixEnd_688433 : Nat := 4983230072969 + 3 ^ 40 * 688433 * 2
def baseEnd_688433 : Nat := 235664684944540157614307

theorem tailTrace_688433 : CollatzResearch.WordTrace tailWord_688433 prefixEnd_688433 235664684944540157614307 := by
  unfold tailWord_688433
  simp only [CollatzResearch.WordTrace]
  refine ⟨25109214314932290840885953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16739476209954860560590635 25109214314932290840885953)
  ·
    refine ⟨18831910736199218130664465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25109214314932290840885953 18831910736199218130664465)
    ·
      refine ⟨14123933052149413597998349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18831910736199218130664465 14123933052149413597998349)
      ·
        refine ⟨5296474894556030099249381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14123933052149413597998349 5296474894556030099249381)
        ·
          refine ⟨993089042729255643609259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5296474894556030099249381 993089042729255643609259)
          ·
            refine ⟨1489633564093883465413889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993089042729255643609259 1489633564093883465413889)
            ·
              refine ⟨1117225173070412599060417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1489633564093883465413889 1117225173070412599060417)
              ·
                refine ⟨837918879802809449295313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1117225173070412599060417 837918879802809449295313)
                ·
                  refine ⟨628439159852107086971485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 837918879802809449295313 628439159852107086971485)
                  ·
                    refine ⟨235664684944540157614307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 628439159852107086971485 235664684944540157614307)
                    ·
                      rfl

theorem cell22_688433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_688433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688433 prefixEnd_688433 := by exact prefixLift 688433
  have htrace : WordTrace (prefixWord ++ tailWord_688433) baseStart_688433 baseEnd_688433 := by
    simpa [prefixWord, tailWord_688433, baseEnd_688433] using wordTrace_append hprefix tailTrace_688433
  have hstable : (prefixWord ++ tailWord_688433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688433).length < 2 ^ (prefixWord ++ tailWord_688433).sum := by decide
  have hdescent : baseEnd_688433 < baseStart_688433 := by decide
  rcases family_descends (prefixWord ++ tailWord_688433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688446 : List Nat := [4, 2, 1, 2, 1, 4, 1, 7]
def baseStart_688446 : Nat := 118140960795 + 688446 * 2 ^ 59
def prefixEnd_688446 : Nat := 4983230072969 + 3 ^ 40 * 688446 * 2
def baseEnd_688446 : Nat := 26185459456690273004363

theorem tailTrace_688446 : CollatzResearch.WordTrace tailWord_688446 prefixEnd_688446 26185459456690273004363 := by
  unfold tailWord_688446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3138711057985649257638649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16739792309256796040739461 3138711057985649257638649)
  ·
    refine ⟨2354033293489236943228987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3138711057985649257638649 2354033293489236943228987)
    ·
      refine ⟨3531049940233855414843481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2354033293489236943228987 3531049940233855414843481)
      ·
        refine ⟨2648287455175391561132611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3531049940233855414843481 2648287455175391561132611)
        ·
          refine ⟨3972431182763087341698917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2648287455175391561132611 3972431182763087341698917)
          ·
            refine ⟨744830846768078876568547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3972431182763087341698917 744830846768078876568547)
            ·
              refine ⟨1117246270152118314852821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 744830846768078876568547 1117246270152118314852821)
              ·
                refine ⟨26185459456690273004363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1117246270152118314852821 26185459456690273004363)
                ·
                  rfl

theorem cell22_688446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_688446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688446 prefixEnd_688446 := by exact prefixLift 688446
  have htrace : WordTrace (prefixWord ++ tailWord_688446) baseStart_688446 baseEnd_688446 := by
    simpa [prefixWord, tailWord_688446, baseEnd_688446] using wordTrace_append hprefix tailTrace_688446
  have hstable : (prefixWord ++ tailWord_688446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688446).length < 2 ^ (prefixWord ++ tailWord_688446).sum := by decide
  have hdescent : baseEnd_688446 < baseStart_688446 := by decide
  rcases family_descends (prefixWord ++ tailWord_688446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688457 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 9]
def baseStart_688457 : Nat := 118140960795 + 688457 * 2 ^ 59
def prefixEnd_688457 : Nat := 4983230072969 + 3 ^ 40 * 688457 * 2
def baseEnd_688457 : Nat := 78557633545004031671411

theorem tailTrace_688457 : CollatzResearch.WordTrace tailWord_688457 prefixEnd_688457 78557633545004031671411 := by
  unfold tailWord_688457
  simp only [CollatzResearch.WordTrace]
  refine ⟨25110089666845342939759625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16740059777896895293173083 25110089666845342939759625)
  ·
    refine ⟨18832567250134007204819719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25110089666845342939759625 18832567250134007204819719)
    ·
      refine ⟨28248850875201010807229579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18832567250134007204819719 28248850875201010807229579)
      ·
        refine ⟨42373276312801516210844369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28248850875201010807229579 42373276312801516210844369)
        ·
          refine ⟨31779957234601137158133277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42373276312801516210844369 31779957234601137158133277)
          ·
            refine ⟨11917483962975426434299979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31779957234601137158133277 11917483962975426434299979)
            ·
              refine ⟨17876225944463139651449969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11917483962975426434299979 17876225944463139651449969)
              ·
                refine ⟨13407169458347354738587477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17876225944463139651449969 13407169458347354738587477)
                ·
                  refine ⟨78557633545004031671411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13407169458347354738587477 78557633545004031671411)
                  ·
                    rfl

theorem cell22_688457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 9].length) (baseStart_688457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688457 prefixEnd_688457 := by exact prefixLift 688457
  have htrace : WordTrace (prefixWord ++ tailWord_688457) baseStart_688457 baseEnd_688457 := by
    simpa [prefixWord, tailWord_688457, baseEnd_688457] using wordTrace_append hprefix tailTrace_688457
  have hstable : (prefixWord ++ tailWord_688457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688457).length < 2 ^ (prefixWord ++ tailWord_688457).sum := by decide
  have hdescent : baseEnd_688457 < baseStart_688457 := by decide
  rcases family_descends (prefixWord ++ tailWord_688457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688519 : List Nat := [1, 1, 4, 2, 2, 1, 1, 4, 6]
def baseStart_688519 : Nat := 118140960795 + 688519 * 2 ^ 59
def prefixEnd_688519 : Nat := 4983230072969 + 3 ^ 40 * 688519 * 2
def baseEnd_688519 : Nat := 78564708167354866654681

theorem tailTrace_688519 : CollatzResearch.WordTrace tailWord_688519 prefixEnd_688519 78564708167354866654681 := by
  unfold tailWord_688519
  simp only [CollatzResearch.WordTrace]
  refine ⟨25112350992620727528516611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16741567328413818352344407 25112350992620727528516611)
  ·
    refine ⟨37668526488931091292774917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25112350992620727528516611 37668526488931091292774917)
    ·
      refine ⟨7062848716674579617395297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37668526488931091292774917 7062848716674579617395297)
      ·
        refine ⟨5297136537505934713046473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7062848716674579617395297 5297136537505934713046473)
        ·
          refine ⟨3972852403129451034784855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5297136537505934713046473 3972852403129451034784855)
          ·
            refine ⟨5959278604694176552177283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3972852403129451034784855 5959278604694176552177283)
            ·
              refine ⟨8938917907041264828265925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5959278604694176552177283 8938917907041264828265925)
              ·
                refine ⟨1676047107570237155299861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8938917907041264828265925 1676047107570237155299861)
                ·
                  refine ⟨78564708167354866654681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1676047107570237155299861 78564708167354866654681)
                  ·
                    rfl

theorem cell22_688519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 6].length) (baseStart_688519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688519 prefixEnd_688519 := by exact prefixLift 688519
  have htrace : WordTrace (prefixWord ++ tailWord_688519) baseStart_688519 baseEnd_688519 := by
    simpa [prefixWord, tailWord_688519, baseEnd_688519] using wordTrace_append hprefix tailTrace_688519
  have hstable : (prefixWord ++ tailWord_688519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688519).length < 2 ^ (prefixWord ++ tailWord_688519).sum := by decide
  have hdescent : baseEnd_688519 < baseStart_688519 := by decide
  rcases family_descends (prefixWord ++ tailWord_688519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688521 : List Nat := [1, 2, 1, 1, 6, 1, 1, 4, 1, 4]
def baseStart_688521 : Nat := 118140960795 + 688521 * 2 ^ 59
def prefixEnd_688521 : Nat := 4983230072969 + 3 ^ 40 * 688521 * 2
def baseEnd_688521 : Nat := 235694809142937261414037

theorem tailTrace_688521 : CollatzResearch.WordTrace tailWord_688521 prefixEnd_688521 235694809142937261414037 := by
  unfold tailWord_688521
  simp only [CollatzResearch.WordTrace]
  refine ⟨25112423938613481870089417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16741615959075654580059611 25112423938613481870089417)
  ·
    refine ⟨18834317953960111402567063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25112423938613481870089417 18834317953960111402567063)
    ·
      refine ⟨28251476930940167103850595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18834317953960111402567063 28251476930940167103850595)
      ·
        refine ⟨42377215396410250655775893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28251476930940167103850595 42377215396410250655775893)
        ·
          refine ⟨1986431971706730499489495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42377215396410250655775893 1986431971706730499489495)
          ·
            refine ⟨2979647957560095749234243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1986431971706730499489495 2979647957560095749234243)
            ·
              refine ⟨4469471936340143623851365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2979647957560095749234243 4469471936340143623851365)
              ·
                refine ⟨838025988063776929472131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4469471936340143623851365 838025988063776929472131)
                ·
                  refine ⟨1257038982095665394208197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 838025988063776929472131 1257038982095665394208197)
                  ·
                    refine ⟨235694809142937261414037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1257038982095665394208197 235694809142937261414037)
                    ·
                      rfl

theorem cell22_688521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 4].length) (baseStart_688521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688521 prefixEnd_688521 := by exact prefixLift 688521
  have htrace : WordTrace (prefixWord ++ tailWord_688521) baseStart_688521 baseEnd_688521 := by
    simpa [prefixWord, tailWord_688521, baseEnd_688521] using wordTrace_append hprefix tailTrace_688521
  have hstable : (prefixWord ++ tailWord_688521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688521).length < 2 ^ (prefixWord ++ tailWord_688521).sum := by decide
  have hdescent : baseEnd_688521 < baseStart_688521 := by decide
  rcases family_descends (prefixWord ++ tailWord_688521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688647 : List Nat := [1, 1, 4, 3, 3, 1, 2, 3, 1, 3]
def baseStart_688647 : Nat := 118140960795 + 688647 * 2 ^ 59
def prefixEnd_688647 : Nat := 4983230072969 + 3 ^ 40 * 688647 * 2
def baseEnd_688647 : Nat := 235737941517914932763651

theorem tailTrace_688647 : CollatzResearch.WordTrace tailWord_688647 prefixEnd_688647 235737941517914932763651 := by
  unfold tailWord_688647
  simp only [CollatzResearch.WordTrace]
  refine ⟨25117019536157005389176195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16744679690771336926117463 25117019536157005389176195)
  ·
    refine ⟨37675529304235508083764293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25117019536157005389176195 37675529304235508083764293)
    ·
      refine ⟨7064161744544157765705805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37675529304235508083764293 7064161744544157765705805)
      ·
        refine ⟨2649060654204059162139677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7064161744544157765705805 2649060654204059162139677)
        ·
          refine ⟨993397745326522185802379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2649060654204059162139677 993397745326522185802379)
          ·
            refine ⟨1490096617989783278703569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993397745326522185802379 1490096617989783278703569)
            ·
              refine ⟨1117572463492337459027677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1490096617989783278703569 1117572463492337459027677)
              ·
                refine ⟨419089673809626547135379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1117572463492337459027677 419089673809626547135379)
                ·
                  refine ⟨628634510714439820703069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419089673809626547135379 628634510714439820703069)
                  ·
                    refine ⟨235737941517914932763651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 628634510714439820703069 235737941517914932763651)
                    ·
                      rfl

theorem cell22_688647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_688647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688647 prefixEnd_688647 := by exact prefixLift 688647
  have htrace : WordTrace (prefixWord ++ tailWord_688647) baseStart_688647 baseEnd_688647 := by
    simpa [prefixWord, tailWord_688647, baseEnd_688647] using wordTrace_append hprefix tailTrace_688647
  have hstable : (prefixWord ++ tailWord_688647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688647).length < 2 ^ (prefixWord ++ tailWord_688647).sum := by decide
  have hdescent : baseEnd_688647 < baseStart_688647 := by decide
  rcases family_descends (prefixWord ++ tailWord_688647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688660 : List Nat := [2, 4, 3, 1, 1, 1, 3, 2, 5]
def baseStart_688660 : Nat := 118140960795 + 688660 * 2 ^ 59
def prefixEnd_688660 : Nat := 4983230072969 + 3 ^ 40 * 688660 * 2
def baseEnd_688660 : Nat := 78580797227862410729537

theorem tailTrace_688660 : CollatzResearch.WordTrace tailWord_688660 prefixEnd_688660 78580797227862410729537 := by
  unfold tailWord_688660
  simp only [CollatzResearch.WordTrace]
  refine ⟨12558746842554954304699717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16744995790073272406266289 12558746842554954304699717)
  ·
    refine ⟨2354765032979053932131197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12558746842554954304699717 2354765032979053932131197)
    ·
      refine ⟨883036887367145224549199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2354765032979053932131197 883036887367145224549199)
      ·
        refine ⟨1324555331050717836823799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 883036887367145224549199 1324555331050717836823799)
        ·
          refine ⟨1986832996576076755235699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1324555331050717836823799 1986832996576076755235699)
          ·
            refine ⟨2980249494864115132853549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1986832996576076755235699 2980249494864115132853549)
            ·
              refine ⟨1117593560574043174820081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2980249494864115132853549 1117593560574043174820081)
              ·
                refine ⟨838195170430532381115061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1117593560574043174820081 838195170430532381115061)
                ·
                  refine ⟨78580797227862410729537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 838195170430532381115061 78580797227862410729537)
                  ·
                    rfl

theorem cell22_688660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_688660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688660 prefixEnd_688660 := by exact prefixLift 688660
  have htrace : WordTrace (prefixWord ++ tailWord_688660) baseStart_688660 baseEnd_688660 := by
    simpa [prefixWord, tailWord_688660, baseEnd_688660] using wordTrace_append hprefix tailTrace_688660
  have hstable : (prefixWord ++ tailWord_688660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688660).length < 2 ^ (prefixWord ++ tailWord_688660).sum := by decide
  have hdescent : baseEnd_688660 < baseStart_688660 := by decide
  rcases family_descends (prefixWord ++ tailWord_688660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688705 : List Nat := [1, 2, 5, 1, 1, 2, 3, 3, 4]
def baseStart_688705 : Nat := 118140960795 + 688705 * 2 ^ 59
def prefixEnd_688705 : Nat := 4983230072969 + 3 ^ 40 * 688705 * 2
def baseEnd_688705 : Nat := 78585932034407371604491

theorem tailTrace_688705 : CollatzResearch.WordTrace tailWord_688705 prefixEnd_688705 78585932034407371604491 := by
  unfold tailWord_688705
  simp only [CollatzResearch.WordTrace]
  refine ⟨25119134969946881294787569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16746089979964587529858379 25119134969946881294787569)
  ·
    refine ⟨18839351227460160971090677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25119134969946881294787569 18839351227460160971090677)
    ·
      refine ⟨1766189177574390091039751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18839351227460160971090677 1766189177574390091039751)
      ·
        refine ⟨2649283766361585136559627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1766189177574390091039751 2649283766361585136559627)
        ·
          refine ⟨3973925649542377704839441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2649283766361585136559627 3973925649542377704839441)
          ·
            refine ⟨2980444237156783278629581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3973925649542377704839441 2980444237156783278629581)
            ·
              refine ⟨1117666588933793729486093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2980444237156783278629581 1117666588933793729486093)
              ·
                refine ⟨419124970850172648557285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1117666588933793729486093 419124970850172648557285)
                ·
                  refine ⟨78585932034407371604491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 419124970850172648557285 78585932034407371604491)
                  ·
                    rfl

theorem cell22_688705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 4].length) (baseStart_688705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688705 prefixEnd_688705 := by exact prefixLift 688705
  have htrace : WordTrace (prefixWord ++ tailWord_688705) baseStart_688705 baseEnd_688705 := by
    simpa [prefixWord, tailWord_688705, baseEnd_688705] using wordTrace_append hprefix tailTrace_688705
  have hstable : (prefixWord ++ tailWord_688705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688705).length < 2 ^ (prefixWord ++ tailWord_688705).sum := by decide
  have hdescent : baseEnd_688705 < baseStart_688705 := by decide
  rcases family_descends (prefixWord ++ tailWord_688705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688737 : List Nat := [1, 2, 3, 1, 1, 6, 2, 1, 2, 3]
def baseStart_688737 : Nat := 118140960795 + 688737 * 2 ^ 59
def prefixEnd_688737 : Nat := 4983230072969 + 3 ^ 40 * 688737 * 2
def baseEnd_688737 : Nat := 235768750357184698013375

theorem tailTrace_688737 : CollatzResearch.WordTrace tailWord_688737 prefixEnd_688737 235768750357184698013375 := by
  unfold tailWord_688737
  simp only [CollatzResearch.WordTrace]
  refine ⟨25120302105830950759952465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16746868070553967173301643 25120302105830950759952465)
  ·
    refine ⟨18840226579373213069964349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25120302105830950759952465 18840226579373213069964349)
    ·
      refine ⟨7065084967264954901236631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18840226579373213069964349 7065084967264954901236631)
      ·
        refine ⟨10597627450897432351854947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7065084967264954901236631 10597627450897432351854947)
        ·
          refine ⟨15896441176346148527782421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10597627450897432351854947 15896441176346148527782421)
          ·
            refine ⟨745145680141225712239801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15896441176346148527782421 745145680141225712239801)
            ·
              refine ⟨558859260105919284179851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 745145680141225712239801 558859260105919284179851)
              ·
                refine ⟨838288890158878926269777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 558859260105919284179851 838288890158878926269777)
                ·
                  refine ⟨628716667619159194702333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 838288890158878926269777 628716667619159194702333)
                  ·
                    refine ⟨235768750357184698013375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 628716667619159194702333 235768750357184698013375)
                    ·
                      rfl

theorem cell22_688737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_688737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688737 prefixEnd_688737 := by exact prefixLift 688737
  have htrace : WordTrace (prefixWord ++ tailWord_688737) baseStart_688737 baseEnd_688737 := by
    simpa [prefixWord, tailWord_688737, baseEnd_688737] using wordTrace_append hprefix tailTrace_688737
  have hstable : (prefixWord ++ tailWord_688737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688737).length < 2 ^ (prefixWord ++ tailWord_688737).sum := by decide
  have hdescent : baseEnd_688737 < baseStart_688737 := by decide
  rcases family_descends (prefixWord ++ tailWord_688737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688748 : List Nat := [2, 2, 1, 1, 3, 1, 2, 4, 3, 3]
def baseStart_688748 : Nat := 118140960795 + 688748 * 2 ^ 59
def prefixEnd_688748 : Nat := 4983230072969 + 3 ^ 40 * 688748 * 2
def baseEnd_688748 : Nat := 235772515881984335988341

theorem tailTrace_688748 : CollatzResearch.WordTrace tailWord_688748 prefixEnd_688748 235772515881984335988341 := by
  unfold tailWord_688748
  simp only [CollatzResearch.WordTrace]
  refine ⟨12560351654395549819301449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16747135539194066425735265 12560351654395549819301449)
  ·
    refine ⟨9420263740796662364476087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12560351654395549819301449 9420263740796662364476087)
    ·
      refine ⟨14130395611194993546714131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9420263740796662364476087 14130395611194993546714131)
      ·
        refine ⟨21195593416792490320071197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14130395611194993546714131 21195593416792490320071197)
        ·
          refine ⟨7948347531297183870026699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21195593416792490320071197 7948347531297183870026699)
          ·
            refine ⟨11922521296945775805040049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7948347531297183870026699 11922521296945775805040049)
            ·
              refine ⟨8941890972709331853780037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11922521296945775805040049 8941890972709331853780037)
              ·
                refine ⟨1676604557382999722583757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8941890972709331853780037 1676604557382999722583757)
                ·
                  refine ⟨628726709018624895968909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1676604557382999722583757 628726709018624895968909)
                  ·
                    refine ⟨235772515881984335988341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 628726709018624895968909 235772515881984335988341)
                    ·
                      rfl

theorem cell22_688748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_688748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688748 prefixEnd_688748 := by exact prefixLift 688748
  have htrace : WordTrace (prefixWord ++ tailWord_688748) baseStart_688748 baseEnd_688748 := by
    simpa [prefixWord, tailWord_688748, baseEnd_688748] using wordTrace_append hprefix tailTrace_688748
  have hstable : (prefixWord ++ tailWord_688748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688748).length < 2 ^ (prefixWord ++ tailWord_688748).sum := by decide
  have hdescent : baseEnd_688748 < baseStart_688748 := by decide
  rcases family_descends (prefixWord ++ tailWord_688748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688782 : List Nat := [4, 1, 1, 3, 1, 1, 3, 4, 1, 3]
def baseStart_688782 : Nat := 118140960795 + 688782 * 2 ^ 59
def prefixEnd_688782 : Nat := 4983230072969 + 3 ^ 40 * 688782 * 2
def baseEnd_688782 : Nat := 235784154776819580638237

theorem tailTrace_688782 : CollatzResearch.WordTrace tailWord_688782 prefixEnd_688782 235784154776819580638237 := by
  unfold tailWord_688782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3140242923833490430667575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16747962260445282296893733 3140242923833490430667575)
  ·
    refine ⟨4710364385750235646001363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3140242923833490430667575 4710364385750235646001363)
    ·
      refine ⟨7065546578625353469002045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4710364385750235646001363 7065546578625353469002045)
      ·
        refine ⟨2649579966984507550875767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7065546578625353469002045 2649579966984507550875767)
        ·
          refine ⟨3974369950476761326313651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2649579966984507550875767 3974369950476761326313651)
          ·
            refine ⟨5961554925715141989470477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3974369950476761326313651 5961554925715141989470477)
            ·
              refine ⟨2235583097143178246051429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5961554925715141989470477 2235583097143178246051429)
              ·
                refine ⟨419171830714345921134643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2235583097143178246051429 419171830714345921134643)
                ·
                  refine ⟨628757746071518881701965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419171830714345921134643 628757746071518881701965)
                  ·
                    refine ⟨235784154776819580638237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 628757746071518881701965 235784154776819580638237)
                    ·
                      rfl

theorem cell22_688782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_688782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688782 prefixEnd_688782 := by exact prefixLift 688782
  have htrace : WordTrace (prefixWord ++ tailWord_688782) baseStart_688782 baseEnd_688782 := by
    simpa [prefixWord, tailWord_688782, baseEnd_688782] using wordTrace_append hprefix tailTrace_688782
  have hstable : (prefixWord ++ tailWord_688782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688782).length < 2 ^ (prefixWord ++ tailWord_688782).sum := by decide
  have hdescent : baseEnd_688782 < baseStart_688782 := by decide
  rcases family_descends (prefixWord ++ tailWord_688782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688840 : List Nat := [2, 1, 3, 1, 2, 3, 2, 4, 4]
def baseStart_688840 : Nat := 118140960795 + 688840 * 2 ^ 59
def prefixEnd_688840 : Nat := 4983230072969 + 3 ^ 40 * 688840 * 2
def baseEnd_688840 : Nat := 78601336454042254229353

theorem tailTrace_688840 : CollatzResearch.WordTrace tailWord_688840 prefixEnd_688840 78601336454042254229353 := by
  unfold tailWord_688840
  simp only [CollatzResearch.WordTrace]
  refine ⟨12562029412228899675475987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16749372549638532900634649 12562029412228899675475987)
  ·
    refine ⟨18843044118343349513213981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12562029412228899675475987 18843044118343349513213981)
    ·
      refine ⟨7066141544378756067455243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18843044118343349513213981 7066141544378756067455243)
      ·
        refine ⟨10599212316568134101182865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7066141544378756067455243 10599212316568134101182865)
        ·
          refine ⟨7949409237426100575887149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10599212316568134101182865 7949409237426100575887149)
          ·
            refine ⟨2981028464034787715957681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7949409237426100575887149 2981028464034787715957681)
            ·
              refine ⟨2235771348026090786968261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2981028464034787715957681 2235771348026090786968261)
              ·
                refine ⟨419207127754892022556549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2235771348026090786968261 419207127754892022556549)
                ·
                  refine ⟨78601336454042254229353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 419207127754892022556549 78601336454042254229353)
                  ·
                    rfl

theorem cell22_688840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 4].length) (baseStart_688840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688840 prefixEnd_688840 := by exact prefixLift 688840
  have htrace : WordTrace (prefixWord ++ tailWord_688840) baseStart_688840 baseEnd_688840 := by
    simpa [prefixWord, tailWord_688840, baseEnd_688840] using wordTrace_append hprefix tailTrace_688840
  have hstable : (prefixWord ++ tailWord_688840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688840).length < 2 ^ (prefixWord ++ tailWord_688840).sum := by decide
  have hdescent : baseEnd_688840 < baseStart_688840 := by decide
  rcases family_descends (prefixWord ++ tailWord_688840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688855 : List Nat := [1, 1, 3, 2, 1, 6, 1, 1, 1, 5]
def baseStart_688855 : Nat := 118140960795 + 688855 * 2 ^ 59
def prefixEnd_688855 : Nat := 4983230072969 + 3 ^ 40 * 688855 * 2
def baseEnd_688855 : Nat := 235809144168671723563013

theorem tailTrace_688855 : CollatzResearch.WordTrace tailWord_688855 prefixEnd_688855 235809144168671723563013 := by
  unfold tailWord_688855
  simp only [CollatzResearch.WordTrace]
  refine ⟨25124605919403456912748019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16749737279602304608498679 25124605919403456912748019)
  ·
    refine ⟨37686908879105185369122029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25124605919403456912748019 37686908879105185369122029)
    ·
      refine ⟨14132590829664444513420761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37686908879105185369122029 14132590829664444513420761)
      ·
        refine ⟨10599443122248333385065571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14132590829664444513420761 10599443122248333385065571)
        ·
          refine ⟨15899164683372500077598357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10599443122248333385065571 15899164683372500077598357)
          ·
            refine ⟨745273344533085941137423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15899164683372500077598357 745273344533085941137423)
            ·
              refine ⟨1117910016799628911706135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 745273344533085941137423 1117910016799628911706135)
              ·
                refine ⟨1676865025199443367559203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117910016799628911706135 1676865025199443367559203)
                ·
                  refine ⟨2515297537799165051338805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1676865025199443367559203 2515297537799165051338805)
                  ·
                    refine ⟨235809144168671723563013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2515297537799165051338805 235809144168671723563013)
                    ·
                      rfl

theorem cell22_688855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_688855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688855 prefixEnd_688855 := by exact prefixLift 688855
  have htrace : WordTrace (prefixWord ++ tailWord_688855) baseStart_688855 baseEnd_688855 := by
    simpa [prefixWord, tailWord_688855, baseEnd_688855] using wordTrace_append hprefix tailTrace_688855
  have hstable : (prefixWord ++ tailWord_688855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688855).length < 2 ^ (prefixWord ++ tailWord_688855).sum := by decide
  have hdescent : baseEnd_688855 < baseStart_688855 := by decide
  rcases family_descends (prefixWord ++ tailWord_688855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688868 : List Nat := [2, 3, 1, 1, 1, 5, 1, 8]
def baseStart_688868 : Nat := 118140960795 + 688868 * 2 ^ 59
def prefixEnd_688868 : Nat := 4983230072969 + 3 ^ 40 * 688868 * 2
def baseEnd_688868 : Nat := 26201510481593780331997

theorem tailTrace_688868 : CollatzResearch.WordTrace tailWord_688868 prefixEnd_688868 26201510481593780331997 := by
  unfold tailWord_688868
  simp only [CollatzResearch.WordTrace]
  refine ⟨12562540034178180066485629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16750053378904240088647505 12562540034178180066485629)
  ·
    refine ⟨4710952512816817524932111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12562540034178180066485629 4710952512816817524932111)
    ·
      refine ⟨7066428769225226287398167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4710952512816817524932111 7066428769225226287398167)
      ·
        refine ⟨10599643153837839431097251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7066428769225226287398167 10599643153837839431097251)
        ·
          refine ⟨15899464730756759146645877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10599643153837839431097251 15899464730756759146645877)
          ·
            refine ⟨1490574818508446169998051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15899464730756759146645877 1490574818508446169998051)
            ·
              refine ⟨2235862227762669254997077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1490574818508446169998051 2235862227762669254997077)
              ·
                refine ⟨26201510481593780331997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2235862227762669254997077 26201510481593780331997)
                ·
                  rfl

theorem cell22_688868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 8].length) (baseStart_688868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688868 prefixEnd_688868 := by exact prefixLift 688868
  have htrace : WordTrace (prefixWord ++ tailWord_688868) baseStart_688868 baseEnd_688868 := by
    simpa [prefixWord, tailWord_688868, baseEnd_688868] using wordTrace_append hprefix tailTrace_688868
  have hstable : (prefixWord ++ tailWord_688868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688868).length < 2 ^ (prefixWord ++ tailWord_688868).sum := by decide
  have hdescent : baseEnd_688868 < baseStart_688868 := by decide
  rcases family_descends (prefixWord ++ tailWord_688868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688943 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 7, 4]
def baseStart_688943 : Nat := 118140960795 + 688943 * 2 ^ 59
def prefixEnd_688943 : Nat := 4983230072969 + 3 ^ 40 * 688943 * 2
def baseEnd_688943 : Nat := 235839268367068827362743

theorem tailTrace_688943 : CollatzResearch.WordTrace tailWord_688943 prefixEnd_688943 235839268367068827362743 := by
  unfold tailWord_688943
  simp only [CollatzResearch.WordTrace]
  refine ⟨25127815543084647941951483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16751877028723098627967655 25127815543084647941951483)
  ·
    refine ⟨37691723314626971912927225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25127815543084647941951483 37691723314626971912927225)
    ·
      refine ⟨28268792485970228934695419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37691723314626971912927225 28268792485970228934695419)
      ·
        refine ⟨42403188728955343402043129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28268792485970228934695419 42403188728955343402043129)
        ·
          refine ⟨31802391546716507551532347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42403188728955343402043129 31802391546716507551532347)
          ·
            refine ⟨47703587320074761327298521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31802391546716507551532347 47703587320074761327298521)
            ·
              refine ⟨35777690490056070995473891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47703587320074761327298521 35777690490056070995473891)
              ·
                refine ⟨53666535735084106493210837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35777690490056070995473891 53666535735084106493210837)
                ·
                  refine ⟨1257809431291033745934629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 53666535735084106493210837 1257809431291033745934629)
                  ·
                    refine ⟨235839268367068827362743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1257809431291033745934629 235839268367068827362743)
                    ·
                      rfl

theorem cell22_688943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 4].length) (baseStart_688943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688943 prefixEnd_688943 := by exact prefixLift 688943
  have htrace : WordTrace (prefixWord ++ tailWord_688943) baseStart_688943 baseEnd_688943 := by
    simpa [prefixWord, tailWord_688943, baseEnd_688943] using wordTrace_append hprefix tailTrace_688943
  have hstable : (prefixWord ++ tailWord_688943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688943).length < 2 ^ (prefixWord ++ tailWord_688943).sum := by decide
  have hdescent : baseEnd_688943 < baseStart_688943 := by decide
  rcases family_descends (prefixWord ++ tailWord_688943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688992 : List Nat := [2, 1, 1, 3, 3, 1, 4, 3, 4]
def baseStart_688992 : Nat := 118140960795 + 688992 * 2 ^ 59
def prefixEnd_688992 : Nat := 4983230072969 + 3 ^ 40 * 688992 * 2
def baseEnd_688992 : Nat := 78618680689483010962531

theorem tailTrace_688992 : CollatzResearch.WordTrace tailWord_688992 prefixEnd_688992 78618680689483010962531 := by
  unfold tailWord_688992
  simp only [CollatzResearch.WordTrace]
  refine ⟨12564801359953564655242615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16753068479938086206990153 12564801359953564655242615)
  ·
    refine ⟨18847202039930346982863923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12564801359953564655242615 18847202039930346982863923)
    ·
      refine ⟨28270803059895520474295885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18847202039930346982863923 28270803059895520474295885)
      ·
        refine ⟨10601551147460820177860957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28270803059895520474295885 10601551147460820177860957)
        ·
          refine ⟨3975581680297807566697859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10601551147460820177860957 3975581680297807566697859)
          ·
            refine ⟨5963372520446711350046789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3975581680297807566697859 5963372520446711350046789)
            ·
              refine ⟨1118132347583758378133773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5963372520446711350046789 1118132347583758378133773)
              ·
                refine ⟨419299630343909391800165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1118132347583758378133773 419299630343909391800165)
                ·
                  refine ⟨78618680689483010962531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 419299630343909391800165 78618680689483010962531)
                  ·
                    rfl

theorem cell22_688992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 4].length) (baseStart_688992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688992 prefixEnd_688992 := by exact prefixLift 688992
  have htrace : WordTrace (prefixWord ++ tailWord_688992) baseStart_688992 baseEnd_688992 := by
    simpa [prefixWord, tailWord_688992, baseEnd_688992] using wordTrace_append hprefix tailTrace_688992
  have hstable : (prefixWord ++ tailWord_688992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688992).length < 2 ^ (prefixWord ++ tailWord_688992).sum := by decide
  have hdescent : baseEnd_688992 < baseStart_688992 := by decide
  rcases family_descends (prefixWord ++ tailWord_688992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688994 : List Nat := [3, 3, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_688994 : Nat := 118140960795 + 688994 * 2 ^ 59
def prefixEnd_688994 : Nat := 4983230072969 + 3 ^ 40 * 688994 * 2
def baseEnd_688994 : Nat := 235856726709321694337587

theorem tailTrace_688994 : CollatzResearch.WordTrace tailWord_688994 prefixEnd_688994 235856726709321694337587 := by
  unfold tailWord_688994
  simp only [CollatzResearch.WordTrace]
  refine ⟨6282418916474970913014509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16753117110599922434705357 6282418916474970913014509)
  ·
    refine ⟨2355907093678114092380441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6282418916474970913014509 2355907093678114092380441)
    ·
      refine ⟨1766930320258585569285331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2355907093678114092380441 1766930320258585569285331)
      ·
        refine ⟨2650395480387878353927997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1766930320258585569285331 2650395480387878353927997)
        ·
          refine ⟨993898305145454382722999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2650395480387878353927997 993898305145454382722999)
          ·
            refine ⟨1490847457718181574084499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993898305145454382722999 1490847457718181574084499)
            ·
              refine ⟨2236271186577272361126749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1490847457718181574084499 2236271186577272361126749)
              ·
                refine ⟨838601694966477135422531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2236271186577272361126749 838601694966477135422531)
                ·
                  refine ⟨1257902542449715703133797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 838601694966477135422531 1257902542449715703133797)
                  ·
                    refine ⟨235856726709321694337587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1257902542449715703133797 235856726709321694337587)
                    ·
                      rfl

theorem cell22_688994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_688994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_688994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_688994 prefixEnd_688994 := by exact prefixLift 688994
  have htrace : WordTrace (prefixWord ++ tailWord_688994) baseStart_688994 baseEnd_688994 := by
    simpa [prefixWord, tailWord_688994, baseEnd_688994] using wordTrace_append hprefix tailTrace_688994
  have hstable : (prefixWord ++ tailWord_688994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688994).length < 2 ^ (prefixWord ++ tailWord_688994).sum := by decide
  have hdescent : baseEnd_688994 < baseStart_688994 := by decide
  rcases family_descends (prefixWord ++ tailWord_688994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689005 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_689005 : Nat := 118140960795 + 689005 * 2 ^ 59
def prefixEnd_689005 : Nat := 4983230072969 + 3 ^ 40 * 689005 * 2
def baseEnd_689005 : Nat := 235860492234121332312553

theorem tailTrace_689005 : CollatzResearch.WordTrace tailWord_689005 prefixEnd_689005 235860492234121332312553 := by
  unfold tailWord_689005
  simp only [CollatzResearch.WordTrace]
  refine ⟨25130076868860032530708469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16753384579240021687138979 25130076868860032530708469)
  ·
    refine ⟨2355944706455628049753919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25130076868860032530708469 2355944706455628049753919)
    ·
      refine ⟨3533917059683442074630879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2355944706455628049753919 3533917059683442074630879)
      ·
        refine ⟨5300875589525163111946319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3533917059683442074630879 5300875589525163111946319)
        ·
          refine ⟨7951313384287744667919479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5300875589525163111946319 7951313384287744667919479)
          ·
            refine ⟨11926970076431617001879219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7951313384287744667919479 11926970076431617001879219)
            ·
              refine ⟨17890455114647425502818829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11926970076431617001879219 17890455114647425502818829)
              ·
                refine ⟨6708920667992784563557061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17890455114647425502818829 6708920667992784563557061)
                ·
                  refine ⟨1257922625248647105666949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6708920667992784563557061 1257922625248647105666949)
                  ·
                    refine ⟨235860492234121332312553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1257922625248647105666949 235860492234121332312553)
                    ·
                      rfl

theorem cell22_689005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_689005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689005 prefixEnd_689005 := by exact prefixLift 689005
  have htrace : WordTrace (prefixWord ++ tailWord_689005) baseStart_689005 baseEnd_689005 := by
    simpa [prefixWord, tailWord_689005, baseEnd_689005] using wordTrace_append hprefix tailTrace_689005
  have hstable : (prefixWord ++ tailWord_689005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689005).length < 2 ^ (prefixWord ++ tailWord_689005).sum := by decide
  have hdescent : baseEnd_689005 < baseStart_689005 := by decide
  rcases family_descends (prefixWord ++ tailWord_689005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689065 : List Nat := [1, 2, 1, 1, 1, 1, 6, 4, 5]
def baseStart_689065 : Nat := 118140960795 + 689065 * 2 ^ 59
def prefixEnd_689065 : Nat := 4983230072969 + 3 ^ 40 * 689065 * 2
def baseEnd_689065 : Nat := 78627010486767058604123

theorem tailTrace_689065 : CollatzResearch.WordTrace tailWord_689065 prefixEnd_689065 78627010486767058604123 := by
  unfold tailWord_689065
  simp only [CollatzResearch.WordTrace]
  refine ⟨25132265248642662777892649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16754843499095108518595099 25132265248642662777892649)
  ·
    refine ⟨18849198936481997083419487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25132265248642662777892649 18849198936481997083419487)
    ·
      refine ⟨28273798404722995625129231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18849198936481997083419487 28273798404722995625129231)
      ·
        refine ⟨42410697607084493437693847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28273798404722995625129231 42410697607084493437693847)
        ·
          refine ⟨63616046410626740156540771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42410697607084493437693847 63616046410626740156540771)
          ·
            refine ⟨95424069615940110234811157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63616046410626740156540771 95424069615940110234811157)
            ·
              refine ⟨4473003263247192667256773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95424069615940110234811157 4473003263247192667256773)
              ·
                refine ⟨838688111858848625110645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4473003263247192667256773 838688111858848625110645)
                ·
                  refine ⟨78627010486767058604123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 838688111858848625110645 78627010486767058604123)
                  ·
                    rfl

theorem cell22_689065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 5].length) (baseStart_689065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689065 prefixEnd_689065 := by exact prefixLift 689065
  have htrace : WordTrace (prefixWord ++ tailWord_689065) baseStart_689065 baseEnd_689065 := by
    simpa [prefixWord, tailWord_689065, baseEnd_689065] using wordTrace_append hprefix tailTrace_689065
  have hstable : (prefixWord ++ tailWord_689065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689065).length < 2 ^ (prefixWord ++ tailWord_689065).sum := by decide
  have hdescent : baseEnd_689065 < baseStart_689065 := by decide
  rcases family_descends (prefixWord ++ tailWord_689065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689176 : List Nat := [2, 1, 2, 3, 2, 4, 1, 2, 2, 3]
def baseStart_689176 : Nat := 118140960795 + 689176 * 2 ^ 59
def prefixEnd_689176 : Nat := 4983230072969 + 3 ^ 40 * 689176 * 2
def baseEnd_689176 : Nat := 235919029028733886287029

theorem tailTrace_689176 : CollatzResearch.WordTrace tailWord_689176 prefixEnd_689176 235919029028733886287029 := by
  unfold tailWord_689176
  simp only [CollatzResearch.WordTrace]
  refine ⟨12568156875620264367591691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16757542500827019156788921 12568156875620264367591691)
  ·
    refine ⟨18852235313430396551387537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12568156875620264367591691 18852235313430396551387537)
    ·
      refine ⟨14139176485072797413540653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18852235313430396551387537 14139176485072797413540653)
      ·
        refine ⟨5302191181902299030077745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14139176485072797413540653 5302191181902299030077745)
        ·
          refine ⟨3976643386426724272558309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5302191181902299030077745 3976643386426724272558309)
          ·
            refine ⟨745620634955010801104683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3976643386426724272558309 745620634955010801104683)
            ·
              refine ⟨1118430952432516201657025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 745620634955010801104683 1118430952432516201657025)
              ·
                refine ⟨838823214324387151242769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1118430952432516201657025 838823214324387151242769)
                ·
                  refine ⟨629117410743290363432077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 838823214324387151242769 629117410743290363432077)
                  ·
                    refine ⟨235919029028733886287029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 629117410743290363432077 235919029028733886287029)
                    ·
                      rfl

theorem cell22_689176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_689176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689176 prefixEnd_689176 := by exact prefixLift 689176
  have htrace : WordTrace (prefixWord ++ tailWord_689176) baseStart_689176 baseEnd_689176 := by
    simpa [prefixWord, tailWord_689176, baseEnd_689176] using wordTrace_append hprefix tailTrace_689176
  have hstable : (prefixWord ++ tailWord_689176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689176).length < 2 ^ (prefixWord ++ tailWord_689176).sum := by decide
  have hdescent : baseEnd_689176 < baseStart_689176 := by decide
  rcases family_descends (prefixWord ++ tailWord_689176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689206 : List Nat := [5, 1, 2, 1, 1, 4, 2, 6]
def baseStart_689206 : Nat := 118140960795 + 689206 * 2 ^ 59
def prefixEnd_689206 : Nat := 4983230072969 + 3 ^ 40 * 689206 * 2
def baseEnd_689206 : Nat := 26214366515758200892993

theorem tailTrace_689206 : CollatzResearch.WordTrace tailWord_689206 prefixEnd_689206 26214366515758200892993 := by
  unfold tailWord_689206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1571087996320740241173467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16758271960754562572516981 1571087996320740241173467)
  ·
    refine ⟨2356631994481110361760201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1571087996320740241173467 2356631994481110361760201)
    ·
      refine ⟨1767473995860832771320151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2356631994481110361760201 1767473995860832771320151)
      ·
        refine ⟨2651210993791249156980227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1767473995860832771320151 2651210993791249156980227)
        ·
          refine ⟨3976816490686873735470341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2651210993791249156980227 3976816490686873735470341)
          ·
            refine ⟨745653092003788825400689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3976816490686873735470341 745653092003788825400689)
            ·
              refine ⟨559239819002841619050517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 745653092003788825400689 559239819002841619050517)
              ·
                refine ⟨26214366515758200892993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 559239819002841619050517 26214366515758200892993)
                ·
                  rfl

theorem cell22_689206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_689206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689206 prefixEnd_689206 := by exact prefixLift 689206
  have htrace : WordTrace (prefixWord ++ tailWord_689206) baseStart_689206 baseEnd_689206 := by
    simpa [prefixWord, tailWord_689206, baseEnd_689206] using wordTrace_append hprefix tailTrace_689206
  have hstable : (prefixWord ++ tailWord_689206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689206).length < 2 ^ (prefixWord ++ tailWord_689206).sum := by decide
  have hdescent : baseEnd_689206 < baseStart_689206 := by decide
  rcases family_descends (prefixWord ++ tailWord_689206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689221 : List Nat := [1, 3, 1, 1, 1, 3, 5, 3, 1, 3]
def baseStart_689221 : Nat := 118140960795 + 689221 * 2 ^ 59
def prefixEnd_689221 : Nat := 4983230072969 + 3 ^ 40 * 689221 * 2
def baseEnd_689221 : Nat := 235934433448368768911891

theorem tailTrace_689221 : CollatzResearch.WordTrace tailWord_689221 prefixEnd_689221 235934433448368768911891 := by
  unfold tailWord_689221
  simp only [CollatzResearch.WordTrace]
  refine ⟨25137955036077501420571517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16758636690718334280381011 25137955036077501420571517)
  ·
    refine ⟨9426733138529063032714319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25137955036077501420571517 9426733138529063032714319)
    ·
      refine ⟨14140099707793594549071479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9426733138529063032714319 14140099707793594549071479)
      ·
        refine ⟨21210149561690391823607219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14140099707793594549071479 21210149561690391823607219)
        ·
          refine ⟨31815224342535587735410829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21210149561690391823607219 31815224342535587735410829)
          ·
            refine ⟨11930709128450845400779061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31815224342535587735410829 11930709128450845400779061)
            ·
              refine ⟨1118503980792266756323037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11930709128450845400779061 1118503980792266756323037)
              ·
                refine ⟨419438992797100033621139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1118503980792266756323037 419438992797100033621139)
                ·
                  refine ⟨629158489195650050431709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419438992797100033621139 629158489195650050431709)
                  ·
                    refine ⟨235934433448368768911891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 629158489195650050431709 235934433448368768911891)
                    ·
                      rfl

theorem cell22_689221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 1, 3].length) (baseStart_689221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689221 prefixEnd_689221 := by exact prefixLift 689221
  have htrace : WordTrace (prefixWord ++ tailWord_689221) baseStart_689221 baseEnd_689221 := by
    simpa [prefixWord, tailWord_689221, baseEnd_689221] using wordTrace_append hprefix tailTrace_689221
  have hstable : (prefixWord ++ tailWord_689221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689221).length < 2 ^ (prefixWord ++ tailWord_689221).sum := by decide
  have hdescent : baseEnd_689221 < baseStart_689221 := by decide
  rcases family_descends (prefixWord ++ tailWord_689221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689247 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 3, 4]
def baseStart_689247 : Nat := 118140960795 + 689247 * 2 ^ 59
def prefixEnd_689247 : Nat := 4983230072969 + 3 ^ 40 * 689247 * 2
def baseEnd_689247 : Nat := 235943333779713367761811

theorem tailTrace_689247 : CollatzResearch.WordTrace tailWord_689247 prefixEnd_689247 235943333779713367761811 := by
  unfold tailWord_689247
  simp only [CollatzResearch.WordTrace]
  refine ⟨25138903333983307861017995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16759268889322205240678663 25138903333983307861017995)
  ·
    refine ⟨37708355000974961791526993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25138903333983307861017995 37708355000974961791526993)
    ·
      refine ⟨28281266250731221343645245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37708355000974961791526993 28281266250731221343645245)
      ·
        refine ⟨10605474844024208003866967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28281266250731221343645245 10605474844024208003866967)
        ·
          refine ⟨15908212266036312005800451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10605474844024208003866967 15908212266036312005800451)
          ·
            refine ⟨23862318399054468008700677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15908212266036312005800451 23862318399054468008700677)
            ·
              refine ⟨4474184699822712751631377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23862318399054468008700677 4474184699822712751631377)
              ·
                refine ⟨3355638524867034563723533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4474184699822712751631377 3355638524867034563723533)
                ·
                  refine ⟨1258364446825137961396325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3355638524867034563723533 1258364446825137961396325)
                  ·
                    refine ⟨235943333779713367761811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1258364446825137961396325 235943333779713367761811)
                    ·
                      rfl

theorem cell22_689247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 4].length) (baseStart_689247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689247 prefixEnd_689247 := by exact prefixLift 689247
  have htrace : WordTrace (prefixWord ++ tailWord_689247) baseStart_689247 baseEnd_689247 := by
    simpa [prefixWord, tailWord_689247, baseEnd_689247] using wordTrace_append hprefix tailTrace_689247
  have hstable : (prefixWord ++ tailWord_689247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689247).length < 2 ^ (prefixWord ++ tailWord_689247).sum := by decide
  have hdescent : baseEnd_689247 < baseStart_689247 := by decide
  rcases family_descends (prefixWord ++ tailWord_689247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689311 : List Nat := [1, 1, 2, 6, 2, 1, 2, 1, 1, 5]
def baseStart_689311 : Nat := 118140960795 + 689311 * 2 ^ 59
def prefixEnd_689311 : Nat := 4983230072969 + 3 ^ 40 * 689311 * 2
def baseEnd_689311 : Nat := 235965242287638534161615

theorem tailTrace_689311 : CollatzResearch.WordTrace tailWord_689311 prefixEnd_689311 235965242287638534161615 := by
  unfold tailWord_689311
  simp only [CollatzResearch.WordTrace]
  refine ⟨25141237605751446791347787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16760825070500964527565191 25141237605751446791347787)
  ·
    refine ⟨37711856408627170187021681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25141237605751446791347787 37711856408627170187021681)
    ·
      refine ⟨28283892306470377640266261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37711856408627170187021681 28283892306470377640266261)
      ·
        refine ⟨1325807451865798951887481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28283892306470377640266261 1325807451865798951887481)
        ·
          refine ⟨994355588899349213915611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1325807451865798951887481 994355588899349213915611)
          ·
            refine ⟨1491533383349023820873417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994355588899349213915611 1491533383349023820873417)
            ·
              refine ⟨1118650037511767865655063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1491533383349023820873417 1118650037511767865655063)
              ·
                refine ⟨1677975056267651798482595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1118650037511767865655063 1677975056267651798482595)
                ·
                  refine ⟨2516962584401477697723893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1677975056267651798482595 2516962584401477697723893)
                  ·
                    refine ⟨235965242287638534161615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2516962584401477697723893 235965242287638534161615)
                    ·
                      rfl

theorem cell22_689311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 5].length) (baseStart_689311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689311 prefixEnd_689311 := by exact prefixLift 689311
  have htrace : WordTrace (prefixWord ++ tailWord_689311) baseStart_689311 baseEnd_689311 := by
    simpa [prefixWord, tailWord_689311, baseEnd_689311] using wordTrace_append hprefix tailTrace_689311
  have hstable : (prefixWord ++ tailWord_689311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689311).length < 2 ^ (prefixWord ++ tailWord_689311).sum := by decide
  have hdescent : baseEnd_689311 < baseStart_689311 := by decide
  rcases family_descends (prefixWord ++ tailWord_689311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689345 : List Nat := [1, 2, 6, 1, 1, 3, 1, 2, 2, 3]
def baseStart_689345 : Nat := 118140960795 + 689345 * 2 ^ 59
def prefixEnd_689345 : Nat := 4983230072969 + 3 ^ 40 * 689345 * 2
def baseEnd_689345 : Nat := 235976881182473778811511

theorem tailTrace_689345 : CollatzResearch.WordTrace tailWord_689345 prefixEnd_689345 235976881182473778811511 := by
  unfold tailWord_689345
  simp only [CollatzResearch.WordTrace]
  refine ⟨25142477687628270598085489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16761651791752180398723659 25142477687628270598085489)
  ·
    refine ⟨18856858265721202948564117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25142477687628270598085489 18856858265721202948564117)
    ·
      refine ⟨883915231205681388213943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18856858265721202948564117 883915231205681388213943)
      ·
        refine ⟨1325872846808522082320915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 883915231205681388213943 1325872846808522082320915)
        ·
          refine ⟨1988809270212783123481373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1325872846808522082320915 1988809270212783123481373)
          ·
            refine ⟨745803476329793671305515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1988809270212783123481373 745803476329793671305515)
            ·
              refine ⟨1118705214494690506958273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 745803476329793671305515 1118705214494690506958273)
              ·
                refine ⟨839028910871017880218705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1118705214494690506958273 839028910871017880218705)
                ·
                  refine ⟨629271683153263410164029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 839028910871017880218705 629271683153263410164029)
                  ·
                    refine ⟨235976881182473778811511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 629271683153263410164029 235976881182473778811511)
                    ·
                      rfl

theorem cell22_689345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_689345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689345 prefixEnd_689345 := by exact prefixLift 689345
  have htrace : WordTrace (prefixWord ++ tailWord_689345) baseStart_689345 baseEnd_689345 := by
    simpa [prefixWord, tailWord_689345, baseEnd_689345] using wordTrace_append hprefix tailTrace_689345
  have hstable : (prefixWord ++ tailWord_689345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689345).length < 2 ^ (prefixWord ++ tailWord_689345).sum := by decide
  have hdescent : baseEnd_689345 < baseStart_689345 := by decide
  rcases family_descends (prefixWord ++ tailWord_689345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689429 : List Nat := [1, 3, 2, 1, 2, 1, 1, 5, 1, 5]
def baseStart_689429 : Nat := 118140960795 + 689429 * 2 ^ 59
def prefixEnd_689429 : Nat := 4983230072969 + 3 ^ 40 * 689429 * 2
def baseEnd_689429 : Nat := 236005636099125559711253

theorem tailTrace_689429 : CollatzResearch.WordTrace tailWord_689429 prefixEnd_689429 236005636099125559711253 := by
  unfold tailWord_689429
  simp only [CollatzResearch.WordTrace]
  refine ⟨25145541419323952944143341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16763694279549301962762227 25145541419323952944143341)
  ·
    refine ⟨9429578032246482354053753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25145541419323952944143341 9429578032246482354053753)
    ·
      refine ⟨7072183524184861765540315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9429578032246482354053753 7072183524184861765540315)
      ·
        refine ⟨10608275286277292648310473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7072183524184861765540315 10608275286277292648310473)
        ·
          refine ⟨7956206464707969486232855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10608275286277292648310473 7956206464707969486232855)
          ·
            refine ⟨11934309697061954229349283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7956206464707969486232855 11934309697061954229349283)
            ·
              refine ⟨17901464545592931344023925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11934309697061954229349283 17901464545592931344023925)
              ·
                refine ⟨1678262301149337313502243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17901464545592931344023925 1678262301149337313502243)
                ·
                  refine ⟨2517393451724005970253365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1678262301149337313502243 2517393451724005970253365)
                  ·
                    refine ⟨236005636099125559711253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2517393451724005970253365 236005636099125559711253)
                    ·
                      rfl

theorem cell22_689429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_689429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689429 prefixEnd_689429 := by exact prefixLift 689429
  have htrace : WordTrace (prefixWord ++ tailWord_689429) baseStart_689429 baseEnd_689429 := by
    simpa [prefixWord, tailWord_689429, baseEnd_689429] using wordTrace_append hprefix tailTrace_689429
  have hstable : (prefixWord ++ tailWord_689429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689429).length < 2 ^ (prefixWord ++ tailWord_689429).sum := by decide
  have hdescent : baseEnd_689429 < baseStart_689429 := by decide
  rcases family_descends (prefixWord ++ tailWord_689429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689450 : List Nat := [3, 1, 4, 2, 1, 2, 3, 1, 1, 4]
def baseStart_689450 : Nat := 118140960795 + 689450 * 2 ^ 59
def prefixEnd_689450 : Nat := 4983230072969 + 3 ^ 40 * 689450 * 2
def baseEnd_689450 : Nat := 236012824828288504936189

theorem tailTrace_689450 : CollatzResearch.WordTrace tailWord_689450 prefixEnd_689450 236012824828288504936189 := by
  unfold tailWord_689450
  simp only [CollatzResearch.WordTrace]
  refine ⟨6286576838061968382664451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16764204901498582353771869 6286576838061968382664451)
  ·
    refine ⟨9429865257092952573996677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6286576838061968382664451 9429865257092952573996677)
    ·
      refine ⟨1768099735704928607624377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9429865257092952573996677 1768099735704928607624377)
      ·
        refine ⟨1326074801778696455718283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1768099735704928607624377 1326074801778696455718283)
        ·
          refine ⟨1989112202668044683577425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1326074801778696455718283 1989112202668044683577425)
          ·
            refine ⟨1491834152001033512683069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1989112202668044683577425 1491834152001033512683069)
            ·
              refine ⟨559437807000387567256151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1491834152001033512683069 559437807000387567256151)
              ·
                refine ⟨839156710500581350884227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 559437807000387567256151 839156710500581350884227)
                ·
                  refine ⟨1258735065750872026326341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839156710500581350884227 1258735065750872026326341)
                  ·
                    refine ⟨236012824828288504936189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1258735065750872026326341 236012824828288504936189)
                    ·
                      rfl

theorem cell22_689450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_689450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689450 prefixEnd_689450 := by exact prefixLift 689450
  have htrace : WordTrace (prefixWord ++ tailWord_689450) baseStart_689450 baseEnd_689450 := by
    simpa [prefixWord, tailWord_689450, baseEnd_689450] using wordTrace_append hprefix tailTrace_689450
  have hstable : (prefixWord ++ tailWord_689450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689450).length < 2 ^ (prefixWord ++ tailWord_689450).sum := by decide
  have hdescent : baseEnd_689450 < baseStart_689450 := by decide
  rcases family_descends (prefixWord ++ tailWord_689450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689461 : List Nat := [1, 3, 3, 1, 2, 2, 2, 2, 2, 4]
def baseStart_689461 : Nat := 118140960795 + 689461 * 2 ^ 59
def prefixEnd_689461 : Nat := 4983230072969 + 3 ^ 40 * 689461 * 2
def baseEnd_689461 : Nat := 236016590353088142911155

theorem tailTrace_689461 : CollatzResearch.WordTrace tailWord_689461 prefixEnd_689461 236016590353088142911155 := by
  unfold tailWord_689461
  simp only [CollatzResearch.WordTrace]
  refine ⟨25146708555208022409308237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16764472370138681606205491 25146708555208022409308237)
  ·
    refine ⟨9430015708203008403490589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25146708555208022409308237 9430015708203008403490589)
    ·
      refine ⟨3536255890576128151308971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9430015708203008403490589 3536255890576128151308971)
      ·
        refine ⟨5304383835864192226963457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3536255890576128151308971 5304383835864192226963457)
        ·
          refine ⟨3978287876898144170222593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5304383835864192226963457 3978287876898144170222593)
          ·
            refine ⟨2983715907673608127666945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3978287876898144170222593 2983715907673608127666945)
            ·
              refine ⟨2237786930755206095750209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2983715907673608127666945 2237786930755206095750209)
              ·
                refine ⟨1678340198066404571812657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2237786930755206095750209 1678340198066404571812657)
                ·
                  refine ⟨1258755148549803428859493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1678340198066404571812657 1258755148549803428859493)
                  ·
                    refine ⟨236016590353088142911155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1258755148549803428859493 236016590353088142911155)
                    ·
                      rfl

theorem cell22_689461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_689461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689461 prefixEnd_689461 := by exact prefixLift 689461
  have htrace : WordTrace (prefixWord ++ tailWord_689461) baseStart_689461 baseEnd_689461 := by
    simpa [prefixWord, tailWord_689461, baseEnd_689461] using wordTrace_append hprefix tailTrace_689461
  have hstable : (prefixWord ++ tailWord_689461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689461).length < 2 ^ (prefixWord ++ tailWord_689461).sum := by decide
  have hdescent : baseEnd_689461 < baseStart_689461 := by decide
  rcases family_descends (prefixWord ++ tailWord_689461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689489 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 2, 6]
def baseStart_689489 : Nat := 118140960795 + 689489 * 2 ^ 59
def prefixEnd_689489 : Nat := 4983230072969 + 3 ^ 40 * 689489 * 2
def baseEnd_689489 : Nat := 236026175325305403211069

theorem tailTrace_689489 : CollatzResearch.WordTrace tailWord_689489 prefixEnd_689489 236026175325305403211069 := by
  unfold tailWord_689489
  simp only [CollatzResearch.WordTrace]
  refine ⟨25147729799106583191327521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16765153199404388794218347 25147729799106583191327521)
  ·
    refine ⟨18860797349329937393495641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25147729799106583191327521 18860797349329937393495641)
    ·
      refine ⟨14145598011997453045121731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18860797349329937393495641 14145598011997453045121731)
      ·
        refine ⟨21218397017996179567682597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14145598011997453045121731 21218397017996179567682597)
        ·
          refine ⟨3978449440874283668940487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21218397017996179567682597 3978449440874283668940487)
          ·
            refine ⟨5967674161311425503410731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3978449440874283668940487 5967674161311425503410731)
            ·
              refine ⟨8951511241967138255116097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5967674161311425503410731 8951511241967138255116097)
              ·
                refine ⟨6713633431475353691337073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8951511241967138255116097 6713633431475353691337073)
                ·
                  refine ⟨5035225073606515268502805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6713633431475353691337073 5035225073606515268502805)
                  ·
                    refine ⟨236026175325305403211069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5035225073606515268502805 236026175325305403211069)
                    ·
                      rfl

theorem cell22_689489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_689489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689489 prefixEnd_689489 := by exact prefixLift 689489
  have htrace : WordTrace (prefixWord ++ tailWord_689489) baseStart_689489 baseEnd_689489 := by
    simpa [prefixWord, tailWord_689489, baseEnd_689489] using wordTrace_append hprefix tailTrace_689489
  have hstable : (prefixWord ++ tailWord_689489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689489).length < 2 ^ (prefixWord ++ tailWord_689489).sum := by decide
  have hdescent : baseEnd_689489 < baseStart_689489 := by decide
  rcases family_descends (prefixWord ++ tailWord_689489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689491 : List Nat := [1, 1, 1, 2, 1, 1, 7, 2, 3, 3]
def baseStart_689491 : Nat := 118140960795 + 689491 * 2 ^ 59
def prefixEnd_689491 : Nat := 4983230072969 + 3 ^ 40 * 689491 * 2
def baseEnd_689491 : Nat := 236026859966178064661063

theorem tailTrace_689491 : CollatzResearch.WordTrace tailWord_689491 prefixEnd_689491 236026859966178064661063 := by
  unfold tailWord_689491
  simp only [CollatzResearch.WordTrace]
  refine ⟨25147802745099337532900327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16765201830066225021933551 25147802745099337532900327)
  ·
    refine ⟨37721704117649006299350491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25147802745099337532900327 37721704117649006299350491)
    ·
      refine ⟨56582556176473509449025737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37721704117649006299350491 56582556176473509449025737)
      ·
        refine ⟨42436917132355132086769303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56582556176473509449025737 42436917132355132086769303)
        ·
          refine ⟨63655375698532698130153955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42436917132355132086769303 63655375698532698130153955)
          ·
            refine ⟨95483063547799047195230933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63655375698532698130153955 95483063547799047195230933)
            ·
              refine ⟨2237884301901540168638225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 95483063547799047195230933 2237884301901540168638225)
              ·
                refine ⟨1678413226426155126478669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2237884301901540168638225 1678413226426155126478669)
                ·
                  refine ⟨629404959909808172429501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1678413226426155126478669 629404959909808172429501)
                  ·
                    refine ⟨236026859966178064661063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 629404959909808172429501 236026859966178064661063)
                    ·
                      rfl

theorem cell22_689491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 3].length) (baseStart_689491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689491 prefixEnd_689491 := by exact prefixLift 689491
  have htrace : WordTrace (prefixWord ++ tailWord_689491) baseStart_689491 baseEnd_689491 := by
    simpa [prefixWord, tailWord_689491, baseEnd_689491] using wordTrace_append hprefix tailTrace_689491
  have hstable : (prefixWord ++ tailWord_689491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689491).length < 2 ^ (prefixWord ++ tailWord_689491).sum := by decide
  have hdescent : baseEnd_689491 < baseStart_689491 := by decide
  rcases family_descends (prefixWord ++ tailWord_689491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689501 : List Nat := [1, 4, 5, 1, 2, 1, 2, 1, 1, 4]
def baseStart_689501 : Nat := 118140960795 + 689501 * 2 ^ 59
def prefixEnd_689501 : Nat := 4983230072969 + 3 ^ 40 * 689501 * 2
def baseEnd_689501 : Nat := 236030283170541371911033

theorem tailTrace_689501 : CollatzResearch.WordTrace tailWord_689501 prefixEnd_689501 236030283170541371911033 := by
  unfold tailWord_689501
  simp only [CollatzResearch.WordTrace]
  refine ⟨25148167475063109240764357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16765444983375406160509571 25148167475063109240764357)
  ·
    refine ⟨4715281401574332982643317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25148167475063109240764357 4715281401574332982643317)
    ·
      refine ⟨442057631397593717122811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4715281401574332982643317 442057631397593717122811)
      ·
        refine ⟨663086447096390575684217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442057631397593717122811 663086447096390575684217)
        ·
          refine ⟨497314835322292931763163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 663086447096390575684217 497314835322292931763163)
          ·
            refine ⟨745972252983439397644745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497314835322292931763163 745972252983439397644745)
            ·
              refine ⟨559479189737579548233559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 745972252983439397644745 559479189737579548233559)
              ·
                refine ⟨839218784606369322350339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 559479189737579548233559 839218784606369322350339)
                ·
                  refine ⟨1258828176909553983525509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839218784606369322350339 1258828176909553983525509)
                  ·
                    refine ⟨236030283170541371911033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1258828176909553983525509 236030283170541371911033)
                    ·
                      rfl

theorem cell22_689501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_689501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689501 prefixEnd_689501 := by exact prefixLift 689501
  have htrace : WordTrace (prefixWord ++ tailWord_689501) baseStart_689501 baseEnd_689501 := by
    simpa [prefixWord, tailWord_689501, baseEnd_689501] using wordTrace_append hprefix tailTrace_689501
  have hstable : (prefixWord ++ tailWord_689501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689501).length < 2 ^ (prefixWord ++ tailWord_689501).sum := by decide
  have hdescent : baseEnd_689501 < baseStart_689501 := by decide
  rcases family_descends (prefixWord ++ tailWord_689501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689519 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 4, 5]
def baseStart_689519 : Nat := 118140960795 + 689519 * 2 ^ 59
def prefixEnd_689519 : Nat := 4983230072969 + 3 ^ 40 * 689519 * 2
def baseEnd_689519 : Nat := 236036444938395324960977

theorem tailTrace_689519 : CollatzResearch.WordTrace tailWord_689519 prefixEnd_689519 236036444938395324960977 := by
  unfold tailWord_689519
  simp only [CollatzResearch.WordTrace]
  refine ⟨25148823988997898314919611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16765882659331932209946407 25148823988997898314919611)
  ·
    refine ⟨37723235983496847472379417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25148823988997898314919611 37723235983496847472379417)
    ·
      refine ⟨28292426987622635604284563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37723235983496847472379417 28292426987622635604284563)
      ·
        refine ⟨42438640481433953406426845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28292426987622635604284563 42438640481433953406426845)
        ·
          refine ⟨15914490180537732527410067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42438640481433953406426845 15914490180537732527410067)
          ·
            refine ⟨23871735270806598791115101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15914490180537732527410067 23871735270806598791115101)
            ·
              refine ⟨8951900726552474546668163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23871735270806598791115101 8951900726552474546668163)
              ·
                refine ⟨13427851089828711820002245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8951900726552474546668163 13427851089828711820002245)
                ·
                  refine ⟨2517722079342883466250421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13427851089828711820002245 2517722079342883466250421)
                  ·
                    refine ⟨236036444938395324960977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2517722079342883466250421 236036444938395324960977)
                    ·
                      rfl

theorem cell22_689519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_689519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689519 prefixEnd_689519 := by exact prefixLift 689519
  have htrace : WordTrace (prefixWord ++ tailWord_689519) baseStart_689519 baseEnd_689519 := by
    simpa [prefixWord, tailWord_689519, baseEnd_689519] using wordTrace_append hprefix tailTrace_689519
  have hstable : (prefixWord ++ tailWord_689519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689519).length < 2 ^ (prefixWord ++ tailWord_689519).sum := by decide
  have hdescent : baseEnd_689519 < baseStart_689519 := by decide
  rcases family_descends (prefixWord ++ tailWord_689519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689521 : List Nat := [1, 2, 2, 2, 1, 2, 5, 2, 5]
def baseStart_689521 : Nat := 118140960795 + 689521 * 2 ^ 59
def prefixEnd_689521 : Nat := 4983230072969 + 3 ^ 40 * 689521 * 2
def baseEnd_689521 : Nat := 78679043193089328803657

theorem tailTrace_689521 : CollatzResearch.WordTrace tailWord_689521 prefixEnd_689521 78679043193089328803657 := by
  unfold tailWord_689521
  simp only [CollatzResearch.WordTrace]
  refine ⟨25148896934990652656492417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16765931289993768437661611 25148896934990652656492417)
  ·
    refine ⟨18861672701242989492369313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25148896934990652656492417 18861672701242989492369313)
    ·
      refine ⟨14146254525932242119276985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18861672701242989492369313 14146254525932242119276985)
      ·
        refine ⟨10609690894449181589457739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14146254525932242119276985 10609690894449181589457739)
        ·
          refine ⟨15914536341673772384186609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10609690894449181589457739 15914536341673772384186609)
          ·
            refine ⟨11935902256255329288139957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15914536341673772384186609 11935902256255329288139957)
            ·
              refine ⟨1118990836523937120763121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11935902256255329288139957 1118990836523937120763121)
              ·
                refine ⟨839243127392952840572341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1118990836523937120763121 839243127392952840572341)
                ·
                  refine ⟨78679043193089328803657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 839243127392952840572341 78679043193089328803657)
                  ·
                    rfl

theorem cell22_689521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 5].length) (baseStart_689521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689521 prefixEnd_689521 := by exact prefixLift 689521
  have htrace : WordTrace (prefixWord ++ tailWord_689521) baseStart_689521 baseEnd_689521 := by
    simpa [prefixWord, tailWord_689521, baseEnd_689521] using wordTrace_append hprefix tailTrace_689521
  have hstable : (prefixWord ++ tailWord_689521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689521).length < 2 ^ (prefixWord ++ tailWord_689521).sum := by decide
  have hdescent : baseEnd_689521 < baseStart_689521 := by decide
  rcases family_descends (prefixWord ++ tailWord_689521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689525 : List Nat := [1, 3, 4, 1, 3, 1, 2, 1, 3, 3]
def baseStart_689525 : Nat := 118140960795 + 689525 * 2 ^ 59
def prefixEnd_689525 : Nat := 4983230072969 + 3 ^ 40 * 689525 * 2
def baseEnd_689525 : Nat := 236038498861013309310959

theorem tailTrace_689525 : CollatzResearch.WordTrace tailWord_689525 prefixEnd_689525 236038498861013309310959 := by
  unfold tailWord_689525
  simp only [CollatzResearch.WordTrace]
  refine ⟨25149042826976161339638029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16766028551317440893092019 25149042826976161339638029)
  ·
    refine ⟨9430891060116060502364261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25149042826976161339638029 9430891060116060502364261)
    ·
      refine ⟨1768292073771761344193299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9430891060116060502364261 1768292073771761344193299)
      ·
        refine ⟨2652438110657642016289949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1768292073771761344193299 2652438110657642016289949)
        ·
          refine ⟨994664291496615756108731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2652438110657642016289949 994664291496615756108731)
          ·
            refine ⟨1491996437244923634163097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994664291496615756108731 1491996437244923634163097)
            ·
              refine ⟨1118997327933692725622323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1491996437244923634163097 1118997327933692725622323)
              ·
                refine ⟨1678495991900539088433485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1118997327933692725622323 1678495991900539088433485)
                ·
                  refine ⟨629435996962702158162557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1678495991900539088433485 629435996962702158162557)
                  ·
                    refine ⟨236038498861013309310959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 629435996962702158162557 236038498861013309310959)
                    ·
                      rfl

theorem cell22_689525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_689525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689525 prefixEnd_689525 := by exact prefixLift 689525
  have htrace : WordTrace (prefixWord ++ tailWord_689525) baseStart_689525 baseEnd_689525 := by
    simpa [prefixWord, tailWord_689525, baseEnd_689525] using wordTrace_append hprefix tailTrace_689525
  have hstable : (prefixWord ++ tailWord_689525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689525).length < 2 ^ (prefixWord ++ tailWord_689525).sum := by decide
  have hdescent : baseEnd_689525 < baseStart_689525 := by decide
  rcases family_descends (prefixWord ++ tailWord_689525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689645 : List Nat := [1, 5, 1, 3, 2, 2, 1, 7]
def baseStart_689645 : Nat := 118140960795 + 689645 * 2 ^ 59
def prefixEnd_689645 : Nat := 4983230072969 + 3 ^ 40 * 689645 * 2
def baseEnd_689645 : Nat := 26231064145930332923399

theorem tailTrace_689645 : CollatzResearch.WordTrace tailWord_689645 prefixEnd_689645 26231064145930332923399 := by
  unfold tailWord_689645
  simp only [CollatzResearch.WordTrace]
  refine ⟨25153419586541421834006389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16768946391027614556004259 25153419586541421834006389)
  ·
    refine ⟨2358133086238258296938099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25153419586541421834006389 2358133086238258296938099)
    ·
      refine ⟨3537199629357387445407149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2358133086238258296938099 3537199629357387445407149)
      ·
        refine ⟨1326449861009020292027681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3537199629357387445407149 1326449861009020292027681)
        ·
          refine ⟨994837395756765219020761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1326449861009020292027681 994837395756765219020761)
          ·
            refine ⟨746128046817573914265571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 994837395756765219020761 746128046817573914265571)
            ·
              refine ⟨1119192070226360871398357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 746128046817573914265571 1119192070226360871398357)
              ·
                refine ⟨26231064145930332923399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1119192070226360871398357 26231064145930332923399)
                ·
                  rfl

theorem cell22_689645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 7].length) (baseStart_689645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689645 prefixEnd_689645 := by exact prefixLift 689645
  have htrace : WordTrace (prefixWord ++ tailWord_689645) baseStart_689645 baseEnd_689645 := by
    simpa [prefixWord, tailWord_689645, baseEnd_689645] using wordTrace_append hprefix tailTrace_689645
  have hstable : (prefixWord ++ tailWord_689645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689645).length < 2 ^ (prefixWord ++ tailWord_689645).sum := by decide
  have hdescent : baseEnd_689645 < baseStart_689645 := by decide
  rcases family_descends (prefixWord ++ tailWord_689645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689662 : List Nat := [4, 2, 2, 3, 1, 1, 3, 6]
def baseStart_689662 : Nat := 118140960795 + 689662 * 2 ^ 59
def prefixEnd_689662 : Nat := 4983230072969 + 3 ^ 40 * 689662 * 2
def baseEnd_689662 : Nat := 26231710751198957626171

theorem tailTrace_689662 : CollatzResearch.WordTrace tailWord_689662 prefixEnd_689662 26231710751198957626171 := by
  unfold tailWord_689662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3144254953434979217171905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16769359751653222491583493 3144254953434979217171905)
  ·
    refine ⟨2358191215076234412878929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3144254953434979217171905 2358191215076234412878929)
    ·
      refine ⟨1768643411307175809659197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2358191215076234412878929 1768643411307175809659197)
      ·
        refine ⟨663241279240190928622199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1768643411307175809659197 663241279240190928622199)
        ·
          refine ⟨994861918860286392933299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663241279240190928622199 994861918860286392933299)
          ·
            refine ⟨1492292878290429589399949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994861918860286392933299 1492292878290429589399949)
            ·
              refine ⟨559609829358911096024981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1492292878290429589399949 559609829358911096024981)
              ·
                refine ⟨26231710751198957626171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 559609829358911096024981 26231710751198957626171)
                ·
                  rfl

theorem cell22_689662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_689662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689662 prefixEnd_689662 := by exact prefixLift 689662
  have htrace : WordTrace (prefixWord ++ tailWord_689662) baseStart_689662 baseEnd_689662 := by
    simpa [prefixWord, tailWord_689662, baseEnd_689662] using wordTrace_append hprefix tailTrace_689662
  have hstable : (prefixWord ++ tailWord_689662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689662).length < 2 ^ (prefixWord ++ tailWord_689662).sum := by decide
  have hdescent : baseEnd_689662 < baseStart_689662 := by decide
  rcases family_descends (prefixWord ++ tailWord_689662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689720 : List Nat := [2, 1, 2, 1, 4, 3, 2, 2, 1, 4]
def baseStart_689720 : Nat := 118140960795 + 689720 * 2 ^ 59
def prefixEnd_689720 : Nat := 4983230072969 + 3 ^ 40 * 689720 * 2
def baseEnd_689720 : Nat := 236105251346097800685361

theorem tailTrace_689720 : CollatzResearch.WordTrace tailWord_689720 prefixEnd_689720 236105251346097800685361 := by
  unfold tailWord_689720
  simp only [CollatzResearch.WordTrace]
  refine ⟨12578077530634854821493307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16770770040846473095324409 12578077530634854821493307)
  ·
    refine ⟨18867116295952282232239961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12578077530634854821493307 18867116295952282232239961)
    ·
      refine ⟨14150337221964211674179971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18867116295952282232239961 14150337221964211674179971)
      ·
        refine ⟨21225505832946317511269957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14150337221964211674179971 21225505832946317511269957)
        ·
          refine ⟨3979782343677434533363117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21225505832946317511269957 3979782343677434533363117)
          ·
            refine ⟨1492418378879037950011169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3979782343677434533363117 1492418378879037950011169)
            ·
              refine ⟨1119313784159278462508377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1492418378879037950011169 1119313784159278462508377)
              ·
                refine ⟨839485338119458846881283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1119313784159278462508377 839485338119458846881283)
                ·
                  refine ⟨1259228007179188270321925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839485338119458846881283 1259228007179188270321925)
                  ·
                    refine ⟨236105251346097800685361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1259228007179188270321925 236105251346097800685361)
                    ·
                      rfl

theorem cell22_689720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_689720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689720 prefixEnd_689720 := by exact prefixLift 689720
  have htrace : WordTrace (prefixWord ++ tailWord_689720) baseStart_689720 baseEnd_689720 := by
    simpa [prefixWord, tailWord_689720, baseEnd_689720] using wordTrace_append hprefix tailTrace_689720
  have hstable : (prefixWord ++ tailWord_689720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689720).length < 2 ^ (prefixWord ++ tailWord_689720).sum := by decide
  have hdescent : baseEnd_689720 < baseStart_689720 := by decide
  rcases family_descends (prefixWord ++ tailWord_689720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689733 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 6, 3]
def baseStart_689733 : Nat := 118140960795 + 689733 * 2 ^ 59
def prefixEnd_689733 : Nat := 4983230072969 + 3 ^ 40 * 689733 * 2
def baseEnd_689733 : Nat := 236109701511770100110321

theorem tailTrace_689733 : CollatzResearch.WordTrace tailWord_689733 prefixEnd_689733 236109701511770100110321 := by
  unfold tailWord_689733
  simp only [CollatzResearch.WordTrace]
  refine ⟨25156629210222612863209853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16771086140148408575473235 25156629210222612863209853)
  ·
    refine ⟨9433735953833479823703695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25156629210222612863209853 9433735953833479823703695)
    ·
      refine ⟨14150603930750219735555543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9433735953833479823703695 14150603930750219735555543)
      ·
        refine ⟨21225905896125329603333315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14150603930750219735555543 21225905896125329603333315)
        ·
          refine ⟨31838858844187994404999973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21225905896125329603333315 31838858844187994404999973)
          ·
            refine ⟨5969786033285248950937495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31838858844187994404999973 5969786033285248950937495)
            ·
              refine ⟨8954679049927873426406243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5969786033285248950937495 8954679049927873426406243)
              ·
                refine ⟨13432018574891810139609365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8954679049927873426406243 13432018574891810139609365)
                ·
                  refine ⟨629625870698053600294189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13432018574891810139609365 629625870698053600294189)
                  ·
                    refine ⟨236109701511770100110321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 629625870698053600294189 236109701511770100110321)
                    ·
                      rfl

theorem cell22_689733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_689733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689733 prefixEnd_689733 := by exact prefixLift 689733
  have htrace : WordTrace (prefixWord ++ tailWord_689733) baseStart_689733 baseEnd_689733 := by
    simpa [prefixWord, tailWord_689733, baseEnd_689733] using wordTrace_append hprefix tailTrace_689733
  have hstable : (prefixWord ++ tailWord_689733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689733).length < 2 ^ (prefixWord ++ tailWord_689733).sum := by decide
  have hdescent : baseEnd_689733 < baseStart_689733 := by decide
  rcases family_descends (prefixWord ++ tailWord_689733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689763 : List Nat := [1, 1, 1, 5, 1, 4, 2, 7]
def baseStart_689763 : Nat := 118140960795 + 689763 * 2 ^ 59
def prefixEnd_689763 : Nat := 4983230072969 + 3 ^ 40 * 689763 * 2
def baseEnd_689763 : Nat := 26235552347206669095581

theorem tailTrace_689763 : CollatzResearch.WordTrace tailWord_689763 prefixEnd_689763 26235552347206669095581 := by
  unfold tailWord_689763
  simp only [CollatzResearch.WordTrace]
  refine ⟨25157723400113927986801943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16771815600075951991201295 25157723400113927986801943)
  ·
    refine ⟨37736585100170891980202915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25157723400113927986801943 37736585100170891980202915)
    ·
      refine ⟨56604877650256337970304373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37736585100170891980202915 56604877650256337970304373)
      ·
        refine ⟨5306707279711531684716035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56604877650256337970304373 5306707279711531684716035)
        ·
          refine ⟨7960060919567297527074053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5306707279711531684716035 7960060919567297527074053)
          ·
            refine ⟨1492511422418868286326385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7960060919567297527074053 1492511422418868286326385)
            ·
              refine ⟨1119383566814151214744789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1492511422418868286326385 1119383566814151214744789)
              ·
                refine ⟨26235552347206669095581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1119383566814151214744789 26235552347206669095581)
                ·
                  rfl

theorem cell22_689763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 7].length) (baseStart_689763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689763 prefixEnd_689763 := by exact prefixLift 689763
  have htrace : WordTrace (prefixWord ++ tailWord_689763) baseStart_689763 baseEnd_689763 := by
    simpa [prefixWord, tailWord_689763, baseEnd_689763] using wordTrace_append hprefix tailTrace_689763
  have hstable : (prefixWord ++ tailWord_689763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689763).length < 2 ^ (prefixWord ++ tailWord_689763).sum := by decide
  have hdescent : baseEnd_689763 < baseStart_689763 := by decide
  rcases family_descends (prefixWord ++ tailWord_689763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689767 : List Nat := [1, 1, 5, 1, 1, 1, 6, 1, 2, 3]
def baseStart_689767 : Nat := 118140960795 + 689767 * 2 ^ 59
def prefixEnd_689767 : Nat := 4983230072969 + 3 ^ 40 * 689767 * 2
def baseEnd_689767 : Nat := 236121340406605344760217

theorem tailTrace_689767 : CollatzResearch.WordTrace tailWord_689767 prefixEnd_689767 236121340406605344760217 := by
  unfold tailWord_689767
  simp only [CollatzResearch.WordTrace]
  refine ⟨25157869292099436669947555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16771912861399624446631703 25157869292099436669947555)
  ·
    refine ⟨37736803938149155004921333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25157869292099436669947555 37736803938149155004921333)
    ·
      refine ⟨3537825369201483281711375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37736803938149155004921333 3537825369201483281711375)
      ·
        refine ⟨5306738053802224922567063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3537825369201483281711375 5306738053802224922567063)
        ·
          refine ⟨7960107080703337383850595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5306738053802224922567063 7960107080703337383850595)
          ·
            refine ⟨11940160621055006075775893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7960107080703337383850595 11940160621055006075775893)
            ·
              refine ⟨559695029111953409801995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11940160621055006075775893 559695029111953409801995)
              ·
                refine ⟨839542543667930114702993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 559695029111953409801995 839542543667930114702993)
                ·
                  refine ⟨629656907750947586027245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 839542543667930114702993 629656907750947586027245)
                  ·
                    refine ⟨236121340406605344760217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 629656907750947586027245 236121340406605344760217)
                    ·
                      rfl

theorem cell22_689767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_689767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689767 prefixEnd_689767 := by exact prefixLift 689767
  have htrace : WordTrace (prefixWord ++ tailWord_689767) baseStart_689767 baseEnd_689767 := by
    simpa [prefixWord, tailWord_689767, baseEnd_689767] using wordTrace_append hprefix tailTrace_689767
  have hstable : (prefixWord ++ tailWord_689767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689767).length < 2 ^ (prefixWord ++ tailWord_689767).sum := by decide
  have hdescent : baseEnd_689767 < baseStart_689767 := by decide
  rcases family_descends (prefixWord ++ tailWord_689767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689782 : List Nat := [5, 1, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_689782 : Nat := 118140960795 + 689782 * 2 ^ 59
def prefixEnd_689782 : Nat := 4983230072969 + 3 ^ 40 * 689782 * 2
def baseEnd_689782 : Nat := 236126475213150305635171

theorem tailTrace_689782 : CollatzResearch.WordTrace tailWord_689782 prefixEnd_689782 236126475213150305635171 := by
  unfold tailWord_689782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1572401024190318389483975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16772277591363396154495733 1572401024190318389483975)
  ·
    refine ⟨2358601536285477584225963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1572401024190318389483975 2358601536285477584225963)
    ·
      refine ⟨3537902304428216376338945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2358601536285477584225963 3537902304428216376338945)
      ·
        refine ⟨2653426728321162282254209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3537902304428216376338945 2653426728321162282254209)
        ·
          refine ⟨1990070046240871711690657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2653426728321162282254209 1990070046240871711690657)
          ·
            refine ⟨1492552534680653783767993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1990070046240871711690657 1492552534680653783767993)
            ·
              refine ⟨1119414401010490337825995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1492552534680653783767993 1119414401010490337825995)
              ·
                refine ⟨1679121601515735506738993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1119414401010490337825995 1679121601515735506738993)
                ·
                  refine ⟨1259341201136801630054245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1679121601515735506738993 1259341201136801630054245)
                  ·
                    refine ⟨236126475213150305635171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1259341201136801630054245 236126475213150305635171)
                    ·
                      rfl

theorem cell22_689782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_689782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689782 prefixEnd_689782 := by exact prefixLift 689782
  have htrace : WordTrace (prefixWord ++ tailWord_689782) baseStart_689782 baseEnd_689782 := by
    simpa [prefixWord, tailWord_689782, baseEnd_689782] using wordTrace_append hprefix tailTrace_689782
  have hstable : (prefixWord ++ tailWord_689782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689782).length < 2 ^ (prefixWord ++ tailWord_689782).sum := by decide
  have hdescent : baseEnd_689782 < baseStart_689782 := by decide
  rcases family_descends (prefixWord ++ tailWord_689782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689825 : List Nat := [1, 2, 3, 3, 2, 1, 2, 3, 5]
def baseStart_689825 : Nat := 118140960795 + 689825 * 2 ^ 59
def prefixEnd_689825 : Nat := 4983230072969 + 3 ^ 40 * 689825 * 2
def baseEnd_689825 : Nat := 78713731663970842270013

theorem tailTrace_689825 : CollatzResearch.WordTrace tailWord_689825 prefixEnd_689825 78713731663970842270013 := by
  unfold tailWord_689825
  simp only [CollatzResearch.WordTrace]
  refine ⟨25159984725889312575558929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16773323150592875050372619 25159984725889312575558929)
  ·
    refine ⟨18869988544416984431669197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25159984725889312575558929 18869988544416984431669197)
    ·
      refine ⟨7076245704156369161875949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18869988544416984431669197 7076245704156369161875949)
      ·
        refine ⟨2653592139058638435703481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7076245704156369161875949 2653592139058638435703481)
        ·
          refine ⟨1990194104293978826777611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2653592139058638435703481 1990194104293978826777611)
          ·
            refine ⟨2985291156440968240166417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1990194104293978826777611 2985291156440968240166417)
            ·
              refine ⟨2238968367330726180124813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2985291156440968240166417 2238968367330726180124813)
              ·
                refine ⟨839613137749022317546805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2238968367330726180124813 839613137749022317546805)
                ·
                  refine ⟨78713731663970842270013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 839613137749022317546805 78713731663970842270013)
                  ·
                    rfl

theorem cell22_689825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 5].length) (baseStart_689825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689825 prefixEnd_689825 := by exact prefixLift 689825
  have htrace : WordTrace (prefixWord ++ tailWord_689825) baseStart_689825 baseEnd_689825 := by
    simpa [prefixWord, tailWord_689825, baseEnd_689825] using wordTrace_append hprefix tailTrace_689825
  have hstable : (prefixWord ++ tailWord_689825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689825).length < 2 ^ (prefixWord ++ tailWord_689825).sum := by decide
  have hdescent : baseEnd_689825 < baseStart_689825 := by decide
  rcases family_descends (prefixWord ++ tailWord_689825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689846 : List Nat := [5, 1, 3, 1, 1, 1, 1, 5, 1, 3]
def baseStart_689846 : Nat := 118140960795 + 689846 * 2 ^ 59
def prefixEnd_689846 : Nat := 4983230072969 + 3 ^ 40 * 689846 * 2
def baseEnd_689846 : Nat := 236148383721075472034975

theorem tailTrace_689846 : CollatzResearch.WordTrace tailWord_689846 prefixEnd_689846 236148383721075472034975 := by
  unfold tailWord_689846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1572546916175827072629587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16773833772542155441382261 1572546916175827072629587)
  ·
    refine ⟨2358820374263740608944381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1572546916175827072629587 2358820374263740608944381)
    ·
      refine ⟨884557640348902728354143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2358820374263740608944381 884557640348902728354143)
      ·
        refine ⟨1326836460523354092531215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 884557640348902728354143 1326836460523354092531215)
        ·
          refine ⟨1990254690785031138796823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1326836460523354092531215 1990254690785031138796823)
          ·
            refine ⟨2985382036177546708195235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1990254690785031138796823 2985382036177546708195235)
            ·
              refine ⟨4478073054266320062292853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2985382036177546708195235 4478073054266320062292853)
              ·
                refine ⟨419819348837467505839955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4478073054266320062292853 419819348837467505839955)
                ·
                  refine ⟨629729023256201258759933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419819348837467505839955 629729023256201258759933)
                  ·
                    refine ⟨236148383721075472034975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 629729023256201258759933 236148383721075472034975)
                    ·
                      rfl

theorem cell22_689846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_689846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689846 prefixEnd_689846 := by exact prefixLift 689846
  have htrace : WordTrace (prefixWord ++ tailWord_689846) baseStart_689846 baseEnd_689846 := by
    simpa [prefixWord, tailWord_689846, baseEnd_689846] using wordTrace_append hprefix tailTrace_689846
  have hstable : (prefixWord ++ tailWord_689846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689846).length < 2 ^ (prefixWord ++ tailWord_689846).sum := by decide
  have hdescent : baseEnd_689846 < baseStart_689846 := by decide
  rcases family_descends (prefixWord ++ tailWord_689846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689853 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 8]
def baseStart_689853 : Nat := 118140960795 + 689853 * 2 ^ 59
def prefixEnd_689853 : Nat := 4983230072969 + 3 ^ 40 * 689853 * 2
def baseEnd_689853 : Nat := 78716926654709929036651

theorem tailTrace_689853 : CollatzResearch.WordTrace tailWord_689853 prefixEnd_689853 78716926654709929036651 := by
  unfold tailWord_689853
  simp only [CollatzResearch.WordTrace]
  refine ⟨25161005969787873357578213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16774003979858582238385475 25161005969787873357578213)
  ·
    refine ⟨4717688619335226254545915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25161005969787873357578213 4717688619335226254545915)
    ·
      refine ⟨7076532929002839381818873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4717688619335226254545915 7076532929002839381818873)
      ·
        refine ⟨5307399696752129536364155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7076532929002839381818873 5307399696752129536364155)
        ·
          refine ⟨7961099545128194304546233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5307399696752129536364155 7961099545128194304546233)
          ·
            refine ⟨5970824658846145728409675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7961099545128194304546233 5970824658846145728409675)
            ·
              refine ⟨8956236988269218592614513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5970824658846145728409675 8956236988269218592614513)
              ·
                refine ⟨6717177741201913944460885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8956236988269218592614513 6717177741201913944460885)
                ·
                  refine ⟨78716926654709929036651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6717177741201913944460885 78716926654709929036651)
                  ·
                    rfl

theorem cell22_689853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_689853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689853 prefixEnd_689853 := by exact prefixLift 689853
  have htrace : WordTrace (prefixWord ++ tailWord_689853) baseStart_689853 baseEnd_689853 := by
    simpa [prefixWord, tailWord_689853, baseEnd_689853] using wordTrace_append hprefix tailTrace_689853
  have hstable : (prefixWord ++ tailWord_689853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689853).length < 2 ^ (prefixWord ++ tailWord_689853).sum := by decide
  have hdescent : baseEnd_689853 < baseStart_689853 := by decide
  rcases family_descends (prefixWord ++ tailWord_689853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689855 : List Nat := [1, 1, 2, 2, 2, 3, 3, 3, 1, 4]
def baseStart_689855 : Nat := 118140960795 + 689855 * 2 ^ 59
def prefixEnd_689855 : Nat := 4983230072969 + 3 ^ 40 * 689855 * 2
def baseEnd_689855 : Nat := 236151464605002448559947

theorem tailTrace_689855 : CollatzResearch.WordTrace tailWord_689855 prefixEnd_689855 236151464605002448559947 := by
  unfold tailWord_689855
  simp only [CollatzResearch.WordTrace]
  refine ⟨25161078915780627699151019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16774052610520418466100679 25161078915780627699151019)
  ·
    refine ⟨37741618373670941548726529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25161078915780627699151019 37741618373670941548726529)
    ·
      refine ⟨28306213780253206161544897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37741618373670941548726529 28306213780253206161544897)
      ·
        refine ⟨21229660335189904621158673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28306213780253206161544897 21229660335189904621158673)
        ·
          refine ⟨15922245251392428465869005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21229660335189904621158673 15922245251392428465869005)
          ·
            refine ⟨5970841969272160674700877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15922245251392428465869005 5970841969272160674700877)
            ·
              refine ⟨2239065738477060253012829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5970841969272160674700877 2239065738477060253012829)
              ·
                refine ⟨839649651928897594879811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2239065738477060253012829 839649651928897594879811)
                ·
                  refine ⟨1259474477893346392319717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839649651928897594879811 1259474477893346392319717)
                  ·
                    refine ⟨236151464605002448559947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1259474477893346392319717 236151464605002448559947)
                    ·
                      rfl

theorem cell22_689855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 4].length) (baseStart_689855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689855 prefixEnd_689855 := by exact prefixLift 689855
  have htrace : WordTrace (prefixWord ++ tailWord_689855) baseStart_689855 baseEnd_689855 := by
    simpa [prefixWord, tailWord_689855, baseEnd_689855] using wordTrace_append hprefix tailTrace_689855
  have hstable : (prefixWord ++ tailWord_689855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689855).length < 2 ^ (prefixWord ++ tailWord_689855).sum := by decide
  have hdescent : baseEnd_689855 < baseStart_689855 := by decide
  rcases family_descends (prefixWord ++ tailWord_689855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689870 : List Nat := [4, 1, 1, 1, 3, 1, 4, 1, 6]
def baseStart_689870 : Nat := 118140960795 + 689870 * 2 ^ 59
def prefixEnd_689870 : Nat := 4983230072969 + 3 ^ 40 * 689870 * 2
def baseEnd_689870 : Nat := 78718866470515803144967

theorem tailTrace_689870 : CollatzResearch.WordTrace tailWord_689870 prefixEnd_689870 78718866470515803144967 := by
  unfold tailWord_689870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3145203251340785657618383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16774417340484190173964709 3145203251340785657618383)
  ·
    refine ⟨4717804877011178486427575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3145203251340785657618383 4717804877011178486427575)
    ·
      refine ⟨7076707315516767729641363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4717804877011178486427575 7076707315516767729641363)
      ·
        refine ⟨10615060973275151594462045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7076707315516767729641363 10615060973275151594462045)
        ·
          refine ⟨3980647864978181847923267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10615060973275151594462045 3980647864978181847923267)
          ·
            refine ⟨5970971797467272771884901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3980647864978181847923267 5970971797467272771884901)
            ·
              refine ⟨1119557212025113644728419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5970971797467272771884901 1119557212025113644728419)
              ·
                refine ⟨1679335818037670467092629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1119557212025113644728419 1679335818037670467092629)
                ·
                  refine ⟨78718866470515803144967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1679335818037670467092629 78718866470515803144967)
                  ·
                    rfl

theorem cell22_689870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_689870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689870 prefixEnd_689870 := by exact prefixLift 689870
  have htrace : WordTrace (prefixWord ++ tailWord_689870) baseStart_689870 baseEnd_689870 := by
    simpa [prefixWord, tailWord_689870, baseEnd_689870] using wordTrace_append hprefix tailTrace_689870
  have hstable : (prefixWord ++ tailWord_689870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689870).length < 2 ^ (prefixWord ++ tailWord_689870).sum := by decide
  have hdescent : baseEnd_689870 < baseStart_689870 := by decide
  rcases family_descends (prefixWord ++ tailWord_689870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689940 : List Nat := [2, 4, 4, 1, 2, 1, 1, 2, 1, 4]
def baseStart_689940 : Nat := 118140960795 + 689940 * 2 ^ 59
def prefixEnd_689940 : Nat := 4983230072969 + 3 ^ 40 * 689940 * 2
def baseEnd_689940 : Nat := 236180561842090560184687

theorem tailTrace_689940 : CollatzResearch.WordTrace tailWord_689940 prefixEnd_689940 236180561842090560184687 := by
  unfold tailWord_689940
  simp only [CollatzResearch.WordTrace]
  refine ⟨12582089560236343607997637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16776119413648458143996849 12582089560236343607997637)
  ·
    refine ⟨2359141792544314426499557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12582089560236343607997637 2359141792544314426499557)
    ·
      refine ⟨442339086102058954968667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2359141792544314426499557 442339086102058954968667)
      ·
        refine ⟨663508629153088432453001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442339086102058954968667 663508629153088432453001)
        ·
          refine ⟨497631471864816324339751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 663508629153088432453001 497631471864816324339751)
          ·
            refine ⟨746447207797224486509627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497631471864816324339751 746447207797224486509627)
            ·
              refine ⟨1119670811695836729764441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 746447207797224486509627 1119670811695836729764441)
              ·
                refine ⟨839753108771877547323331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1119670811695836729764441 839753108771877547323331)
                ·
                  refine ⟨1259629663157816320984997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839753108771877547323331 1259629663157816320984997)
                  ·
                    refine ⟨236180561842090560184687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1259629663157816320984997 236180561842090560184687)
                    ·
                      rfl

theorem cell22_689940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_689940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689940 prefixEnd_689940 := by exact prefixLift 689940
  have htrace : WordTrace (prefixWord ++ tailWord_689940) baseStart_689940 baseEnd_689940 := by
    simpa [prefixWord, tailWord_689940, baseEnd_689940] using wordTrace_append hprefix tailTrace_689940
  have hstable : (prefixWord ++ tailWord_689940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689940).length < 2 ^ (prefixWord ++ tailWord_689940).sum := by decide
  have hdescent : baseEnd_689940 < baseStart_689940 := by decide
  rcases family_descends (prefixWord ++ tailWord_689940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689981 : List Nat := [1, 4, 1, 4, 1, 2, 1, 4, 1, 3]
def baseStart_689981 : Nat := 118140960795 + 689981 * 2 ^ 59
def prefixEnd_689981 : Nat := 4983230072969 + 3 ^ 40 * 689981 * 2
def baseEnd_689981 : Nat := 236194596979980119909561

theorem tailTrace_689981 : CollatzResearch.WordTrace tailWord_689981 prefixEnd_689981 236194596979980119909561 := by
  unfold tailWord_689981
  simp only [CollatzResearch.WordTrace]
  refine ⟨25165674513324151218237797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16777116342216100812158531 25165674513324151218237797)
  ·
    refine ⟨4718563971248278353419587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25165674513324151218237797 4718563971248278353419587)
    ·
      refine ⟨7077845956872417530129381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4718563971248278353419587 7077845956872417530129381)
      ·
        refine ⟨1327096116913578286899259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7077845956872417530129381 1327096116913578286899259)
        ·
          refine ⟨1990644175370367430348889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1327096116913578286899259 1990644175370367430348889)
          ·
            refine ⟨1492983131527775572761667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1990644175370367430348889 1492983131527775572761667)
            ·
              refine ⟨2239474697291663359142501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1492983131527775572761667 2239474697291663359142501)
              ·
                refine ⟨419901505742186879839219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2239474697291663359142501 419901505742186879839219)
                ·
                  refine ⟨629852258613280319758829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419901505742186879839219 629852258613280319758829)
                  ·
                    refine ⟨236194596979980119909561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 629852258613280319758829 236194596979980119909561)
                    ·
                      rfl

theorem cell22_689981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_689981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_689981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_689981 prefixEnd_689981 := by exact prefixLift 689981
  have htrace : WordTrace (prefixWord ++ tailWord_689981) baseStart_689981 baseEnd_689981 := by
    simpa [prefixWord, tailWord_689981, baseEnd_689981] using wordTrace_append hprefix tailTrace_689981
  have hstable : (prefixWord ++ tailWord_689981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689981).length < 2 ^ (prefixWord ++ tailWord_689981).sum := by decide
  have hdescent : baseEnd_689981 < baseStart_689981 := by decide
  rcases family_descends (prefixWord ++ tailWord_689981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690005 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 8]
def baseStart_690005 : Nat := 118140960795 + 690005 * 2 ^ 59
def prefixEnd_690005 : Nat := 4983230072969 + 3 ^ 40 * 690005 * 2
def baseEnd_690005 : Nat := 78734270890150685769829

theorem tailTrace_690005 : CollatzResearch.WordTrace tailWord_690005 prefixEnd_690005 78734270890150685769829 := by
  unfold tailWord_690005
  simp only [CollatzResearch.WordTrace]
  refine ⟨25166549865237203317111469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16777699910158135544740979 25166549865237203317111469)
  ·
    refine ⟨9437456199463951243916801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25166549865237203317111469 9437456199463951243916801)
    ·
      refine ⟨7078092149597963432937601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9437456199463951243916801 7078092149597963432937601)
      ·
        refine ⟨5308569112198472574703201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7078092149597963432937601 5308569112198472574703201)
        ·
          refine ⟨3981426834148854431027401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5308569112198472574703201 3981426834148854431027401)
          ·
            refine ⟨2986070125611640823270551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3981426834148854431027401 2986070125611640823270551)
            ·
              refine ⟨4479105188417461234905827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2986070125611640823270551 4479105188417461234905827)
              ·
                refine ⟨6718657782626191852358741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4479105188417461234905827 6718657782626191852358741)
                ·
                  refine ⟨78734270890150685769829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6718657782626191852358741 78734270890150685769829)
                  ·
                    rfl

theorem cell22_690005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_690005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690005 prefixEnd_690005 := by exact prefixLift 690005
  have htrace : WordTrace (prefixWord ++ tailWord_690005) baseStart_690005 baseEnd_690005 := by
    simpa [prefixWord, tailWord_690005, baseEnd_690005] using wordTrace_append hprefix tailTrace_690005
  have hstable : (prefixWord ++ tailWord_690005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690005).length < 2 ^ (prefixWord ++ tailWord_690005).sum := by decide
  have hdescent : baseEnd_690005 < baseStart_690005 := by decide
  rcases family_descends (prefixWord ++ tailWord_690005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690035 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 4, 4]
def baseStart_690035 : Nat := 118140960795 + 690035 * 2 ^ 59
def prefixEnd_690035 : Nat := 4983230072969 + 3 ^ 40 * 690035 * 2
def baseEnd_690035 : Nat := 236213082283541979059395

theorem tailTrace_690035 : CollatzResearch.WordTrace tailWord_690035 prefixEnd_690035 236213082283541979059395 := by
  unfold tailWord_690035
  simp only [CollatzResearch.WordTrace]
  refine ⟨25167644055128518440703559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16778429370085678960469039 25167644055128518440703559)
  ·
    refine ⟨37751466082692777661055339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25167644055128518440703559 37751466082692777661055339)
    ·
      refine ⟨56627199124039166491583009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37751466082692777661055339 56627199124039166491583009)
      ·
        refine ⟨42470399343029374868687257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56627199124039166491583009 42470399343029374868687257)
        ·
          refine ⟨31852799507272031151515443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42470399343029374868687257 31852799507272031151515443)
          ·
            refine ⟨47779199260908046727273165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31852799507272031151515443 47779199260908046727273165)
            ·
              refine ⟨17917199722840517522727437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47779199260908046727273165 17917199722840517522727437)
              ·
                refine ⟨6718949896065194071022789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17917199722840517522727437 6718949896065194071022789)
                ·
                  refine ⟨1259803105512223888316773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6718949896065194071022789 1259803105512223888316773)
                  ·
                    refine ⟨236213082283541979059395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1259803105512223888316773 236213082283541979059395)
                    ·
                      rfl

theorem cell22_690035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 4].length) (baseStart_690035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690035 prefixEnd_690035 := by exact prefixLift 690035
  have htrace : WordTrace (prefixWord ++ tailWord_690035) baseStart_690035 baseEnd_690035 := by
    simpa [prefixWord, tailWord_690035, baseEnd_690035] using wordTrace_append hprefix tailTrace_690035
  have hstable : (prefixWord ++ tailWord_690035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690035).length < 2 ^ (prefixWord ++ tailWord_690035).sum := by decide
  have hdescent : baseEnd_690035 < baseStart_690035 := by decide
  rcases family_descends (prefixWord ++ tailWord_690035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690080 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 1, 8]
def baseStart_690080 : Nat := 118140960795 + 690080 * 2 ^ 59
def prefixEnd_690080 : Nat := 4983230072969 + 3 ^ 40 * 690080 * 2
def baseEnd_690080 : Nat := 236228486703176861684257

theorem tailTrace_690080 : CollatzResearch.WordTrace tailWord_690080 prefixEnd_690080 236228486703176861684257 := by
  unfold tailWord_690080
  simp only [CollatzResearch.WordTrace]
  refine ⟨12584642669982745563045847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16779523559976994084061129 12584642669982745563045847)
  ·
    refine ⟨18876964004974118344568771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12584642669982745563045847 18876964004974118344568771)
    ·
      refine ⟨28315446007461177516853157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18876964004974118344568771 28315446007461177516853157)
      ·
        refine ⟨5309146126398970784409967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28315446007461177516853157 5309146126398970784409967)
        ·
          refine ⟨7963719189598456176614951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5309146126398970784409967 7963719189598456176614951)
          ·
            refine ⟨11945578784397684264922427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7963719189598456176614951 11945578784397684264922427)
            ·
              refine ⟨17918368176596526397383641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11945578784397684264922427 17918368176596526397383641)
              ·
                refine ⟨13438776132447394798037731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17918368176596526397383641 13438776132447394798037731)
                ·
                  refine ⟨20158164198671092197056597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13438776132447394798037731 20158164198671092197056597)
                  ·
                    refine ⟨236228486703176861684257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20158164198671092197056597 236228486703176861684257)
                    ·
                      rfl

theorem cell22_690080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_690080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690080 prefixEnd_690080 := by exact prefixLift 690080
  have htrace : WordTrace (prefixWord ++ tailWord_690080) baseStart_690080 baseEnd_690080 := by
    simpa [prefixWord, tailWord_690080, baseEnd_690080] using wordTrace_append hprefix tailTrace_690080
  have hstable : (prefixWord ++ tailWord_690080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690080).length < 2 ^ (prefixWord ++ tailWord_690080).sum := by decide
  have hdescent : baseEnd_690080 < baseStart_690080 := by decide
  rcases family_descends (prefixWord ++ tailWord_690080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690095 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 7]
def baseStart_690095 : Nat := 118140960795 + 690095 * 2 ^ 59
def prefixEnd_690095 : Nat := 4983230072969 + 3 ^ 40 * 690095 * 2
def baseEnd_690095 : Nat := 78744540503240607519737

theorem tailTrace_690095 : CollatzResearch.WordTrace tailWord_690095 prefixEnd_690095 78744540503240607519737 := by
  unfold tailWord_690095
  simp only [CollatzResearch.WordTrace]
  refine ⟨25169832434911148687887739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16779888289940765791925159 25169832434911148687887739)
  ·
    refine ⟨37754748652366723031831609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25169832434911148687887739 37754748652366723031831609)
    ·
      refine ⟨28316061489275042273873707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37754748652366723031831609 28316061489275042273873707)
      ·
        refine ⟨42474092233912563410810561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28316061489275042273873707 42474092233912563410810561)
        ·
          refine ⟨31855569175434422558107921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42474092233912563410810561 31855569175434422558107921)
          ·
            refine ⟨23891676881575816918580941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31855569175434422558107921 23891676881575816918580941)
            ·
              refine ⟨8959378830590931344467853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23891676881575816918580941 8959378830590931344467853)
              ·
                refine ⟨3359767061471599254175445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8959378830590931344467853 3359767061471599254175445)
                ·
                  refine ⟨78744540503240607519737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3359767061471599254175445 78744540503240607519737)
                  ·
                    rfl

theorem cell22_690095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 7].length) (baseStart_690095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690095 prefixEnd_690095 := by exact prefixLift 690095
  have htrace : WordTrace (prefixWord ++ tailWord_690095) baseStart_690095 baseEnd_690095 := by
    simpa [prefixWord, tailWord_690095, baseEnd_690095] using wordTrace_append hprefix tailTrace_690095
  have hstable : (prefixWord ++ tailWord_690095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690095).length < 2 ^ (prefixWord ++ tailWord_690095).sum := by decide
  have hdescent : baseEnd_690095 < baseStart_690095 := by decide
  rcases family_descends (prefixWord ++ tailWord_690095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690112 : List Nat := [2, 1, 1, 2, 3, 2, 3, 3, 5]
def baseStart_690112 : Nat := 118140960795 + 690112 * 2 ^ 59
def prefixEnd_690112 : Nat := 4983230072969 + 3 ^ 40 * 690112 * 2
def baseEnd_690112 : Nat := 78746480319046481628053

theorem tailTrace_690112 : CollatzResearch.WordTrace tailWord_690112 prefixEnd_690112 78746480319046481628053 := by
  unfold tailWord_690112
  simp only [CollatzResearch.WordTrace]
  refine ⟨12585226237924780295628295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16780301650566373727504393 12585226237924780295628295)
  ·
    refine ⟨18877839356887170443442443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12585226237924780295628295 18877839356887170443442443)
    ·
      refine ⟨28316759035330755665163665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18877839356887170443442443 28316759035330755665163665)
      ·
        refine ⟨21237569276498066748872749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28316759035330755665163665 21237569276498066748872749)
        ·
          refine ⟨7964088478686775030827281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21237569276498066748872749 7964088478686775030827281)
          ·
            refine ⟨5973066359015081273120461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7964088478686775030827281 5973066359015081273120461)
            ·
              refine ⟨2239899884630655477420173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5973066359015081273120461 2239899884630655477420173)
              ·
                refine ⟨839962456736495804032565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2239899884630655477420173 839962456736495804032565)
                ·
                  refine ⟨78746480319046481628053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 839962456736495804032565 78746480319046481628053)
                  ·
                    rfl

theorem cell22_690112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 5].length) (baseStart_690112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690112 prefixEnd_690112 := by exact prefixLift 690112
  have htrace : WordTrace (prefixWord ++ tailWord_690112) baseStart_690112 baseEnd_690112 := by
    simpa [prefixWord, tailWord_690112, baseEnd_690112] using wordTrace_append hprefix tailTrace_690112
  have hstable : (prefixWord ++ tailWord_690112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690112).length < 2 ^ (prefixWord ++ tailWord_690112).sum := by decide
  have hdescent : baseEnd_690112 < baseStart_690112 := by decide
  rcases family_descends (prefixWord ++ tailWord_690112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690174 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 8]
def baseStart_690174 : Nat := 118140960795 + 690174 * 2 ^ 59
def prefixEnd_690174 : Nat := 4983230072969 + 3 ^ 40 * 690174 * 2
def baseEnd_690174 : Nat := 78753554941397316611323

theorem tailTrace_690174 : CollatzResearch.WordTrace tailWord_690174 prefixEnd_690174 78753554941397316611323 := by
  unfold tailWord_690174
  simp only [CollatzResearch.WordTrace]
  refine ⟨3146589225203118147501697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16781809201083296786675717 3146589225203118147501697)
  ·
    refine ⟨2359941918902338610626273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3146589225203118147501697 2359941918902338610626273)
    ·
      refine ⟨1769956439176753957969705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2359941918902338610626273 1769956439176753957969705)
      ·
        refine ⟨1327467329382565468477279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1769956439176753957969705 1327467329382565468477279)
        ·
          refine ⟨1991200994073848202715919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1327467329382565468477279 1991200994073848202715919)
          ·
            refine ⟨2986801491110772304073879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991200994073848202715919 2986801491110772304073879)
            ·
              refine ⟨4480202236666158456110819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2986801491110772304073879 4480202236666158456110819)
              ·
                refine ⟨6720303354999237684166229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4480202236666158456110819 6720303354999237684166229)
                ·
                  refine ⟨78753554941397316611323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6720303354999237684166229 78753554941397316611323)
                  ·
                    rfl

theorem cell22_690174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_690174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690174 prefixEnd_690174 := by exact prefixLift 690174
  have htrace : WordTrace (prefixWord ++ tailWord_690174) baseStart_690174 baseEnd_690174 := by
    simpa [prefixWord, tailWord_690174, baseEnd_690174] using wordTrace_append hprefix tailTrace_690174
  have hstable : (prefixWord ++ tailWord_690174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690174).length < 2 ^ (prefixWord ++ tailWord_690174).sum := by decide
  have hdescent : baseEnd_690174 < baseStart_690174 := by decide
  rcases family_descends (prefixWord ++ tailWord_690174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690187 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 1, 6]
def baseStart_690187 : Nat := 118140960795 + 690187 * 2 ^ 59
def prefixEnd_690187 : Nat := 4983230072969 + 3 ^ 40 * 690187 * 2
def baseEnd_690187 : Nat := 236265114989864249258929

theorem tailTrace_690187 : CollatzResearch.WordTrace tailWord_690187 prefixEnd_690187 236265114989864249258929 := by
  unfold tailWord_690187
  simp only [CollatzResearch.WordTrace]
  refine ⟨25173187950577848400236815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16782125300385232266824543 25173187950577848400236815)
  ·
    refine ⟨37759781925866772600355223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25173187950577848400236815 37759781925866772600355223)
    ·
      refine ⟨56639672888800158900532835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37759781925866772600355223 56639672888800158900532835)
      ·
        refine ⟨84959509333200238350799253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56639672888800158900532835 84959509333200238350799253)
        ·
          refine ⟨3982476999993761172693715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84959509333200238350799253 3982476999993761172693715)
          ·
            refine ⟨5973715499990641759040573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3982476999993761172693715 5973715499990641759040573)
            ·
              refine ⟨2240143312496490659640215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5973715499990641759040573 2240143312496490659640215)
              ·
                refine ⟨3360214968744735989460323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2240143312496490659640215 3360214968744735989460323)
                ·
                  refine ⟨5040322453117103984190485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3360214968744735989460323 5040322453117103984190485)
                  ·
                    refine ⟨236265114989864249258929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5040322453117103984190485 236265114989864249258929)
                    ·
                      rfl

theorem cell22_690187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 6].length) (baseStart_690187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690187 prefixEnd_690187 := by exact prefixLift 690187
  have htrace : WordTrace (prefixWord ++ tailWord_690187) baseStart_690187 baseEnd_690187 := by
    simpa [prefixWord, tailWord_690187, baseEnd_690187] using wordTrace_append hprefix tailTrace_690187
  have hstable : (prefixWord ++ tailWord_690187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690187).length < 2 ^ (prefixWord ++ tailWord_690187).sum := by decide
  have hdescent : baseEnd_690187 < baseStart_690187 := by decide
  rcases family_descends (prefixWord ++ tailWord_690187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690202 : List Nat := [3, 1, 1, 3, 1, 4, 9]
def baseStart_690202 : Nat := 118140960795 + 690202 * 2 ^ 59
def prefixEnd_690202 : Nat := 4983230072969 + 3 ^ 40 * 690202 * 2
def baseEnd_690202 : Nat := 8750749992459600375329

theorem tailTrace_690202 : CollatzResearch.WordTrace tailWord_690202 prefixEnd_690202 8750749992459600375329 := by
  unfold tailWord_690202
  simp only [CollatzResearch.WordTrace]
  refine ⟨6293433761380876490508215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16782490030349003974688573 6293433761380876490508215)
  ·
    refine ⟨9440150642071314735762323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6293433761380876490508215 9440150642071314735762323)
    ·
      refine ⟨14160225963106972103643485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9440150642071314735762323 14160225963106972103643485)
      ·
        refine ⟨5310084736165114538866307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14160225963106972103643485 5310084736165114538866307)
        ·
          refine ⟨7965127104247671808299461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5310084736165114538866307 7965127104247671808299461)
          ·
            refine ⟨1493461332046438464056149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7965127104247671808299461 1493461332046438464056149)
            ·
              refine ⟨8750749992459600375329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1493461332046438464056149 8750749992459600375329)
              ·
                rfl

theorem cell22_690202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 9].length) (baseStart_690202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690202 prefixEnd_690202 := by exact prefixLift 690202
  have htrace : WordTrace (prefixWord ++ tailWord_690202) baseStart_690202 baseEnd_690202 := by
    simpa [prefixWord, tailWord_690202, baseEnd_690202] using wordTrace_append hprefix tailTrace_690202
  have hstable : (prefixWord ++ tailWord_690202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690202).length < 2 ^ (prefixWord ++ tailWord_690202).sum := by decide
  have hdescent : baseEnd_690202 < baseStart_690202 := by decide
  rcases family_descends (prefixWord ++ tailWord_690202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690247 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 9]
def baseStart_690247 : Nat := 118140960795 + 690247 * 2 ^ 59
def prefixEnd_690247 : Nat := 4983230072969 + 3 ^ 40 * 690247 * 2
def baseEnd_690247 : Nat := 78761884738681364252915

theorem tailTrace_690247 : CollatzResearch.WordTrace tailWord_690247 prefixEnd_690247 78761884738681364252915 := by
  unfold tailWord_690247
  simp only [CollatzResearch.WordTrace]
  refine ⟨25175376330360478647420995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16783584220240319098280663 25175376330360478647420995)
  ·
    refine ⟨37763064495540717971131493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25175376330360478647420995 37763064495540717971131493)
    ·
      refine ⟨7080574592913884619587155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37763064495540717971131493 7080574592913884619587155)
      ·
        refine ⟨10620861889370826929380733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7080574592913884619587155 10620861889370826929380733)
        ·
          refine ⟨3982823208514060098517775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10620861889370826929380733 3982823208514060098517775)
          ·
            refine ⟨5974234812771090147776663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3982823208514060098517775 5974234812771090147776663)
            ·
              refine ⟨8961352219156635221664995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5974234812771090147776663 8961352219156635221664995)
              ·
                refine ⟨13442028328734952832497493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8961352219156635221664995 13442028328734952832497493)
                ·
                  refine ⟨78761884738681364252915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13442028328734952832497493 78761884738681364252915)
                  ·
                    rfl

theorem cell22_690247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 9].length) (baseStart_690247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690247 prefixEnd_690247 := by exact prefixLift 690247
  have htrace : WordTrace (prefixWord ++ tailWord_690247) baseStart_690247 baseEnd_690247 := by
    simpa [prefixWord, tailWord_690247, baseEnd_690247] using wordTrace_append hprefix tailTrace_690247
  have hstable : (prefixWord ++ tailWord_690247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690247).length < 2 ^ (prefixWord ++ tailWord_690247).sum := by decide
  have hdescent : baseEnd_690247 < baseStart_690247 := by decide
  rcases family_descends (prefixWord ++ tailWord_690247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690268 : List Nat := [2, 2, 4, 1, 1, 4, 1, 1, 3, 3]
def baseStart_690268 : Nat := 118140960795 + 690268 * 2 ^ 59
def prefixEnd_690268 : Nat := 4983230072969 + 3 ^ 40 * 690268 * 2
def baseEnd_690268 : Nat := 236292842945207037983681

theorem tailTrace_690268 : CollatzResearch.WordTrace tailWord_690268 prefixEnd_690268 236292842945207037983681 := by
  unfold tailWord_690268
  simp only [CollatzResearch.WordTrace]
  refine ⟨12588071131642199616967729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16784094842189599489290305 12588071131642199616967729)
  ·
    refine ⟨9441053348731649712725797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12588071131642199616967729 9441053348731649712725797)
    ·
      refine ⟨1770197502887184321136087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9441053348731649712725797 1770197502887184321136087)
      ·
        refine ⟨2655296254330776481704131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1770197502887184321136087 2655296254330776481704131)
        ·
          refine ⟨3982944381496164722556197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2655296254330776481704131 3982944381496164722556197)
          ·
            refine ⟨746802071530530885479287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3982944381496164722556197 746802071530530885479287)
            ·
              refine ⟨1120203107295796328218931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 746802071530530885479287 1120203107295796328218931)
              ·
                refine ⟨1680304660943694492328397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1120203107295796328218931 1680304660943694492328397)
                ·
                  refine ⟨630114247853885434623149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1680304660943694492328397 630114247853885434623149)
                  ·
                    refine ⟨236292842945207037983681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 630114247853885434623149 236292842945207037983681)
                    ·
                      rfl

theorem cell22_690268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_690268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690268 prefixEnd_690268 := by exact prefixLift 690268
  have htrace : WordTrace (prefixWord ++ tailWord_690268) baseStart_690268 baseEnd_690268 := by
    simpa [prefixWord, tailWord_690268, baseEnd_690268] using wordTrace_append hprefix tailTrace_690268
  have hstable : (prefixWord ++ tailWord_690268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690268).length < 2 ^ (prefixWord ++ tailWord_690268).sum := by decide
  have hdescent : baseEnd_690268 < baseStart_690268 := by decide
  rcases family_descends (prefixWord ++ tailWord_690268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690341 : List Nat := [1, 3, 1, 2, 1, 3, 1, 5, 2, 3]
def baseStart_690341 : Nat := 118140960795 + 690341 * 2 ^ 59
def prefixEnd_690341 : Nat := 4983230072969 + 3 ^ 40 * 690341 * 2
def baseEnd_690341 : Nat := 236317832337059180908457

theorem tailTrace_690341 : CollatzResearch.WordTrace tailWord_690341 prefixEnd_690341 236317832337059180908457 := by
  unfold tailWord_690341
  simp only [CollatzResearch.WordTrace]
  refine ⟨25178804792019932701342877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16785869861346621800895251 25178804792019932701342877)
  ·
    refine ⟨9442051797007474763003579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25178804792019932701342877 9442051797007474763003579)
    ·
      refine ⟨14163077695511212144505369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9442051797007474763003579 14163077695511212144505369)
      ·
        refine ⟨10622308271633409108379027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14163077695511212144505369 10622308271633409108379027)
        ·
          refine ⟨15933462407450113662568541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10622308271633409108379027 15933462407450113662568541)
          ·
            refine ⟨5975048402793792623463203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15933462407450113662568541 5975048402793792623463203)
            ·
              refine ⟨8962572604190688935194805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5975048402793792623463203 8962572604190688935194805)
              ·
                refine ⟨840241181642877087674513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8962572604190688935194805 840241181642877087674513)
                ·
                  refine ⟨630180886232157815755885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 840241181642877087674513 630180886232157815755885)
                  ·
                    refine ⟨236317832337059180908457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 630180886232157815755885 236317832337059180908457)
                    ·
                      rfl

theorem cell22_690341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_690341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690341 prefixEnd_690341 := by exact prefixLift 690341
  have htrace : WordTrace (prefixWord ++ tailWord_690341) baseStart_690341 baseEnd_690341 := by
    simpa [prefixWord, tailWord_690341, baseEnd_690341] using wordTrace_append hprefix tailTrace_690341
  have hstable : (prefixWord ++ tailWord_690341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690341).length < 2 ^ (prefixWord ++ tailWord_690341).sum := by decide
  have hdescent : baseEnd_690341 < baseStart_690341 := by decide
  rcases family_descends (prefixWord ++ tailWord_690341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690446 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_690446 : Nat := 118140960795 + 690446 * 2 ^ 59
def prefixEnd_690446 : Nat := 4983230072969 + 3 ^ 40 * 690446 * 2
def baseEnd_690446 : Nat := 236353775982873907033135

theorem tailTrace_690446 : CollatzResearch.WordTrace tailWord_690446 prefixEnd_690446 236353775982873907033135 := by
  unfold tailWord_690446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3147829307079941954239399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16788422971093023755943461 3147829307079941954239399)
  ·
    refine ⟨4721743960619912931359099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3147829307079941954239399 4721743960619912931359099)
    ·
      refine ⟨7082615940929869397038649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4721743960619912931359099 7082615940929869397038649)
      ·
        refine ⟨5311961955697402047778987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7082615940929869397038649 5311961955697402047778987)
        ·
          refine ⟨7967942933546103071668481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5311961955697402047778987 7967942933546103071668481)
          ·
            refine ⟨5975957200159577303751361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7967942933546103071668481 5975957200159577303751361)
            ·
              refine ⟨4481967900119682977813521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5975957200159577303751361 4481967900119682977813521)
              ·
                refine ⟨3361475925089762233360141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4481967900119682977813521 3361475925089762233360141)
                ·
                  refine ⟨1260553471908660837510053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3361475925089762233360141 1260553471908660837510053)
                  ·
                    refine ⟨236353775982873907033135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1260553471908660837510053 236353775982873907033135)
                    ·
                      rfl

theorem cell22_690446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_690446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690446 prefixEnd_690446 := by exact prefixLift 690446
  have htrace : WordTrace (prefixWord ++ tailWord_690446) baseStart_690446 baseEnd_690446 := by
    simpa [prefixWord, tailWord_690446, baseEnd_690446] using wordTrace_append hprefix tailTrace_690446
  have hstable : (prefixWord ++ tailWord_690446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690446).length < 2 ^ (prefixWord ++ tailWord_690446).sum := by decide
  have hdescent : baseEnd_690446 < baseStart_690446 := by decide
  rcases family_descends (prefixWord ++ tailWord_690446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690463 : List Nat := [1, 1, 2, 4, 3, 1, 3, 2, 1, 4]
def baseStart_690463 : Nat := 118140960795 + 690463 * 2 ^ 59
def prefixEnd_690463 : Nat := 4983230072969 + 3 ^ 40 * 690463 * 2
def baseEnd_690463 : Nat := 236359595430291529358083

theorem tailTrace_690463 : CollatzResearch.WordTrace tailWord_690463 prefixEnd_690463 236359595430291529358083 := by
  unfold tailWord_690463
  simp only [CollatzResearch.WordTrace]
  refine ⟨25183254497577947537284043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16788836331718631691522695 25183254497577947537284043)
  ·
    refine ⟨37774881746366921305926065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25183254497577947537284043 37774881746366921305926065)
    ·
      refine ⟨28331161309775190979444549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37774881746366921305926065 28331161309775190979444549)
      ·
        refine ⟨5312092745582848308645853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28331161309775190979444549 5312092745582848308645853)
        ·
          refine ⟨1992034779593568115742195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5312092745582848308645853 1992034779593568115742195)
          ·
            refine ⟨2988052169390352173613293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1992034779593568115742195 2988052169390352173613293)
            ·
              refine ⟨1120519563521382065104985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2988052169390352173613293 1120519563521382065104985)
              ·
                refine ⟨840389672641036548828739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1120519563521382065104985 840389672641036548828739)
                ·
                  refine ⟨1260584508961554823243109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 840389672641036548828739 1260584508961554823243109)
                  ·
                    refine ⟨236359595430291529358083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1260584508961554823243109 236359595430291529358083)
                    ·
                      rfl

theorem cell22_690463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 4].length) (baseStart_690463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690463 prefixEnd_690463 := by exact prefixLift 690463
  have htrace : WordTrace (prefixWord ++ tailWord_690463) baseStart_690463 baseEnd_690463 := by
    simpa [prefixWord, tailWord_690463, baseEnd_690463] using wordTrace_append hprefix tailTrace_690463
  have hstable : (prefixWord ++ tailWord_690463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690463).length < 2 ^ (prefixWord ++ tailWord_690463).sum := by decide
  have hdescent : baseEnd_690463 < baseStart_690463 := by decide
  rcases family_descends (prefixWord ++ tailWord_690463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690476 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 6, 3]
def baseStart_690476 : Nat := 118140960795 + 690476 * 2 ^ 59
def prefixEnd_690476 : Nat := 4983230072969 + 3 ^ 40 * 690476 * 2
def baseEnd_690476 : Nat := 236364045595963828783043

theorem tailTrace_690476 : CollatzResearch.WordTrace tailWord_690476 prefixEnd_690476 236364045595963828783043 := by
  unfold tailWord_690476
  simp only [CollatzResearch.WordTrace]
  refine ⟨12591864323265425378753641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16789152431020567171671521 12591864323265425378753641)
  ·
    refine ⟨9443898242449069034065231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12591864323265425378753641 9443898242449069034065231)
    ·
      refine ⟨14165847363673603551097847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9443898242449069034065231 14165847363673603551097847)
      ·
        refine ⟨21248771045510405326646771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14165847363673603551097847 21248771045510405326646771)
        ·
          refine ⟨31873156568265607989970157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21248771045510405326646771 31873156568265607989970157)
          ·
            refine ⟨11952433713099602996238809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31873156568265607989970157 11952433713099602996238809)
            ·
              refine ⟨8964325284824702247179107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11952433713099602996238809 8964325284824702247179107)
              ·
                refine ⟨13446487927237053370768661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8964325284824702247179107 13446487927237053370768661)
                ·
                  refine ⟨630304121589236876754781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13446487927237053370768661 630304121589236876754781)
                  ·
                    refine ⟨236364045595963828783043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 630304121589236876754781 236364045595963828783043)
                    ·
                      rfl

theorem cell22_690476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_690476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690476 prefixEnd_690476 := by exact prefixLift 690476
  have htrace : WordTrace (prefixWord ++ tailWord_690476) baseStart_690476 baseEnd_690476 := by
    simpa [prefixWord, tailWord_690476, baseEnd_690476] using wordTrace_append hprefix tailTrace_690476
  have hstable : (prefixWord ++ tailWord_690476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690476).length < 2 ^ (prefixWord ++ tailWord_690476).sum := by decide
  have hdescent : baseEnd_690476 < baseStart_690476 := by decide
  rcases family_descends (prefixWord ++ tailWord_690476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690551 : List Nat := [1, 1, 3, 1, 1, 2, 2, 6, 5]
def baseStart_690551 : Nat := 118140960795 + 690551 * 2 ^ 59
def prefixEnd_690551 : Nat := 4983230072969 + 3 ^ 40 * 690551 * 2
def baseEnd_690551 : Nat := 78796573209562877719271

theorem tailTrace_690551 : CollatzResearch.WordTrace tailWord_690551 prefixEnd_690551 78796573209562877719271 := by
  unfold tailWord_690551
  simp only [CollatzResearch.WordTrace]
  refine ⟨25186464121259138566487507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16790976080839425710991671 25186464121259138566487507)
  ·
    refine ⟨37779696181888707849731261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25186464121259138566487507 37779696181888707849731261)
    ·
      refine ⟨14167386068208265443649223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37779696181888707849731261 14167386068208265443649223)
      ·
        refine ⟨21251079102312398165473835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14167386068208265443649223 21251079102312398165473835)
        ·
          refine ⟨31876618653468597248210753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21251079102312398165473835 31876618653468597248210753)
          ·
            refine ⟨23907463990101447936158065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31876618653468597248210753 23907463990101447936158065)
            ·
              refine ⟨17930597992576085952118549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23907463990101447936158065 17930597992576085952118549)
              ·
                refine ⟨840496780902004029005557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17930597992576085952118549 840496780902004029005557)
                ·
                  refine ⟨78796573209562877719271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 840496780902004029005557 78796573209562877719271)
                  ·
                    rfl

theorem cell22_690551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 5].length) (baseStart_690551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690551 prefixEnd_690551 := by exact prefixLift 690551
  have htrace : WordTrace (prefixWord ++ tailWord_690551) baseStart_690551 baseEnd_690551 := by
    simpa [prefixWord, tailWord_690551, baseEnd_690551] using wordTrace_append hprefix tailTrace_690551
  have hstable : (prefixWord ++ tailWord_690551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690551).length < 2 ^ (prefixWord ++ tailWord_690551).sum := by decide
  have hdescent : baseEnd_690551 < baseStart_690551 := by decide
  rcases family_descends (prefixWord ++ tailWord_690551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690555 : List Nat := [1, 1, 1, 1, 1, 7, 2, 4, 1, 3]
def baseStart_690555 : Nat := 118140960795 + 690555 * 2 ^ 59
def prefixEnd_690555 : Nat := 4983230072969 + 3 ^ 40 * 690555 * 2
def baseEnd_690555 : Nat := 236391088910433956057801

theorem tailTrace_690555 : CollatzResearch.WordTrace tailWord_690555 prefixEnd_690555 236391088910433956057801 := by
  unfold tailWord_690555
  simp only [CollatzResearch.WordTrace]
  refine ⟨25186610013244647249633119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16791073342163098166422079 25186610013244647249633119)
  ·
    refine ⟨37779915019866970874449679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25186610013244647249633119 37779915019866970874449679)
    ·
      refine ⟨56669872529800456311674519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37779915019866970874449679 56669872529800456311674519)
      ·
        refine ⟨85004808794700684467511779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56669872529800456311674519 85004808794700684467511779)
        ·
          refine ⟨127507213192051026701267669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85004808794700684467511779 127507213192051026701267669)
          ·
            refine ⟨2988450309188695938310961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 127507213192051026701267669 2988450309188695938310961)
            ·
              refine ⟨2241337731891521953733221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2988450309188695938310961 2241337731891521953733221)
              ·
                refine ⟨420250824729660366324979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2241337731891521953733221 420250824729660366324979)
                ·
                  refine ⟨630376237094490549487469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 420250824729660366324979 630376237094490549487469)
                  ·
                    refine ⟨236391088910433956057801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 630376237094490549487469 236391088910433956057801)
                    ·
                      rfl

theorem cell22_690555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 1, 3].length) (baseStart_690555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690555 prefixEnd_690555 := by exact prefixLift 690555
  have htrace : WordTrace (prefixWord ++ tailWord_690555) baseStart_690555 baseEnd_690555 := by
    simpa [prefixWord, tailWord_690555, baseEnd_690555] using wordTrace_append hprefix tailTrace_690555
  have hstable : (prefixWord ++ tailWord_690555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690555).length < 2 ^ (prefixWord ++ tailWord_690555).sum := by decide
  have hdescent : baseEnd_690555 < baseStart_690555 := by decide
  rcases family_descends (prefixWord ++ tailWord_690555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690589 : List Nat := [1, 4, 2, 1, 4, 2, 1, 3, 1, 3]
def baseStart_690589 : Nat := 118140960795 + 690589 * 2 ^ 59
def prefixEnd_690589 : Nat := 4983230072969 + 3 ^ 40 * 690589 * 2
def baseEnd_690589 : Nat := 236402727805269200707697

theorem tailTrace_690589 : CollatzResearch.WordTrace tailWord_690589 prefixEnd_690589 236402727805269200707697 := by
  unfold tailWord_690589
  simp only [CollatzResearch.WordTrace]
  refine ⟨25187850095121471056370821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16791900063414314037580547 25187850095121471056370821)
  ·
    refine ⟨4722721892835275823069529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25187850095121471056370821 4722721892835275823069529)
    ·
      refine ⟨3542041419626456867302147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4722721892835275823069529 3542041419626456867302147)
      ·
        refine ⟨5313062129439685300953221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3542041419626456867302147 5313062129439685300953221)
        ·
          refine ⟨996199149269940993928729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5313062129439685300953221 996199149269940993928729)
          ·
            refine ⟨747149361952455745446547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 996199149269940993928729 747149361952455745446547)
            ·
              refine ⟨1120724042928683618169821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747149361952455745446547 1120724042928683618169821)
              ·
                refine ⟨420271516098256356813683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1120724042928683618169821 420271516098256356813683)
                ·
                  refine ⟨630407274147384535220525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 420271516098256356813683 630407274147384535220525)
                  ·
                    refine ⟨236402727805269200707697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 630407274147384535220525 236402727805269200707697)
                    ·
                      rfl

theorem cell22_690589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_690589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690589 prefixEnd_690589 := by exact prefixLift 690589
  have htrace : WordTrace (prefixWord ++ tailWord_690589) baseStart_690589 baseEnd_690589 := by
    simpa [prefixWord, tailWord_690589, baseEnd_690589] using wordTrace_append hprefix tailTrace_690589
  have hstable : (prefixWord ++ tailWord_690589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690589).length < 2 ^ (prefixWord ++ tailWord_690589).sum := by decide
  have hdescent : baseEnd_690589 < baseStart_690589 := by decide
  rcases family_descends (prefixWord ++ tailWord_690589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690596 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 8]
def baseStart_690596 : Nat := 118140960795 + 690596 * 2 ^ 59
def prefixEnd_690596 : Nat := 4983230072969 + 3 ^ 40 * 690596 * 2
def baseEnd_690596 : Nat := 78801708016107838594225

theorem tailTrace_690596 : CollatzResearch.WordTrace tailWord_690596 prefixEnd_690596 78801708016107838594225 := by
  unfold tailWord_690596
  simp only [CollatzResearch.WordTrace]
  refine ⟨12594052703048055625937821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16792070270730740834583761 12594052703048055625937821)
  ·
    refine ⟨4722769763643020859726683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12594052703048055625937821 4722769763643020859726683)
    ·
      refine ⟨7084154645464531289590025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4722769763643020859726683 7084154645464531289590025)
      ·
        refine ⟨5313115984098398467192519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7084154645464531289590025 5313115984098398467192519)
        ·
          refine ⟨7969673976147597700788779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5313115984098398467192519 7969673976147597700788779)
          ·
            refine ⟨11954510964221396551183169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7969673976147597700788779 11954510964221396551183169)
            ·
              refine ⟨8965883223166047413387377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11954510964221396551183169 8965883223166047413387377)
              ·
                refine ⟨6724412417374535560040533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8965883223166047413387377 6724412417374535560040533)
                ·
                  refine ⟨78801708016107838594225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6724412417374535560040533 78801708016107838594225)
                  ·
                    rfl

theorem cell22_690596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_690596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690596 prefixEnd_690596 := by exact prefixLift 690596
  have htrace : WordTrace (prefixWord ++ tailWord_690596) baseStart_690596 baseEnd_690596 := by
    simpa [prefixWord, tailWord_690596, baseEnd_690596] using wordTrace_append hprefix tailTrace_690596
  have hstable : (prefixWord ++ tailWord_690596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690596).length < 2 ^ (prefixWord ++ tailWord_690596).sum := by decide
  have hdescent : baseEnd_690596 < baseStart_690596 := by decide
  rcases family_descends (prefixWord ++ tailWord_690596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690694 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_690694 : Nat := 118140960795 + 690694 * 2 ^ 59
def prefixEnd_690694 : Nat := 4983230072969 + 3 ^ 40 * 690694 * 2
def baseEnd_690694 : Nat := 236438671451083926832375

theorem tailTrace_690694 : CollatzResearch.WordTrace tailWord_690694 prefixEnd_690694 236438671451083926832375 := by
  unfold tailWord_690694
  simp only [CollatzResearch.WordTrace]
  refine ⟨787239992491908562154473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16794453173160715992628757 787239992491908562154473)
  ·
    refine ⟨590429994368931421615855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 787239992491908562154473 590429994368931421615855)
    ·
      refine ⟨885644991553397132423783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 590429994368931421615855 885644991553397132423783)
      ·
        refine ⟨1328467487330095698635675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 885644991553397132423783 1328467487330095698635675)
        ·
          refine ⟨1992701230995143547953513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1328467487330095698635675 1992701230995143547953513)
          ·
            refine ⟨1494525923246357660965135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1992701230995143547953513 1494525923246357660965135)
            ·
              refine ⟨2241788884869536491447703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1494525923246357660965135 2241788884869536491447703)
              ·
                refine ⟨3362683327304304737171555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2241788884869536491447703 3362683327304304737171555)
                ·
                  refine ⟨5044024990956457105757333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3362683327304304737171555 5044024990956457105757333)
                  ·
                    refine ⟨236438671451083926832375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5044024990956457105757333 236438671451083926832375)
                    ·
                      rfl

theorem cell22_690694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_690694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690694 prefixEnd_690694 := by exact prefixLift 690694
  have htrace : WordTrace (prefixWord ++ tailWord_690694) baseStart_690694 baseEnd_690694 := by
    simpa [prefixWord, tailWord_690694, baseEnd_690694] using wordTrace_append hprefix tailTrace_690694
  have hstable : (prefixWord ++ tailWord_690694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690694).length < 2 ^ (prefixWord ++ tailWord_690694).sum := by decide
  have hdescent : baseEnd_690694 < baseStart_690694 := by decide
  rcases family_descends (prefixWord ++ tailWord_690694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690707 : List Nat := [1, 1, 1, 2, 1, 5, 4, 3, 1, 3]
def baseStart_690707 : Nat := 118140960795 + 690707 * 2 ^ 59
def prefixEnd_690707 : Nat := 4983230072969 + 3 ^ 40 * 690707 * 2
def baseEnd_690707 : Nat := 236443121616756226257335

theorem tailTrace_690707 : CollatzResearch.WordTrace tailWord_690707 prefixEnd_690707 236443121616756226257335 := by
  unfold tailWord_690707
  simp only [CollatzResearch.WordTrace]
  refine ⟨25192153908693977209166375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16794769272462651472777583 25192153908693977209166375)
  ·
    refine ⟨37788230863040965813749563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25192153908693977209166375 37788230863040965813749563)
    ·
      refine ⟨56682346294561448720624345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37788230863040965813749563 56682346294561448720624345)
      ·
        refine ⟨42511759720921086540468259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56682346294561448720624345 42511759720921086540468259)
        ·
          refine ⟨63767639581381629810702389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42511759720921086540468259 63767639581381629810702389)
          ·
            refine ⟨5978216210754527794753349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63767639581381629810702389 5978216210754527794753349)
            ·
              refine ⟨1120915539516473961516253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5978216210754527794753349 1120915539516473961516253)
              ·
                refine ⟨420343327318677735568595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1120915539516473961516253 420343327318677735568595)
                ·
                  refine ⟨630514990978016603352893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 420343327318677735568595 630514990978016603352893)
                  ·
                    refine ⟨236443121616756226257335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 630514990978016603352893 236443121616756226257335)
                    ·
                      rfl

theorem cell22_690707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 1, 3].length) (baseStart_690707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690707 prefixEnd_690707 := by exact prefixLift 690707
  have htrace : WordTrace (prefixWord ++ tailWord_690707) baseStart_690707 baseEnd_690707 := by
    simpa [prefixWord, tailWord_690707, baseEnd_690707] using wordTrace_append hprefix tailTrace_690707
  have hstable : (prefixWord ++ tailWord_690707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690707).length < 2 ^ (prefixWord ++ tailWord_690707).sum := by decide
  have hdescent : baseEnd_690707 < baseStart_690707 := by decide
  rcases family_descends (prefixWord ++ tailWord_690707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690720 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 7]
def baseStart_690720 : Nat := 118140960795 + 690720 * 2 ^ 59
def prefixEnd_690720 : Nat := 4983230072969 + 3 ^ 40 * 690720 * 2
def baseEnd_690720 : Nat := 78815857260809508560765

theorem tailTrace_690720 : CollatzResearch.WordTrace tailWord_690720 prefixEnd_690720 78815857260809508560765 := by
  unfold tailWord_690720
  simp only [CollatzResearch.WordTrace]
  refine ⟨12596314028823440214694807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16795085371764586952926409 12596314028823440214694807)
  ·
    refine ⟨18894471043235160322042211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12596314028823440214694807 18894471043235160322042211)
    ·
      refine ⟨28341706564852740483063317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18894471043235160322042211 28341706564852740483063317)
      ·
        refine ⟨1328517495227472210143593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28341706564852740483063317 1328517495227472210143593)
        ·
          refine ⟨996388121420604157607695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1328517495227472210143593 996388121420604157607695)
          ·
            refine ⟨1494582182130906236411543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996388121420604157607695 1494582182130906236411543)
            ·
              refine ⟨2241873273196359354617315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1494582182130906236411543 2241873273196359354617315)
              ·
                refine ⟨3362809909794539031925973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2241873273196359354617315 3362809909794539031925973)
                ·
                  refine ⟨78815857260809508560765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3362809909794539031925973 78815857260809508560765)
                  ·
                    rfl

theorem cell22_690720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 7].length) (baseStart_690720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690720 prefixEnd_690720 := by exact prefixLift 690720
  have htrace : WordTrace (prefixWord ++ tailWord_690720) baseStart_690720 baseEnd_690720 := by
    simpa [prefixWord, tailWord_690720, baseEnd_690720] using wordTrace_append hprefix tailTrace_690720
  have hstable : (prefixWord ++ tailWord_690720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690720).length < 2 ^ (prefixWord ++ tailWord_690720).sum := by decide
  have hdescent : baseEnd_690720 < baseStart_690720 := by decide
  rcases family_descends (prefixWord ++ tailWord_690720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690724 : List Nat := [2, 3, 1, 5, 1, 1, 2, 1, 3, 3]
def baseStart_690724 : Nat := 118140960795 + 690724 * 2 ^ 59
def prefixEnd_690724 : Nat := 4983230072969 + 3 ^ 40 * 690724 * 2
def baseEnd_690724 : Nat := 236448941064173848582283

theorem tailTrace_690724 : CollatzResearch.WordTrace tailWord_690724 prefixEnd_690724 236448941064173848582283 := by
  unfold tailWord_690724
  simp only [CollatzResearch.WordTrace]
  refine ⟨12596386974816194556267613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16795182633088259408356817 12596386974816194556267613)
  ·
    refine ⟨4723645115556072958600355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12596386974816194556267613 4723645115556072958600355)
    ·
      refine ⟨7085467673334109437900533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4723645115556072958600355 7085467673334109437900533)
      ·
        refine ⟨664262594375072759803175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7085467673334109437900533 664262594375072759803175)
        ·
          refine ⟨996393891562609139704763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 664262594375072759803175 996393891562609139704763)
          ·
            refine ⟨1494590837343913709557145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996393891562609139704763 1494590837343913709557145)
            ·
              refine ⟨1120943128007935282167859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1494590837343913709557145 1120943128007935282167859)
              ·
                refine ⟨1681414692011902923251789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1120943128007935282167859 1681414692011902923251789)
                ·
                  refine ⟨630530509504463596219421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1681414692011902923251789 630530509504463596219421)
                  ·
                    refine ⟨236448941064173848582283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 630530509504463596219421 236448941064173848582283)
                    ·
                      rfl

theorem cell22_690724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_690724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690724 prefixEnd_690724 := by exact prefixLift 690724
  have htrace : WordTrace (prefixWord ++ tailWord_690724) baseStart_690724 baseEnd_690724 := by
    simpa [prefixWord, tailWord_690724, baseEnd_690724] using wordTrace_append hprefix tailTrace_690724
  have hstable : (prefixWord ++ tailWord_690724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690724).length < 2 ^ (prefixWord ++ tailWord_690724).sum := by decide
  have hdescent : baseEnd_690724 < baseStart_690724 := by decide
  rcases family_descends (prefixWord ++ tailWord_690724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690758 : List Nat := [6, 1, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_690758 : Nat := 118140960795 + 690758 * 2 ^ 59
def prefixEnd_690758 : Nat := 4983230072969 + 3 ^ 40 * 690758 * 2
def baseEnd_690758 : Nat := 236460579959009093232179

theorem tailTrace_690758 : CollatzResearch.WordTrace tailWord_690758 prefixEnd_690758 236460579959009093232179 := by
  unfold tailWord_690758
  simp only [CollatzResearch.WordTrace]
  refine ⟨787312938484662903727279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16796009354339475279515285 787312938484662903727279)
  ·
    refine ⟨1180969407726994355590919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 787312938484662903727279 1180969407726994355590919)
    ·
      refine ⟨1771454111590491533386379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1180969407726994355590919 1771454111590491533386379)
      ·
        refine ⟨2657181167385737300079569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1771454111590491533386379 2657181167385737300079569)
        ·
          refine ⟨1992885875539302975059677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2657181167385737300079569 1992885875539302975059677)
          ·
            refine ⟨747332203327238615647379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1992885875539302975059677 747332203327238615647379)
            ·
              refine ⟨1120998304990857923471069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747332203327238615647379 1120998304990857923471069)
              ·
                refine ⟨420374364371571721301651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1120998304990857923471069 420374364371571721301651)
                ·
                  refine ⟨630561546557357581952477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 420374364371571721301651 630561546557357581952477)
                  ·
                    refine ⟨236460579959009093232179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 630561546557357581952477 236460579959009093232179)
                    ·
                      rfl

theorem cell22_690758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_690758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690758 prefixEnd_690758 := by exact prefixLift 690758
  have htrace : WordTrace (prefixWord ++ tailWord_690758) baseStart_690758 baseEnd_690758 := by
    simpa [prefixWord, tailWord_690758, baseEnd_690758] using wordTrace_append hprefix tailTrace_690758
  have hstable : (prefixWord ++ tailWord_690758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690758).length < 2 ^ (prefixWord ++ tailWord_690758).sum := by decide
  have hdescent : baseEnd_690758 < baseStart_690758 := by decide
  rcases family_descends (prefixWord ++ tailWord_690758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690763 : List Nat := [1, 1, 1, 1, 3, 1, 4, 4, 1, 5]
def baseStart_690763 : Nat := 118140960795 + 690763 * 2 ^ 59
def prefixEnd_690763 : Nat := 4983230072969 + 3 ^ 40 * 690763 * 2
def baseEnd_690763 : Nat := 236462291561190746857163

theorem tailTrace_690763 : CollatzResearch.WordTrace tailWord_690763 prefixEnd_690763 236462291561190746857163 := by
  unfold tailWord_690763
  simp only [CollatzResearch.WordTrace]
  refine ⟨25194196396491098773204943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16796130930994065848803295 25194196396491098773204943)
  ·
    refine ⟨37791294594736648159807415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25194196396491098773204943 37791294594736648159807415)
    ·
      refine ⟨56686941892104972239711123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37791294594736648159807415 56686941892104972239711123)
      ·
        refine ⟨85030412838157458359566685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56686941892104972239711123 85030412838157458359566685)
        ·
          refine ⟨31886404814309046884837507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85030412838157458359566685 31886404814309046884837507)
          ·
            refine ⟨47829607221463570327256261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31886404814309046884837507 47829607221463570327256261)
            ·
              refine ⟨8968051354024419436360549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47829607221463570327256261 8968051354024419436360549)
              ·
                refine ⟨1681509628879578644317603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8968051354024419436360549 1681509628879578644317603)
                ·
                  refine ⟨2522264443319367966476405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1681509628879578644317603 2522264443319367966476405)
                  ·
                    refine ⟨236462291561190746857163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2522264443319367966476405 236462291561190746857163)
                    ·
                      rfl

theorem cell22_690763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 5].length) (baseStart_690763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690763 prefixEnd_690763 := by exact prefixLift 690763
  have htrace : WordTrace (prefixWord ++ tailWord_690763) baseStart_690763 baseEnd_690763 := by
    simpa [prefixWord, tailWord_690763, baseEnd_690763] using wordTrace_append hprefix tailTrace_690763
  have hstable : (prefixWord ++ tailWord_690763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690763).length < 2 ^ (prefixWord ++ tailWord_690763).sum := by decide
  have hdescent : baseEnd_690763 < baseStart_690763 := by decide
  rcases family_descends (prefixWord ++ tailWord_690763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690951 : List Nat := [1, 1, 4, 4, 1, 2, 3, 2, 4]
def baseStart_690951 : Nat := 118140960795 + 690951 * 2 ^ 59
def prefixEnd_690951 : Nat := 4983230072969 + 3 ^ 40 * 690951 * 2
def baseEnd_690951 : Nat := 78842215934406974385529

theorem tailTrace_690951 : CollatzResearch.WordTrace tailWord_690951 prefixEnd_690951 78842215934406974385529 := by
  unfold tailWord_690951
  simp only [CollatzResearch.WordTrace]
  refine ⟨25201053319810006881048707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16800702213206671254032471 25201053319810006881048707)
  ·
    refine ⟨37801579979715010321573061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25201053319810006881048707 37801579979715010321573061)
    ·
      refine ⟨7087796246196564435294949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37801579979715010321573061 7087796246196564435294949)
      ·
        refine ⟨1328961796161855831617803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7087796246196564435294949 1328961796161855831617803)
        ·
          refine ⟨1993442694242783747426705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1328961796161855831617803 1993442694242783747426705)
          ·
            refine ⟨1495082020682087810570029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1993442694242783747426705 1495082020682087810570029)
            ·
              refine ⟨560655757755782928963761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1495082020682087810570029 560655757755782928963761)
              ·
                refine ⟨420491818316837196722821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 560655757755782928963761 420491818316837196722821)
                ·
                  refine ⟨78842215934406974385529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 420491818316837196722821 78842215934406974385529)
                  ·
                    rfl

theorem cell22_690951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 4].length) (baseStart_690951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690951 prefixEnd_690951 := by exact prefixLift 690951
  have htrace : WordTrace (prefixWord ++ tailWord_690951) baseStart_690951 baseEnd_690951 := by
    simpa [prefixWord, tailWord_690951, baseEnd_690951] using wordTrace_append hprefix tailTrace_690951
  have hstable : (prefixWord ++ tailWord_690951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690951).length < 2 ^ (prefixWord ++ tailWord_690951).sum := by decide
  have hdescent : baseEnd_690951 < baseStart_690951 := by decide
  rcases family_descends (prefixWord ++ tailWord_690951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690977 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 5, 3]
def baseStart_690977 : Nat := 118140960795 + 690977 * 2 ^ 59
def prefixEnd_690977 : Nat := 4983230072969 + 3 ^ 40 * 690977 * 2
def baseEnd_690977 : Nat := 236535548134565522006507

theorem tailTrace_690977 : CollatzResearch.WordTrace tailWord_690977 prefixEnd_690977 236535548134565522006507 := by
  unfold tailWord_690977
  simp only [CollatzResearch.WordTrace]
  refine ⟨25202001617715813321495185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16801334411810542214330123 25202001617715813321495185)
  ·
    refine ⟨18901501213286859991121389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25202001617715813321495185 18901501213286859991121389)
    ·
      refine ⟨7088062954982572496670521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18901501213286859991121389 7088062954982572496670521)
      ·
        refine ⟨5316047216236929372502891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7088062954982572496670521 5316047216236929372502891)
        ·
          refine ⟨7974070824355394058754337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5316047216236929372502891 7974070824355394058754337)
          ·
            refine ⟨5980553118266545544065753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7974070824355394058754337 5980553118266545544065753)
            ·
              refine ⟨4485414838699909158049315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5980553118266545544065753 4485414838699909158049315)
              ·
                refine ⟨6728122258049863737073973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4485414838699909158049315 6728122258049863737073973)
                ·
                  refine ⟨630761461692174725350685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6728122258049863737073973 630761461692174725350685)
                  ·
                    refine ⟨236535548134565522006507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 630761461692174725350685 236535548134565522006507)
                    ·
                      rfl

theorem cell22_690977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_690977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_690977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_690977 prefixEnd_690977 := by exact prefixLift 690977
  have htrace : WordTrace (prefixWord ++ tailWord_690977) baseStart_690977 baseEnd_690977 := by
    simpa [prefixWord, tailWord_690977, baseEnd_690977] using wordTrace_append hprefix tailTrace_690977
  have hstable : (prefixWord ++ tailWord_690977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690977).length < 2 ^ (prefixWord ++ tailWord_690977).sum := by decide
  have hdescent : baseEnd_690977 < baseStart_690977 := by decide
  rcases family_descends (prefixWord ++ tailWord_690977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691007 : List Nat := [1, 1, 2, 2, 5, 1, 1, 4, 5]
def baseStart_691007 : Nat := 118140960795 + 691007 * 2 ^ 59
def prefixEnd_691007 : Nat := 4983230072969 + 3 ^ 40 * 691007 * 2
def baseEnd_691007 : Nat := 78848605915885147918805

theorem tailTrace_691007 : CollatzResearch.WordTrace tailWord_691007 prefixEnd_691007 78848605915885147918805 := by
  unfold tailWord_691007
  simp only [CollatzResearch.WordTrace]
  refine ⟨25203095807607128445087275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16802063871738085630058183 25203095807607128445087275)
  ·
    refine ⟨37804643711410692667630913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25203095807607128445087275 37804643711410692667630913)
    ·
      refine ⟨28353482783558019500723185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37804643711410692667630913 28353482783558019500723185)
      ·
        refine ⟨21265112087668514625542389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28353482783558019500723185 21265112087668514625542389)
        ·
          refine ⟨1993604258218923246144599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21265112087668514625542389 1993604258218923246144599)
          ·
            refine ⟨2990406387328384869216899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1993604258218923246144599 2990406387328384869216899)
            ·
              refine ⟨4485609580992577303825349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2990406387328384869216899 4485609580992577303825349)
              ·
                refine ⟨841051796436108244467253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4485609580992577303825349 841051796436108244467253)
                ·
                  refine ⟨78848605915885147918805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 841051796436108244467253 78848605915885147918805)
                  ·
                    rfl

theorem cell22_691007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 5].length) (baseStart_691007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691007 prefixEnd_691007 := by exact prefixLift 691007
  have htrace : WordTrace (prefixWord ++ tailWord_691007) baseStart_691007 baseEnd_691007 := by
    simpa [prefixWord, tailWord_691007, baseEnd_691007] using wordTrace_append hprefix tailTrace_691007
  have hstable : (prefixWord ++ tailWord_691007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691007).length < 2 ^ (prefixWord ++ tailWord_691007).sum := by decide
  have hdescent : baseEnd_691007 < baseStart_691007 := by decide
  rcases family_descends (prefixWord ++ tailWord_691007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691069 : List Nat := [1, 4, 1, 1, 2, 1, 4, 4, 4]
def baseStart_691069 : Nat := 118140960795 + 691069 * 2 ^ 59
def prefixEnd_691069 : Nat := 4983230072969 + 3 ^ 40 * 691069 * 2
def baseEnd_691069 : Nat := 78855680538235982902075

theorem tailTrace_691069 : CollatzResearch.WordTrace tailWord_691069 prefixEnd_691069 78855680538235982902075 := by
  unfold tailWord_691069
  simp only [CollatzResearch.WordTrace]
  refine ⟨25205357133382513033844261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16803571422255008689229507 25205357133382513033844261)
  ·
    refine ⟨4726004462509221193845799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25205357133382513033844261 4726004462509221193845799)
    ·
      refine ⟨7089006693763831790768699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4726004462509221193845799 7089006693763831790768699)
      ·
        refine ⟨10633510040645747686153049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7089006693763831790768699 10633510040645747686153049)
        ·
          refine ⟨7975132530484310764614787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10633510040645747686153049 7975132530484310764614787)
          ·
            refine ⟨11962698795726466146922181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7975132530484310764614787 11962698795726466146922181)
            ·
              refine ⟨2243006024198712402547909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11962698795726466146922181 2243006024198712402547909)
              ·
                refine ⟨420563629537258575477733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2243006024198712402547909 420563629537258575477733)
                ·
                  refine ⟨78855680538235982902075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 420563629537258575477733 78855680538235982902075)
                  ·
                    rfl

theorem cell22_691069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_691069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691069 prefixEnd_691069 := by exact prefixLift 691069
  have htrace : WordTrace (prefixWord ++ tailWord_691069) baseStart_691069 baseEnd_691069 := by
    simpa [prefixWord, tailWord_691069, baseEnd_691069] using wordTrace_append hprefix tailTrace_691069
  have hstable : (prefixWord ++ tailWord_691069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691069).length < 2 ^ (prefixWord ++ tailWord_691069).sum := by decide
  have hdescent : baseEnd_691069 < baseStart_691069 := by decide
  rcases family_descends (prefixWord ++ tailWord_691069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691084 : List Nat := [2, 2, 1, 2, 1, 2, 2, 5, 2, 3]
def baseStart_691084 : Nat := 118140960795 + 691084 * 2 ^ 59
def prefixEnd_691084 : Nat := 4983230072969 + 3 ^ 40 * 691084 * 2
def baseEnd_691084 : Nat := 236572176421252909581179

theorem tailTrace_691084 : CollatzResearch.WordTrace tailWord_691084 prefixEnd_691084 236572176421252909581179 := by
  unfold tailWord_691084
  simp only [CollatzResearch.WordTrace]
  refine ⟨12602952114164085297820153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16803936152218780397093537 12602952114164085297820153)
  ·
    refine ⟨9452214085623063973365115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12602952114164085297820153 9452214085623063973365115)
    ·
      refine ⟨14178321128434595960047673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9452214085623063973365115 14178321128434595960047673)
      ·
        refine ⟨10633740846325946970035755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14178321128434595960047673 10633740846325946970035755)
        ·
          refine ⟨15950611269488920455053633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10633740846325946970035755 15950611269488920455053633)
          ·
            refine ⟨11962958452116690341290225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15950611269488920455053633 11962958452116690341290225)
            ·
              refine ⟨8972218839087517755967669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11962958452116690341290225 8972218839087517755967669)
              ·
                refine ⟨841145516164454789621969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8972218839087517755967669 841145516164454789621969)
                ·
                  refine ⟨630859137123341092216477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 841145516164454789621969 630859137123341092216477)
                  ·
                    refine ⟨236572176421252909581179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 630859137123341092216477 236572176421252909581179)
                    ·
                      rfl

theorem cell22_691084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_691084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691084 prefixEnd_691084 := by exact prefixLift 691084
  have htrace : WordTrace (prefixWord ++ tailWord_691084) baseStart_691084 baseEnd_691084 := by
    simpa [prefixWord, tailWord_691084, baseEnd_691084] using wordTrace_append hprefix tailTrace_691084
  have hstable : (prefixWord ++ tailWord_691084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691084).length < 2 ^ (prefixWord ++ tailWord_691084).sum := by decide
  have hdescent : baseEnd_691084 < baseStart_691084 := by decide
  rcases family_descends (prefixWord ++ tailWord_691084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691219 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 4, 3]
def baseStart_691219 : Nat := 118140960795 + 691219 * 2 ^ 59
def prefixEnd_691219 : Nat := 4983230072969 + 3 ^ 40 * 691219 * 2
def baseEnd_691219 : Nat := 236618389680157557455765

theorem tailTrace_691219 : CollatzResearch.WordTrace tailWord_691219 prefixEnd_691219 236618389680157557455765 := by
  unfold tailWord_691219
  simp only [CollatzResearch.WordTrace]
  refine ⟨25210828082839088651804711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16807218721892725767869807 25210828082839088651804711)
  ·
    refine ⟨37816242124258632977707067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25210828082839088651804711 37816242124258632977707067)
    ·
      refine ⟨56724363186387949466560601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37816242124258632977707067 56724363186387949466560601)
      ·
        refine ⟨42543272389790962099920451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56724363186387949466560601 42543272389790962099920451)
        ·
          refine ⟨63814908584686443149880677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42543272389790962099920451 63814908584686443149880677)
          ·
            refine ⟨11965295359628708090602627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63814908584686443149880677 11965295359628708090602627)
            ·
              refine ⟨17947943039443062135903941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11965295359628708090602627 17947943039443062135903941)
              ·
                refine ⟨3365239319895574150481989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17947943039443062135903941 3365239319895574150481989)
                ·
                  refine ⟨630982372480420153215373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3365239319895574150481989 630982372480420153215373)
                  ·
                    refine ⟨236618389680157557455765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 630982372480420153215373 236618389680157557455765)
                    ·
                      rfl

theorem cell22_691219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 3].length) (baseStart_691219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691219 prefixEnd_691219 := by exact prefixLift 691219
  have htrace : WordTrace (prefixWord ++ tailWord_691219) baseStart_691219 baseEnd_691219 := by
    simpa [prefixWord, tailWord_691219, baseEnd_691219] using wordTrace_append hprefix tailTrace_691219
  have hstable : (prefixWord ++ tailWord_691219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691219).length < 2 ^ (prefixWord ++ tailWord_691219).sum := by decide
  have hdescent : baseEnd_691219 < baseStart_691219 := by decide
  rcases family_descends (prefixWord ++ tailWord_691219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691221 : List Nat := [1, 3, 2, 1, 4, 1, 1, 5, 4]
def baseStart_691221 : Nat := 118140960795 + 691221 * 2 ^ 59
def prefixEnd_691221 : Nat := 4983230072969 + 3 ^ 40 * 691221 * 2
def baseEnd_691221 : Nat := 78873024773676739635253

theorem tailTrace_691221 : CollatzResearch.WordTrace tailWord_691221 prefixEnd_691221 78873024773676739635253 := by
  unfold tailWord_691221
  simp only [CollatzResearch.WordTrace]
  refine ⟨25210901028831842993377517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16807267352554561995585011 25210901028831842993377517)
  ·
    refine ⟨9454087885811941122516569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25210901028831842993377517 9454087885811941122516569)
    ·
      refine ⟨7090565914358955841887427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9454087885811941122516569 7090565914358955841887427)
      ·
        refine ⟨10635848871538433762831141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7090565914358955841887427 10635848871538433762831141)
        ·
          refine ⟨1994221663413456330530839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10635848871538433762831141 1994221663413456330530839)
          ·
            refine ⟨2991332495120184495796259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1994221663413456330530839 2991332495120184495796259)
            ·
              refine ⟨4486998742680276743694389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2991332495120184495796259 4486998742680276743694389)
              ·
                refine ⟨420656132126275944721349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4486998742680276743694389 420656132126275944721349)
                ·
                  refine ⟨78873024773676739635253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 420656132126275944721349 78873024773676739635253)
                  ·
                    rfl

theorem cell22_691221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 4].length) (baseStart_691221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691221 prefixEnd_691221 := by exact prefixLift 691221
  have htrace : WordTrace (prefixWord ++ tailWord_691221) baseStart_691221 baseEnd_691221 := by
    simpa [prefixWord, tailWord_691221, baseEnd_691221] using wordTrace_append hprefix tailTrace_691221
  have hstable : (prefixWord ++ tailWord_691221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691221).length < 2 ^ (prefixWord ++ tailWord_691221).sum := by decide
  have hdescent : baseEnd_691221 < baseStart_691221 := by decide
  rcases family_descends (prefixWord ++ tailWord_691221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691223 : List Nat := [1, 1, 3, 5, 1, 1, 4, 1, 1, 4]
def baseStart_691223 : Nat := 118140960795 + 691223 * 2 ^ 59
def prefixEnd_691223 : Nat := 4983230072969 + 3 ^ 40 * 691223 * 2
def baseEnd_691223 : Nat := 236619758961902880355753

theorem tailTrace_691223 : CollatzResearch.WordTrace tailWord_691223 prefixEnd_691223 236619758961902880355753 := by
  unfold tailWord_691223
  simp only [CollatzResearch.WordTrace]
  refine ⟨25210973974824597334950323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16807315983216398223300215 25210973974824597334950323)
  ·
    refine ⟨37816460962236896002425485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25210973974824597334950323 37816460962236896002425485)
    ·
      refine ⟨14181172860838836000909557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37816460962236896002425485 14181172860838836000909557)
      ·
        refine ⟨1329484955703640875085271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14181172860838836000909557 1329484955703640875085271)
        ·
          refine ⟨1994227433555461312627907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1329484955703640875085271 1994227433555461312627907)
          ·
            refine ⟨2991341150333191968941861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1994227433555461312627907 2991341150333191968941861)
            ·
              refine ⟨560876465687473494176599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2991341150333191968941861 560876465687473494176599)
              ·
                refine ⟨841314698531210241264899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560876465687473494176599 841314698531210241264899)
                ·
                  refine ⟨1261972047796815361897349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 841314698531210241264899 1261972047796815361897349)
                  ·
                    refine ⟨236619758961902880355753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1261972047796815361897349 236619758961902880355753)
                    ·
                      rfl

theorem cell22_691223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 1, 4].length) (baseStart_691223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691223 prefixEnd_691223 := by exact prefixLift 691223
  have htrace : WordTrace (prefixWord ++ tailWord_691223) baseStart_691223 baseEnd_691223 := by
    simpa [prefixWord, tailWord_691223, baseEnd_691223] using wordTrace_append hprefix tailTrace_691223
  have hstable : (prefixWord ++ tailWord_691223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691223).length < 2 ^ (prefixWord ++ tailWord_691223).sum := by decide
  have hdescent : baseEnd_691223 < baseStart_691223 := by decide
  rcases family_descends (prefixWord ++ tailWord_691223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691304 : List Nat := [2, 1, 4, 4, 2, 1, 2, 1, 2, 3]
def baseStart_691304 : Nat := 118140960795 + 691304 * 2 ^ 59
def prefixEnd_691304 : Nat := 4983230072969 + 3 ^ 40 * 691304 * 2
def baseEnd_691304 : Nat := 236647486917245669080505

theorem tailTrace_691304 : CollatzResearch.WordTrace tailWord_691304 prefixEnd_691304 236647486917245669080505 := by
  unfold tailWord_691304
  simp only [CollatzResearch.WordTrace]
  refine ⟨12606964143765574084324483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16809285525020765445765977 12606964143765574084324483)
  ·
    refine ⟨18910446215648361126486725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12606964143765574084324483 18910446215648361126486725)
    ·
      refine ⟨3545708665434067711216261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18910446215648361126486725 3545708665434067711216261)
      ·
        refine ⟨664820374768887695853049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3545708665434067711216261 664820374768887695853049)
        ·
          refine ⟨498615281076665771889787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 664820374768887695853049 498615281076665771889787)
          ·
            refine ⟨747922921614998657834681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498615281076665771889787 747922921614998657834681)
            ·
              refine ⟨560942191211248993376011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 747922921614998657834681 560942191211248993376011)
              ·
                refine ⟨841413286816873490064017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560942191211248993376011 841413286816873490064017)
                ·
                  refine ⟨631059965112655117548013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 841413286816873490064017 631059965112655117548013)
                  ·
                    refine ⟨236647486917245669080505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 631059965112655117548013 236647486917245669080505)
                    ·
                      rfl

theorem cell22_691304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_691304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691304 prefixEnd_691304 := by exact prefixLift 691304
  have htrace : WordTrace (prefixWord ++ tailWord_691304) baseStart_691304 baseEnd_691304 := by
    simpa [prefixWord, tailWord_691304, baseEnd_691304] using wordTrace_append hprefix tailTrace_691304
  have hstable : (prefixWord ++ tailWord_691304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691304).length < 2 ^ (prefixWord ++ tailWord_691304).sum := by decide
  have hdescent : baseEnd_691304 < baseStart_691304 := by decide
  rcases family_descends (prefixWord ++ tailWord_691304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691358 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_691358 : Nat := 118140960795 + 691358 * 2 ^ 59
def prefixEnd_691358 : Nat := 4983230072969 + 3 ^ 40 * 691358 * 2
def baseEnd_691358 : Nat := 236665972220807528230339

theorem tailTrace_691358 : CollatzResearch.WordTrace tailWord_691358 prefixEnd_691358 236665972220807528230339 := by
  unfold tailWord_691358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3151987228666939423889341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16810598552890343594076485 3151987228666939423889341)
  ·
    refine ⟨1181995210750102283958503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3151987228666939423889341 1181995210750102283958503)
    ·
      refine ⟨1772992816125153425937755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1181995210750102283958503 1772992816125153425937755)
      ·
        refine ⟨2659489224187730138906633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1772992816125153425937755 2659489224187730138906633)
        ·
          refine ⟨1994616918140797604179975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2659489224187730138906633 1994616918140797604179975)
          ·
            refine ⟨2991925377211196406269963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1994616918140797604179975 2991925377211196406269963)
            ·
              refine ⟨4487888065816794609404945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2991925377211196406269963 4487888065816794609404945)
              ·
                refine ⟨3365916049362595957053709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4487888065816794609404945 3365916049362595957053709)
                ·
                  refine ⟨1262218518510973483895141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3365916049362595957053709 1262218518510973483895141)
                  ·
                    refine ⟨236665972220807528230339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1262218518510973483895141 236665972220807528230339)
                    ·
                      rfl

theorem cell22_691358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_691358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691358 prefixEnd_691358 := by exact prefixLift 691358
  have htrace : WordTrace (prefixWord ++ tailWord_691358) baseStart_691358 baseEnd_691358 := by
    simpa [prefixWord, tailWord_691358, baseEnd_691358] using wordTrace_append hprefix tailTrace_691358
  have hstable : (prefixWord ++ tailWord_691358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691358).length < 2 ^ (prefixWord ++ tailWord_691358).sum := by decide
  have hdescent : baseEnd_691358 < baseStart_691358 := by decide
  rcases family_descends (prefixWord ++ tailWord_691358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691373 : List Nat := [1, 5, 2, 1, 3, 1, 1, 2, 6]
def baseStart_691373 : Nat := 118140960795 + 691373 * 2 ^ 59
def prefixEnd_691373 : Nat := 4983230072969 + 3 ^ 40 * 691373 * 2
def baseEnd_691373 : Nat := 78890369009117496368431

theorem tailTrace_691373 : CollatzResearch.WordTrace tailWord_691373 prefixEnd_691373 78890369009117496368431 := by
  unfold tailWord_691373
  simp only [CollatzResearch.WordTrace]
  refine ⟨25216444924281172952910773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16810963282854115301940515 25216444924281172952910773)
  ·
    refine ⟨2364041711651359964335385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25216444924281172952910773 2364041711651359964335385)
    ·
      refine ⟨1773031283738519973251539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2364041711651359964335385 1773031283738519973251539)
      ·
        refine ⟨2659546925607779959877309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1773031283738519973251539 2659546925607779959877309)
        ·
          refine ⟨997330097102917484953991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2659546925607779959877309 997330097102917484953991)
          ·
            refine ⟨1495995145654376227430987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997330097102917484953991 1495995145654376227430987)
            ·
              refine ⟨2243992718481564341146481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495995145654376227430987 2243992718481564341146481)
              ·
                refine ⟨1682994538861173255859861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2243992718481564341146481 1682994538861173255859861)
                ·
                  refine ⟨78890369009117496368431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1682994538861173255859861 78890369009117496368431)
                  ·
                    rfl

theorem cell22_691373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_691373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691373 prefixEnd_691373 := by exact prefixLift 691373
  have htrace : WordTrace (prefixWord ++ tailWord_691373) baseStart_691373 baseEnd_691373 := by
    simpa [prefixWord, tailWord_691373, baseEnd_691373] using wordTrace_append hprefix tailTrace_691373
  have hstable : (prefixWord ++ tailWord_691373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691373).length < 2 ^ (prefixWord ++ tailWord_691373).sum := by decide
  have hdescent : baseEnd_691373 < baseStart_691373 := by decide
  rcases family_descends (prefixWord ++ tailWord_691373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691390 : List Nat := [4, 2, 1, 1, 3, 2, 2, 3, 4]
def baseStart_691390 : Nat := 118140960795 + 691390 * 2 ^ 59
def prefixEnd_691390 : Nat := 4983230072969 + 3 ^ 40 * 691390 * 2
def baseEnd_691390 : Nat := 78892308824923370476747

theorem tailTrace_691390 : CollatzResearch.WordTrace tailWord_691390 prefixEnd_691390 78892308824923370476747 := by
  unfold tailWord_691390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3152133120652448107034953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16811376643479723237519749 3152133120652448107034953)
  ·
    refine ⟨2364099840489336080276215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3152133120652448107034953 2364099840489336080276215)
    ·
      refine ⟨3546149760734004120414323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2364099840489336080276215 3546149760734004120414323)
      ·
        refine ⟨5319224641101006180621485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3546149760734004120414323 5319224641101006180621485)
        ·
          refine ⟨1994709240412877317733057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5319224641101006180621485 1994709240412877317733057)
          ·
            refine ⟨1496031930309657988299793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1994709240412877317733057 1496031930309657988299793)
            ·
              refine ⟨1122023947732243491224845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1496031930309657988299793 1122023947732243491224845)
              ·
                refine ⟨420758980399591309209317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1122023947732243491224845 420758980399591309209317)
                ·
                  refine ⟨78892308824923370476747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 420758980399591309209317 78892308824923370476747)
                  ·
                    rfl

theorem cell22_691390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_691390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691390 prefixEnd_691390 := by exact prefixLift 691390
  have htrace : WordTrace (prefixWord ++ tailWord_691390) baseStart_691390 baseEnd_691390 := by
    simpa [prefixWord, tailWord_691390, baseEnd_691390] using wordTrace_append hprefix tailTrace_691390
  have hstable : (prefixWord ++ tailWord_691390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691390).length < 2 ^ (prefixWord ++ tailWord_691390).sum := by decide
  have hdescent : baseEnd_691390 < baseStart_691390 := by decide
  rcases family_descends (prefixWord ++ tailWord_691390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691392 : List Nat := [2, 1, 1, 2, 7, 1, 2, 1, 1, 4]
def baseStart_691392 : Nat := 118140960795 + 691392 * 2 ^ 59
def prefixEnd_691392 : Nat := 4983230072969 + 3 ^ 40 * 691392 * 2
def baseEnd_691392 : Nat := 236677611115642772880235

theorem tailTrace_691392 : CollatzResearch.WordTrace tailWord_691392 prefixEnd_691392 236677611115642772880235 := by
  unfold tailWord_691392
  simp only [CollatzResearch.WordTrace]
  refine ⟨12608568955606169598926215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16811425274141559465234953 12608568955606169598926215)
  ·
    refine ⟨18912853433409254398389323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12608568955606169598926215 18912853433409254398389323)
    ·
      refine ⟨28369280150113881597583985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18912853433409254398389323 28369280150113881597583985)
      ·
        refine ⟨21276960112585411198187989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28369280150113881597583985 21276960112585411198187989)
        ·
          refine ⟨498678752638720574957531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 21276960112585411198187989 498678752638720574957531)
          ·
            refine ⟨748018128958080862436297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498678752638720574957531 748018128958080862436297)
            ·
              refine ⟨561013596718560646827223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 748018128958080862436297 561013596718560646827223)
              ·
                refine ⟨841520395077840970240835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561013596718560646827223 841520395077840970240835)
                ·
                  refine ⟨1262280592616761455361253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 841520395077840970240835 1262280592616761455361253)
                  ·
                    refine ⟨236677611115642772880235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1262280592616761455361253 236677611115642772880235)
                    ·
                      rfl

theorem cell22_691392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 1, 4].length) (baseStart_691392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691392 prefixEnd_691392 := by exact prefixLift 691392
  have htrace : WordTrace (prefixWord ++ tailWord_691392) baseStart_691392 baseEnd_691392 := by
    simpa [prefixWord, tailWord_691392, baseEnd_691392] using wordTrace_append hprefix tailTrace_691392
  have hstable : (prefixWord ++ tailWord_691392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691392).length < 2 ^ (prefixWord ++ tailWord_691392).sum := by decide
  have hdescent : baseEnd_691392 < baseStart_691392 := by decide
  rcases family_descends (prefixWord ++ tailWord_691392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691399 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 1, 9]
def baseStart_691399 : Nat := 118140960795 + 691399 * 2 ^ 59
def prefixEnd_691399 : Nat := 4983230072969 + 3 ^ 40 * 691399 * 2
def baseEnd_691399 : Nat := 236680007358697087955213

theorem tailTrace_691399 : CollatzResearch.WordTrace tailWord_691399 prefixEnd_691399 236680007358697087955213 := by
  unfold tailWord_691399
  simp only [CollatzResearch.WordTrace]
  refine ⟨25217393222186979393357251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16811595481457986262238167 25217393222186979393357251)
  ·
    refine ⟨37826089833280469090035877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25217393222186979393357251 37826089833280469090035877)
    ·
      refine ⟨7092391843740087954381727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37826089833280469090035877 7092391843740087954381727)
      ·
        refine ⟨10638587765610131931572591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7092391843740087954381727 10638587765610131931572591)
        ·
          refine ⟨15957881648415197897358887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10638587765610131931572591 15957881648415197897358887)
          ·
            refine ⟨23936822472622796846038331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15957881648415197897358887 23936822472622796846038331)
            ·
              refine ⟨35905233708934195269057497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23936822472622796846038331 35905233708934195269057497)
              ·
                refine ⟨26928925281700646451793123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35905233708934195269057497 26928925281700646451793123)
                ·
                  refine ⟨40393387922550969677689685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26928925281700646451793123 40393387922550969677689685)
                  ·
                    refine ⟨236680007358697087955213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 40393387922550969677689685 236680007358697087955213)
                    ·
                      rfl

theorem cell22_691399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_691399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691399 prefixEnd_691399 := by exact prefixLift 691399
  have htrace : WordTrace (prefixWord ++ tailWord_691399) baseStart_691399 baseEnd_691399 := by
    simpa [prefixWord, tailWord_691399, baseEnd_691399] using wordTrace_append hprefix tailTrace_691399
  have hstable : (prefixWord ++ tailWord_691399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691399).length < 2 ^ (prefixWord ++ tailWord_691399).sum := by decide
  have hdescent : baseEnd_691399 < baseStart_691399 := by decide
  rcases family_descends (prefixWord ++ tailWord_691399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691467 : List Nat := [1, 1, 1, 1, 5, 4, 3, 2, 1, 3]
def baseStart_691467 : Nat := 118140960795 + 691467 * 2 ^ 59
def prefixEnd_691467 : Nat := 4983230072969 + 3 ^ 40 * 691467 * 2
def baseEnd_691467 : Nat := 236703285148367577255005

theorem tailTrace_691467 : CollatzResearch.WordTrace tailWord_691467 prefixEnd_691467 236703285148367577255005 := by
  unfold tailWord_691467
  simp only [CollatzResearch.WordTrace]
  refine ⟨25219873385940627006832655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16813248923960418004555103 25219873385940627006832655)
  ·
    refine ⟨37829810078910940510248983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25219873385940627006832655 37829810078910940510248983)
    ·
      refine ⟨56744715118366410765373475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37829810078910940510248983 56744715118366410765373475)
      ·
        refine ⟨85117072677549616148060213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56744715118366410765373475 85117072677549616148060213)
        ·
          refine ⟨7979725563520276513880645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85117072677549616148060213 7979725563520276513880645)
          ·
            refine ⟨1496198543160051846352621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7979725563520276513880645 1496198543160051846352621)
            ·
              refine ⟨561074453685019442382233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1496198543160051846352621 561074453685019442382233)
              ·
                refine ⟨420805840263764581786675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 561074453685019442382233 420805840263764581786675)
                ·
                  refine ⟨631208760395646872680013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 420805840263764581786675 631208760395646872680013)
                  ·
                    refine ⟨236703285148367577255005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 631208760395646872680013 236703285148367577255005)
                    ·
                      rfl

theorem cell22_691467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 1, 3].length) (baseStart_691467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691467 prefixEnd_691467 := by exact prefixLift 691467
  have htrace : WordTrace (prefixWord ++ tailWord_691467) baseStart_691467 baseEnd_691467 := by
    simpa [prefixWord, tailWord_691467, baseEnd_691467] using wordTrace_append hprefix tailTrace_691467
  have hstable : (prefixWord ++ tailWord_691467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691467).length < 2 ^ (prefixWord ++ tailWord_691467).sum := by decide
  have hdescent : baseEnd_691467 < baseStart_691467 := by decide
  rcases family_descends (prefixWord ++ tailWord_691467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691480 : List Nat := [2, 1, 2, 3, 1, 5, 2, 1, 5]
def baseStart_691480 : Nat := 118140960795 + 691480 * 2 ^ 59
def prefixEnd_691480 : Nat := 4983230072969 + 3 ^ 40 * 691480 * 2
def baseEnd_691480 : Nat := 78902578438013292226655

theorem tailTrace_691480 : CollatzResearch.WordTrace tailWord_691480 prefixEnd_691480 78902578438013292226655 := by
  unfold tailWord_691480
  simp only [CollatzResearch.WordTrace]
  refine ⟨12610173767446765113527947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16813565023262353484703929 12610173767446765113527947)
  ·
    refine ⟨18915260651170147670291921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12610173767446765113527947 18915260651170147670291921)
    ·
      refine ⟨14186445488377610752718941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18915260651170147670291921 14186445488377610752718941)
      ·
        refine ⟨5319917058141604032269603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14186445488377610752718941 5319917058141604032269603)
        ·
          refine ⟨7979875587212406048404405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5319917058141604032269603 7979875587212406048404405)
          ·
            refine ⟨748113336301163067037913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7979875587212406048404405 748113336301163067037913)
            ·
              refine ⟨561085002225872300278435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 748113336301163067037913 561085002225872300278435)
              ·
                refine ⟨841627503338808450417653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561085002225872300278435 841627503338808450417653)
                ·
                  refine ⟨78902578438013292226655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 841627503338808450417653 78902578438013292226655)
                  ·
                    rfl

theorem cell22_691480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 5].length) (baseStart_691480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691480 prefixEnd_691480 := by exact prefixLift 691480
  have htrace : WordTrace (prefixWord ++ tailWord_691480) baseStart_691480 baseEnd_691480 := by
    simpa [prefixWord, tailWord_691480, baseEnd_691480] using wordTrace_append hprefix tailTrace_691480
  have hstable : (prefixWord ++ tailWord_691480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691480).length < 2 ^ (prefixWord ++ tailWord_691480).sum := by decide
  have hdescent : baseEnd_691480 < baseStart_691480 := by decide
  rcases family_descends (prefixWord ++ tailWord_691480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691493 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 3, 4]
def baseStart_691493 : Nat := 118140960795 + 691493 * 2 ^ 59
def prefixEnd_691493 : Nat := 4983230072969 + 3 ^ 40 * 691493 * 2
def baseEnd_691493 : Nat := 236712185479712176104925

theorem tailTrace_691493 : CollatzResearch.WordTrace tailWord_691493 prefixEnd_691493 236712185479712176104925 := by
  unfold tailWord_691493
  simp only [CollatzResearch.WordTrace]
  refine ⟨25220821683846433447279133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16813881122564288964852755 25220821683846433447279133)
  ·
    refine ⟨9457808131442412542729675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25220821683846433447279133 9457808131442412542729675)
    ·
      refine ⟨14186712197163618814094513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9457808131442412542729675 14186712197163618814094513)
      ·
        refine ⟨10640034147872714110570885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14186712197163618814094513 10640034147872714110570885)
        ·
          refine ⟨1995006402726133895732041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10640034147872714110570885 1995006402726133895732041)
          ·
            refine ⟨1496254802044600421799031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1995006402726133895732041 1496254802044600421799031)
            ·
              refine ⟨2244382203066900632698547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1496254802044600421799031 2244382203066900632698547)
              ·
                refine ⟨3366573304600350949047821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2244382203066900632698547 3366573304600350949047821)
                ·
                  refine ⟨1262464989225131605892933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3366573304600350949047821 1262464989225131605892933)
                  ·
                    refine ⟨236712185479712176104925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1262464989225131605892933 236712185479712176104925)
                    ·
                      rfl

theorem cell22_691493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_691493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691493 prefixEnd_691493 := by exact prefixLift 691493
  have htrace : WordTrace (prefixWord ++ tailWord_691493) baseStart_691493 baseEnd_691493 := by
    simpa [prefixWord, tailWord_691493, baseEnd_691493] using wordTrace_append hprefix tailTrace_691493
  have hstable : (prefixWord ++ tailWord_691493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691493).length < 2 ^ (prefixWord ++ tailWord_691493).sum := by decide
  have hdescent : baseEnd_691493 < baseStart_691493 := by decide
  rcases family_descends (prefixWord ++ tailWord_691493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691540 : List Nat := [2, 4, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_691540 : Nat := 118140960795 + 691540 * 2 ^ 59
def prefixEnd_691540 : Nat := 4983230072969 + 3 ^ 40 * 691540 * 2
def baseEnd_691540 : Nat := 236728274540219720179781

theorem tailTrace_691540 : CollatzResearch.WordTrace tailWord_691540 prefixEnd_691540 236728274540219720179781 := by
  unfold tailWord_691540
  simp only [CollatzResearch.WordTrace]
  refine ⟨12611267957338080237120037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16815023943117440316160049 12611267957338080237120037)
  ·
    refine ⟨2364612742000890044460007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12611267957338080237120037 2364612742000890044460007)
    ·
      refine ⟨3546919113001335066690011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2364612742000890044460007 3546919113001335066690011)
      ·
        refine ⟨5320378669502002600035017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3546919113001335066690011 5320378669502002600035017)
        ·
          refine ⟨3990284002126501950026263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5320378669502002600035017 3990284002126501950026263)
          ·
            refine ⟨5985426003189752925039395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3990284002126501950026263 5985426003189752925039395)
            ·
              refine ⟨8978139004784629387559093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5985426003189752925039395 8978139004784629387559093)
              ·
                refine ⟨841700531698559005083665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8978139004784629387559093 841700531698559005083665)
                ·
                  refine ⟨631275398773919253812749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 841700531698559005083665 631275398773919253812749)
                  ·
                    refine ⟨236728274540219720179781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 631275398773919253812749 236728274540219720179781)
                    ·
                      rfl

theorem cell22_691540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_691540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691540 prefixEnd_691540 := by exact prefixLift 691540
  have htrace : WordTrace (prefixWord ++ tailWord_691540) baseStart_691540 baseEnd_691540 := by
    simpa [prefixWord, tailWord_691540, baseEnd_691540] using wordTrace_append hprefix tailTrace_691540
  have hstable : (prefixWord ++ tailWord_691540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691540).length < 2 ^ (prefixWord ++ tailWord_691540).sum := by decide
  have hdescent : baseEnd_691540 < baseStart_691540 := by decide
  rcases family_descends (prefixWord ++ tailWord_691540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691555 : List Nat := [1, 1, 1, 5, 2, 4, 1, 1, 2, 4]
def baseStart_691555 : Nat := 118140960795 + 691555 * 2 ^ 59
def prefixEnd_691555 : Nat := 4983230072969 + 3 ^ 40 * 691555 * 2
def baseEnd_691555 : Nat := 236733409346764681054735

theorem tailTrace_691555 : CollatzResearch.WordTrace tailWord_691555 prefixEnd_691555 236733409346764681054735 := by
  unfold tailWord_691555
  simp only [CollatzResearch.WordTrace]
  refine ⟨25223083009621818036036119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16815388673081212024024079 25223083009621818036036119)
  ·
    refine ⟨37834624514432727054054179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25223083009621818036036119 37834624514432727054054179)
    ·
      refine ⟨56751936771649090581081269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37834624514432727054054179 56751936771649090581081269)
      ·
        refine ⟨5320494072342102241976369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56751936771649090581081269 5320494072342102241976369)
        ·
          refine ⟨3990370554256576681482277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5320494072342102241976369 3990370554256576681482277)
          ·
            refine ⟨748194478923108127777927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3990370554256576681482277 748194478923108127777927)
            ·
              refine ⟨1122291718384662191666891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748194478923108127777927 1122291718384662191666891)
              ·
                refine ⟨1683437577576993287500337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122291718384662191666891 1683437577576993287500337)
                ·
                  refine ⟨1262578183182744965625253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1683437577576993287500337 1262578183182744965625253)
                  ·
                    refine ⟨236733409346764681054735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1262578183182744965625253 236733409346764681054735)
                    ·
                      rfl

theorem cell22_691555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 4].length) (baseStart_691555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691555 prefixEnd_691555 := by exact prefixLift 691555
  have htrace : WordTrace (prefixWord ++ tailWord_691555) baseStart_691555 baseEnd_691555 := by
    simpa [prefixWord, tailWord_691555, baseEnd_691555] using wordTrace_append hprefix tailTrace_691555
  have hstable : (prefixWord ++ tailWord_691555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691555).length < 2 ^ (prefixWord ++ tailWord_691555).sum := by decide
  have hdescent : baseEnd_691555 < baseStart_691555 := by decide
  rcases family_descends (prefixWord ++ tailWord_691555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691568 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 5, 3]
def baseStart_691568 : Nat := 118140960795 + 691568 * 2 ^ 59
def prefixEnd_691568 : Nat := 4983230072969 + 3 ^ 40 * 691568 * 2
def baseEnd_691568 : Nat := 236737859512436980479695

theorem tailTrace_691568 : CollatzResearch.WordTrace tailWord_691568 prefixEnd_691568 236737859512436980479695 := by
  unfold tailWord_691568
  simp only [CollatzResearch.WordTrace]
  refine ⟨12611778579287360628129679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16815704772383147504172905 12611778579287360628129679)
  ·
    refine ⟨18917667868931040942194519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12611778579287360628129679 18917667868931040942194519)
    ·
      refine ⟨28376501803396561413291779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18917667868931040942194519 28376501803396561413291779)
      ·
        refine ⟨42564752705094842119937669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28376501803396561413291779 42564752705094842119937669)
        ·
          refine ⟨7980891132205282897488313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42564752705094842119937669 7980891132205282897488313)
          ·
            refine ⟨5985668349153962173116235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7980891132205282897488313 5985668349153962173116235)
            ·
              refine ⟨8978502523730943259674353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5985668349153962173116235 8978502523730943259674353)
              ·
                refine ⟨6733876892798207444755765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8978502523730943259674353 6733876892798207444755765)
                ·
                  refine ⟨631300958699831947945853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6733876892798207444755765 631300958699831947945853)
                  ·
                    refine ⟨236737859512436980479695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 631300958699831947945853 236737859512436980479695)
                    ·
                      rfl

theorem cell22_691568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 5, 3].length) (baseStart_691568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691568 prefixEnd_691568 := by exact prefixLift 691568
  have htrace : WordTrace (prefixWord ++ tailWord_691568) baseStart_691568 baseEnd_691568 := by
    simpa [prefixWord, tailWord_691568, baseEnd_691568] using wordTrace_append hprefix tailTrace_691568
  have hstable : (prefixWord ++ tailWord_691568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691568).length < 2 ^ (prefixWord ++ tailWord_691568).sum := by decide
  have hdescent : baseEnd_691568 < baseStart_691568 := by decide
  rcases family_descends (prefixWord ++ tailWord_691568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691720 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 5, 3]
def baseStart_691720 : Nat := 118140960795 + 691720 * 2 ^ 59
def prefixEnd_691720 : Nat := 4983230072969 + 3 ^ 40 * 691720 * 2
def baseEnd_691720 : Nat := 236789892218759250679229

theorem tailTrace_691720 : CollatzResearch.WordTrace tailWord_691720 prefixEnd_691720 236789892218759250679229 := by
  unfold tailWord_691720
  simp only [CollatzResearch.WordTrace]
  refine ⟨12614550527012025607896307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16819400702682700810528409 12614550527012025607896307)
  ·
    refine ⟨18921825790518038411844461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12614550527012025607896307 18921825790518038411844461)
    ·
      refine ⟨7095684671444264404441673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18921825790518038411844461 7095684671444264404441673)
      ·
        refine ⟨5321763503583198303331255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7095684671444264404441673 5321763503583198303331255)
        ·
          refine ⟨7982645255374797454996883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5321763503583198303331255 7982645255374797454996883)
          ·
            refine ⟨11973967883062196182495325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7982645255374797454996883 11973967883062196182495325)
            ·
              refine ⟨4490237956148323568435747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11973967883062196182495325 4490237956148323568435747)
              ·
                refine ⟨6735356934222485352653621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4490237956148323568435747 6735356934222485352653621)
                ·
                  refine ⟨631439712583358001811277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6735356934222485352653621 631439712583358001811277)
                  ·
                    refine ⟨236789892218759250679229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 631439712583358001811277 236789892218759250679229)
                    ·
                      rfl

theorem cell22_691720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_691720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691720 prefixEnd_691720 := by exact prefixLift 691720
  have htrace : WordTrace (prefixWord ++ tailWord_691720) baseStart_691720 baseEnd_691720 := by
    simpa [prefixWord, tailWord_691720, baseEnd_691720] using wordTrace_append hprefix tailTrace_691720
  have hstable : (prefixWord ++ tailWord_691720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691720).length < 2 ^ (prefixWord ++ tailWord_691720).sum := by decide
  have hdescent : baseEnd_691720 < baseStart_691720 := by decide
  rcases family_descends (prefixWord ++ tailWord_691720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691724 : List Nat := [2, 2, 1, 2, 6, 1, 1, 1, 2, 4]
def baseStart_691724 : Nat := 118140960795 + 691724 * 2 ^ 59
def prefixEnd_691724 : Nat := 4983230072969 + 3 ^ 40 * 691724 * 2
def baseEnd_691724 : Nat := 236791261500504573579217

theorem tailTrace_691724 : CollatzResearch.WordTrace tailWord_691724 prefixEnd_691724 236791261500504573579217 := by
  unfold tailWord_691724
  simp only [CollatzResearch.WordTrace]
  refine ⟨12614623473004779949469113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16819497964006373265958817 12614623473004779949469113)
  ·
    refine ⟨9460967604753584962101835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12614623473004779949469113 9460967604753584962101835)
    ·
      refine ⟨14191451407130377443152753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9460967604753584962101835 14191451407130377443152753)
      ·
        refine ⟨10643588555347783082364565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14191451407130377443152753 10643588555347783082364565)
        ·
          refine ⟨498918213531927331985839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10643588555347783082364565 498918213531927331985839)
          ·
            refine ⟨748377320297890997978759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498918213531927331985839 748377320297890997978759)
            ·
              refine ⟨1122565980446836496968139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748377320297890997978759 1122565980446836496968139)
              ·
                refine ⟨1683848970670254745452209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122565980446836496968139 1683848970670254745452209)
                ·
                  refine ⟨1262886728002691059089157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1683848970670254745452209 1262886728002691059089157)
                  ·
                    refine ⟨236791261500504573579217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1262886728002691059089157 236791261500504573579217)
                    ·
                      rfl

theorem cell22_691724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 2, 4].length) (baseStart_691724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691724 prefixEnd_691724 := by exact prefixLift 691724
  have htrace : WordTrace (prefixWord ++ tailWord_691724) baseStart_691724 baseEnd_691724 := by
    simpa [prefixWord, tailWord_691724, baseEnd_691724] using wordTrace_append hprefix tailTrace_691724
  have hstable : (prefixWord ++ tailWord_691724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691724).length < 2 ^ (prefixWord ++ tailWord_691724).sum := by decide
  have hdescent : baseEnd_691724 < baseStart_691724 := by decide
  rcases family_descends (prefixWord ++ tailWord_691724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691754 : List Nat := [3, 1, 4, 1, 1, 1, 1, 6, 1, 3]
def baseStart_691754 : Nat := 118140960795 + 691754 * 2 ^ 59
def prefixEnd_691754 : Nat := 4983230072969 + 3 ^ 40 * 691754 * 2
def baseEnd_691754 : Nat := 236801531113594495329125

theorem tailTrace_691754 : CollatzResearch.WordTrace tailWord_691754 prefixEnd_691754 236801531113594495329125 := by
  unfold tailWord_691754
  simp only [CollatzResearch.WordTrace]
  refine ⟨6307585283975218755632579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16820227423933916681686877 6307585283975218755632579)
  ·
    refine ⟨9461377925962828133448869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6307585283975218755632579 9461377925962828133448869)
    ·
      refine ⟨1774008361118030275021663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9461377925962828133448869 1774008361118030275021663)
      ·
        refine ⟨2661012541677045412532495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1774008361118030275021663 2661012541677045412532495)
        ·
          refine ⟨3991518812515568118798743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2661012541677045412532495 3991518812515568118798743)
          ·
            refine ⟨5987278218773352178198115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3991518812515568118798743 5987278218773352178198115)
            ·
              refine ⟨8980917328160028267297173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5987278218773352178198115 8980917328160028267297173)
              ·
                refine ⟨420980499757501325029555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8980917328160028267297173 420980499757501325029555)
                ·
                  refine ⟨631470749636251987544333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 420980499757501325029555 631470749636251987544333)
                  ·
                    refine ⟨236801531113594495329125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 631470749636251987544333 236801531113594495329125)
                    ·
                      rfl

theorem cell22_691754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_691754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691754 prefixEnd_691754 := by exact prefixLift 691754
  have htrace : WordTrace (prefixWord ++ tailWord_691754) baseStart_691754 baseEnd_691754 := by
    simpa [prefixWord, tailWord_691754, baseEnd_691754] using wordTrace_append hprefix tailTrace_691754
  have hstable : (prefixWord ++ tailWord_691754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691754).length < 2 ^ (prefixWord ++ tailWord_691754).sum := by decide
  have hdescent : baseEnd_691754 < baseStart_691754 := by decide
  rcases family_descends (prefixWord ++ tailWord_691754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691765 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 2, 5]
def baseStart_691765 : Nat := 118140960795 + 691765 * 2 ^ 59
def prefixEnd_691765 : Nat := 4983230072969 + 3 ^ 40 * 691765 * 2
def baseEnd_691765 : Nat := 236805296638394133304091

theorem tailTrace_691765 : CollatzResearch.WordTrace tailWord_691765 prefixEnd_691765 236805296638394133304091 := by
  unfold tailWord_691765
  simp only [CollatzResearch.WordTrace]
  refine ⟨25230742338861023901180749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16820494892574015934120499 25230742338861023901180749)
  ·
    refine ⟨9461528377072883962942781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25230742338861023901180749 9461528377072883962942781)
    ·
      refine ⟨3548073141402331486103543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9461528377072883962942781 3548073141402331486103543)
      ·
        refine ⟨5322109712103497229155315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3548073141402331486103543 5322109712103497229155315)
        ·
          refine ⟨7983164568155245843732973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5322109712103497229155315 7983164568155245843732973)
          ·
            refine ⟨2993686713058217191399865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7983164568155245843732973 2993686713058217191399865)
            ·
              refine ⟨2245265034793662893549899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2993686713058217191399865 2245265034793662893549899)
              ·
                refine ⟨3367897552190494340324849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2245265034793662893549899 3367897552190494340324849)
                ·
                  refine ⟨2525923164142870755243637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3367897552190494340324849 2525923164142870755243637)
                  ·
                    refine ⟨236805296638394133304091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2525923164142870755243637 236805296638394133304091)
                    ·
                      rfl

theorem cell22_691765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_691765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691765 prefixEnd_691765 := by exact prefixLift 691765
  have htrace : WordTrace (prefixWord ++ tailWord_691765) baseStart_691765 baseEnd_691765 := by
    simpa [prefixWord, tailWord_691765, baseEnd_691765] using wordTrace_append hprefix tailTrace_691765
  have hstable : (prefixWord ++ tailWord_691765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691765).length < 2 ^ (prefixWord ++ tailWord_691765).sum := by decide
  have hdescent : baseEnd_691765 < baseStart_691765 := by decide
  rcases family_descends (prefixWord ++ tailWord_691765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691767 : List Nat := [1, 1, 3, 1, 2, 5, 3, 1, 5]
def baseStart_691767 : Nat := 118140960795 + 691767 * 2 ^ 59
def prefixEnd_691767 : Nat := 4983230072969 + 3 ^ 40 * 691767 * 2
def baseEnd_691767 : Nat := 78935327093088931584695

theorem tailTrace_691767 : CollatzResearch.WordTrace tailWord_691767 prefixEnd_691767 78935327093088931584695 := by
  unfold tailWord_691767
  simp only [CollatzResearch.WordTrace]
  refine ⟨25230815284853778242753555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16820543523235852161835703 25230815284853778242753555)
  ·
    refine ⟨37846222927280667364130333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25230815284853778242753555 37846222927280667364130333)
    ·
      refine ⟨14192333597730250261548875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37846222927280667364130333 14192333597730250261548875)
      ·
        refine ⟨21288500396595375392323313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14192333597730250261548875 21288500396595375392323313)
        ·
          refine ⟨15966375297446531544242485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21288500396595375392323313 15966375297446531544242485)
          ·
            refine ⟨1496847684135612332272733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15966375297446531544242485 1496847684135612332272733)
            ·
              refine ⟨561317881550854624602275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1496847684135612332272733 561317881550854624602275)
              ·
                refine ⟨841976822326281936903413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561317881550854624602275 841976822326281936903413)
                ·
                  refine ⟨78935327093088931584695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 841976822326281936903413 78935327093088931584695)
                  ·
                    rfl

theorem cell22_691767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 5].length) (baseStart_691767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691767 prefixEnd_691767 := by exact prefixLift 691767
  have htrace : WordTrace (prefixWord ++ tailWord_691767) baseStart_691767 baseEnd_691767 := by
    simpa [prefixWord, tailWord_691767, baseEnd_691767] using wordTrace_append hprefix tailTrace_691767
  have hstable : (prefixWord ++ tailWord_691767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691767).length < 2 ^ (prefixWord ++ tailWord_691767).sum := by decide
  have hdescent : baseEnd_691767 < baseStart_691767 := by decide
  rcases family_descends (prefixWord ++ tailWord_691767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691805 : List Nat := [1, 4, 4, 2, 1, 1, 3, 2, 1, 3]
def baseStart_691805 : Nat := 118140960795 + 691805 * 2 ^ 59
def prefixEnd_691805 : Nat := 4983230072969 + 3 ^ 40 * 691805 * 2
def baseEnd_691805 : Nat := 236818989455847362303969

theorem tailTrace_691805 : CollatzResearch.WordTrace tailWord_691805 prefixEnd_691805 236818989455847362303969 := by
  unfold tailWord_691805
  simp only [CollatzResearch.WordTrace]
  refine ⟨25232201258716110732636869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16821467505810740488424579 25232201258716110732636869)
  ·
    refine ⟨4731037736009270762369413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25232201258716110732636869 4731037736009270762369413)
    ·
      refine ⟨887069575501738267944265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4731037736009270762369413 887069575501738267944265)
      ·
        refine ⟨665302181626303700958199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 887069575501738267944265 665302181626303700958199)
        ·
          refine ⟨997953272439455551437299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 665302181626303700958199 997953272439455551437299)
          ·
            refine ⟨1496929908659183327155949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997953272439455551437299 1496929908659183327155949)
            ·
              refine ⟨561348715747193747683481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1496929908659183327155949 561348715747193747683481)
              ·
                refine ⟨421011536810395310762611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 561348715747193747683481 421011536810395310762611)
                ·
                  refine ⟨631517305215592966143917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421011536810395310762611 631517305215592966143917)
                  ·
                    refine ⟨236818989455847362303969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 631517305215592966143917 236818989455847362303969)
                    ·
                      rfl

theorem cell22_691805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_691805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691805 prefixEnd_691805 := by exact prefixLift 691805
  have htrace : WordTrace (prefixWord ++ tailWord_691805) baseStart_691805 baseEnd_691805 := by
    simpa [prefixWord, tailWord_691805, baseEnd_691805] using wordTrace_append hprefix tailTrace_691805
  have hstable : (prefixWord ++ tailWord_691805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691805).length < 2 ^ (prefixWord ++ tailWord_691805).sum := by decide
  have hdescent : baseEnd_691805 < baseStart_691805 := by decide
  rcases family_descends (prefixWord ++ tailWord_691805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691812 : List Nat := [2, 3, 1, 1, 2, 5, 1, 1, 6]
def baseStart_691812 : Nat := 118140960795 + 691812 * 2 ^ 59
def prefixEnd_691812 : Nat := 4983230072969 + 3 ^ 40 * 691812 * 2
def baseEnd_691812 : Nat := 78940461899633892459649

theorem tailTrace_691812 : CollatzResearch.WordTrace tailWord_691812 prefixEnd_691812 78940461899633892459649 := by
  unfold tailWord_691812
  simp only [CollatzResearch.WordTrace]
  refine ⟨12616228284845375464070845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16821637713127167285427793 12616228284845375464070845)
  ·
    refine ⟨4731085606817015799026567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12616228284845375464070845 4731085606817015799026567)
    ·
      refine ⟨7096628410225523698539851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4731085606817015799026567 7096628410225523698539851)
      ·
        refine ⟨10644942615338285547809777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7096628410225523698539851 10644942615338285547809777)
        ·
          refine ⟨7983706961503714160857333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10644942615338285547809777 7983706961503714160857333)
          ·
            refine ⟨748472527640973202580375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7983706961503714160857333 748472527640973202580375)
            ·
              refine ⟨1122708791461459803870563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748472527640973202580375 1122708791461459803870563)
              ·
                refine ⟨1684063187192189705805845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122708791461459803870563 1684063187192189705805845)
                ·
                  refine ⟨78940461899633892459649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1684063187192189705805845 78940461899633892459649)
                  ·
                    rfl

theorem cell22_691812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_691812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691812 prefixEnd_691812 := by exact prefixLift 691812
  have htrace : WordTrace (prefixWord ++ tailWord_691812) baseStart_691812 baseEnd_691812 := by
    simpa [prefixWord, tailWord_691812, baseEnd_691812] using wordTrace_append hprefix tailTrace_691812
  have hstable : (prefixWord ++ tailWord_691812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691812).length < 2 ^ (prefixWord ++ tailWord_691812).sum := by decide
  have hdescent : baseEnd_691812 < baseStart_691812 := by decide
  rcases family_descends (prefixWord ++ tailWord_691812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
