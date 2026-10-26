import V185TrunkScan23Chunk0865

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5125202 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_5125202 : Nat := 118140960795 + 5125202 * 2 ^ 59
def prefixEnd_5125202 : Nat := 4983230072969 + 3 ^ 40 * 5125202 * 2
def baseEnd_5125202 : Nat := 2631692077384761857304631

theorem tailTrace_5125202 : CollatzResearch.WordTrace tailWord_5125202 prefixEnd_5125202 2631692077384761857304631 := by
  unfold tailWord_5125202
  simp only [CollatzResearch.WordTrace]
  refine ⟨46732868494568985914834465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124620982652183962439558573 46732868494568985914834465)
  ·
    refine ⟨35049651370926739436125849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46732868494568985914834465 35049651370926739436125849)
    ·
      refine ⟨26287238528195054577094387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35049651370926739436125849 26287238528195054577094387)
      ·
        refine ⟨39430857792292581865641581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26287238528195054577094387 39430857792292581865641581)
        ·
          refine ⟨14786571672109718199615593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39430857792292581865641581 14786571672109718199615593)
          ·
            refine ⟨11089928754082288649711695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14786571672109718199615593 11089928754082288649711695)
            ·
              refine ⟨16634893131123432974567543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11089928754082288649711695 16634893131123432974567543)
              ·
                refine ⟨24952339696685149461851315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16634893131123432974567543 24952339696685149461851315)
                ·
                  refine ⟨37428509545027724192776973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24952339696685149461851315 37428509545027724192776973)
                  ·
                    refine ⟨14035691079385396572291365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37428509545027724192776973 14035691079385396572291365)
                    ·
                      refine ⟨2631692077384761857304631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14035691079385396572291365 2631692077384761857304631)
                      ·
                        rfl

theorem cell23_5125202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_5125202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125202 prefixEnd_5125202 := by exact prefixLift 5125202
  have htrace : WordTrace (prefixWord ++ tailWord_5125202) baseStart_5125202 baseEnd_5125202 := by
    simpa [prefixWord, tailWord_5125202, baseEnd_5125202] using wordTrace_append hprefix tailTrace_5125202
  have hstable : (prefixWord ++ tailWord_5125202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125202).length < 2 ^ (prefixWord ++ tailWord_5125202).sum := by decide
  have hdescent : baseEnd_5125202 < baseStart_5125202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125212 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 5, 4]
def baseStart_5125212 : Nat := 118140960795 + 5125212 * 2 ^ 59
def prefixEnd_5125212 : Nat := 4983230072969 + 3 ^ 40 * 5125212 * 2
def baseEnd_5125212 : Nat := 877232404063768939393195

theorem tailTrace_5125212 : CollatzResearch.WordTrace tailWord_5125212 prefixEnd_5125212 877232404063768939393195 := by
  unfold tailWord_5125212
  simp only [CollatzResearch.WordTrace]
  refine ⟨93465919354119857683600945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124621225805493143578134593 93465919354119857683600945)
  ·
    refine ⟨70099439515589893262700709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93465919354119857683600945 70099439515589893262700709)
    ·
      refine ⟨13143644909173104986756383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70099439515589893262700709 13143644909173104986756383)
      ·
        refine ⟨19715467363759657480134575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13143644909173104986756383 19715467363759657480134575)
        ·
          refine ⟨29573201045639486220201863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19715467363759657480134575 29573201045639486220201863)
          ·
            refine ⟨44359801568459229330302795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29573201045639486220201863 44359801568459229330302795)
            ·
              refine ⟨66539702352688843995454193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44359801568459229330302795 66539702352688843995454193)
              ·
                refine ⟨49904776764516632996590645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66539702352688843995454193 49904776764516632996590645)
                ·
                  refine ⟨4678572821673434343430373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49904776764516632996590645 4678572821673434343430373)
                  ·
                    refine ⟨877232404063768939393195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4678572821673434343430373 877232404063768939393195)
                    ·
                      rfl

theorem cell23_5125212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_5125212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125212 prefixEnd_5125212 := by exact prefixLift 5125212
  have htrace : WordTrace (prefixWord ++ tailWord_5125212) baseStart_5125212 baseEnd_5125212 := by
    simpa [prefixWord, tailWord_5125212, baseEnd_5125212] using wordTrace_append hprefix tailTrace_5125212
  have hstable : (prefixWord ++ tailWord_5125212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125212).length < 2 ^ (prefixWord ++ tailWord_5125212).sum := by decide
  have hdescent : baseEnd_5125212 < baseStart_5125212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125225 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 8]
def baseStart_5125225 : Nat := 118140960795 + 5125225 * 2 ^ 59
def prefixEnd_5125225 : Nat := 4983230072969 + 3 ^ 40 * 5125225 * 2
def baseEnd_5125225 : Nat := 292411543048868363035225

theorem tailTrace_5125225 : CollatzResearch.WordTrace tailWord_5125225 prefixEnd_5125225 292411543048868363035225 := by
  unfold tailWord_5125225
  simp only [CollatzResearch.WordTrace]
  refine ⟨186932312857192618587425129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124621541904795079058283419 186932312857192618587425129)
  ·
    refine ⟨140199234642894463940568847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186932312857192618587425129 140199234642894463940568847)
    ·
      refine ⟨210298851964341695910853271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140199234642894463940568847 210298851964341695910853271)
      ·
        refine ⟨315448277946512543866279907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210298851964341695910853271 315448277946512543866279907)
        ·
          refine ⟨473172416919768815799419861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315448277946512543866279907 473172416919768815799419861)
          ·
            refine ⟨11089978521557081620298903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 473172416919768815799419861 11089978521557081620298903)
            ·
              refine ⟨16634967782335622430448355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11089978521557081620298903 16634967782335622430448355)
              ·
                refine ⟨24952451673503433645672533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16634967782335622430448355 24952451673503433645672533)
                ·
                  refine ⟨292411543048868363035225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24952451673503433645672533 292411543048868363035225)
                  ·
                    rfl

theorem cell23_5125225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 8].length) (baseStart_5125225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125225 prefixEnd_5125225 := by exact prefixLift 5125225
  have htrace : WordTrace (prefixWord ++ tailWord_5125225) baseStart_5125225 baseEnd_5125225 := by
    simpa [prefixWord, tailWord_5125225, baseEnd_5125225] using wordTrace_append hprefix tailTrace_5125225
  have hstable : (prefixWord ++ tailWord_5125225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125225).length < 2 ^ (prefixWord ++ tailWord_5125225).sum := by decide
  have hdescent : baseEnd_5125225 < baseStart_5125225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125229 : List Nat := [1, 5, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_5125229 : Nat := 118140960795 + 5125229 * 2 ^ 59
def prefixEnd_5125229 : Nat := 4983230072969 + 3 ^ 40 * 5125229 * 2
def baseEnd_5125229 : Nat := 877235313787477750555669

theorem tailTrace_5125229 : CollatzResearch.WordTrace tailWord_5125229 prefixEnd_5125229 877235313787477750555669 := by
  unfold tailWord_5125229
  simp only [CollatzResearch.WordTrace]
  refine ⟨186932458749178127270570741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124621639166118751513713827 186932458749178127270570741)
  ·
    refine ⟨17524918007735449431616007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 186932458749178127270570741 17524918007735449431616007)
    ·
      refine ⟨26287377011603174147424011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17524918007735449431616007 26287377011603174147424011)
      ·
        refine ⟨39431065517404761221136017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26287377011603174147424011 39431065517404761221136017)
        ·
          refine ⟨29573299138053570915852013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39431065517404761221136017 29573299138053570915852013)
          ·
            refine ⟨11089987176770089093444505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29573299138053570915852013 11089987176770089093444505)
            ·
              refine ⟨8317490382577566820083379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11089987176770089093444505 8317490382577566820083379)
              ·
                refine ⟨12476235573866350230125069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8317490382577566820083379 12476235573866350230125069)
                ·
                  refine ⟨4678588340199881336296901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12476235573866350230125069 4678588340199881336296901)
                  ·
                    refine ⟨877235313787477750555669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4678588340199881336296901 877235313787477750555669)
                    ·
                      rfl

theorem cell23_5125229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_5125229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125229 prefixEnd_5125229 := by exact prefixLift 5125229
  have htrace : WordTrace (prefixWord ++ tailWord_5125229) baseStart_5125229 baseEnd_5125229 := by
    simpa [prefixWord, tailWord_5125229, baseEnd_5125229] using wordTrace_append hprefix tailTrace_5125229
  have hstable : (prefixWord ++ tailWord_5125229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125229).length < 2 ^ (prefixWord ++ tailWord_5125229).sum := by decide
  have hdescent : baseEnd_5125229 < baseStart_5125229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125245 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_5125245 : Nat := 118140960795 + 5125245 * 2 ^ 59
def prefixEnd_5125245 : Nat := 4983230072969 + 3 ^ 40 * 5125245 * 2
def baseEnd_5125245 : Nat := 2631714157052905189066933

theorem tailTrace_5125245 : CollatzResearch.WordTrace tailWord_5125245 prefixEnd_5125245 2631714157052905189066933 := by
  unfold tailWord_5125245
  simp only [CollatzResearch.WordTrace]
  refine ⟨186933042317120162003153189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124622028211413441335435459 186933042317120162003153189)
  ·
    refine ⟨35049945434460030375591223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186933042317120162003153189 35049945434460030375591223)
    ·
      refine ⟨52574918151690045563386835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35049945434460030375591223 52574918151690045563386835)
      ·
        refine ⟨78862377227535068345080253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52574918151690045563386835 78862377227535068345080253)
        ·
          refine ⟨29573391460325650629405095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78862377227535068345080253 29573391460325650629405095)
          ·
            refine ⟨44360087190488475944107643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29573391460325650629405095 44360087190488475944107643)
            ·
              refine ⟨66540130785732713916161465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44360087190488475944107643 66540130785732713916161465)
              ·
                refine ⟨49905098089299535437121099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66540130785732713916161465 49905098089299535437121099)
                ·
                  refine ⟨74857647133949303155681649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49905098089299535437121099 74857647133949303155681649)
                  ·
                    refine ⟨56143235350461977366761237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74857647133949303155681649 56143235350461977366761237)
                    ·
                      refine ⟨2631714157052905189066933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56143235350461977366761237 2631714157052905189066933)
                      ·
                        rfl

theorem cell23_5125245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_5125245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125245 prefixEnd_5125245 := by exact prefixLift 5125245
  have htrace : WordTrace (prefixWord ++ tailWord_5125245) baseStart_5125245 baseEnd_5125245 := by
    simpa [prefixWord, tailWord_5125245, baseEnd_5125245] using wordTrace_append hprefix tailTrace_5125245
  have hstable : (prefixWord ++ tailWord_5125245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125245).length < 2 ^ (prefixWord ++ tailWord_5125245).sum := by decide
  have hdescent : baseEnd_5125245 < baseStart_5125245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125292 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 2, 6, 2]
def baseStart_5125292 : Nat := 118140960795 + 5125292 * 2 ^ 59
def prefixEnd_5125292 : Nat := 4983230072969 + 3 ^ 40 * 5125292 * 2
def baseEnd_5125292 : Nat := 2631738290643666505179217

theorem tailTrace_5125292 : CollatzResearch.WordTrace tailWord_5125292 prefixEnd_5125292 2631738290643666505179217 := by
  unfold tailWord_5125292
  simp only [CollatzResearch.WordTrace]
  refine ⟨93467378273974944515057065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124623171031966592686742753 93467378273974944515057065)
  ·
    refine ⟨70100533705481208386292799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93467378273974944515057065 70100533705481208386292799)
    ·
      refine ⟨105150800558221812579439199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70100533705481208386292799 105150800558221812579439199)
      ·
        refine ⟨157726200837332718869158799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105150800558221812579439199 157726200837332718869158799)
        ·
          refine ⟨236589301255999078303738199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157726200837332718869158799 236589301255999078303738199)
          ·
            refine ⟨354883951883998617455607299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236589301255999078303738199 354883951883998617455607299)
            ·
              refine ⟨532325927825997926183410949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354883951883998617455607299 532325927825997926183410949)
              ·
                refine ⟨99811111467374611159389553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 532325927825997926183410949 99811111467374611159389553)
                ·
                  refine ⟨74858333600530958369542165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99811111467374611159389553 74858333600530958369542165)
                  ·
                    refine ⟨3508984387524888673572289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74858333600530958369542165 3508984387524888673572289)
                    ·
                      refine ⟨2631738290643666505179217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3508984387524888673572289 2631738290643666505179217)
                      ·
                        rfl

theorem cell23_5125292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 6, 2].length) (baseStart_5125292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125292 prefixEnd_5125292 := by exact prefixLift 5125292
  have htrace : WordTrace (prefixWord ++ tailWord_5125292) baseStart_5125292 baseEnd_5125292 := by
    simpa [prefixWord, tailWord_5125292, baseEnd_5125292] using wordTrace_append hprefix tailTrace_5125292
  have hstable : (prefixWord ++ tailWord_5125292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125292).length < 2 ^ (prefixWord ++ tailWord_5125292).sum := by decide
  have hdescent : baseEnd_5125292 < baseStart_5125292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125293 : List Nat := [1, 5, 2, 1, 4, 1, 2, 1, 6]
def baseStart_5125293 : Nat := 118140960795 + 5125293 * 2 ^ 59
def prefixEnd_5125293 : Nat := 4983230072969 + 3 ^ 40 * 5125293 * 2
def baseEnd_5125293 : Nat := 292415422680480111251857

theorem tailTrace_5125293 : CollatzResearch.WordTrace tailWord_5125293 prefixEnd_5125293 292415422680480111251857 := by
  unfold tailWord_5125293
  simp only [CollatzResearch.WordTrace]
  refine ⟨186934793020946266200900533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124623195347297510800600355 186934793020946266200900533)
  ·
    refine ⟨17525136845713712456334425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 186934793020946266200900533 17525136845713712456334425)
    ·
      refine ⟨13143852634285284342250819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17525136845713712456334425 13143852634285284342250819)
      ·
        refine ⟨19715778951427926513376229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13143852634285284342250819 19715778951427926513376229)
        ·
          refine ⟨3696708553392736221258043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19715778951427926513376229 3696708553392736221258043)
          ·
            refine ⟨5545062830089104331887065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3696708553392736221258043 5545062830089104331887065)
            ·
              refine ⟨4158797122566828248915299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5545062830089104331887065 4158797122566828248915299)
              ·
                refine ⟨6238195683850242373372949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4158797122566828248915299 6238195683850242373372949)
                ·
                  refine ⟨292415422680480111251857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6238195683850242373372949 292415422680480111251857)
                  ·
                    rfl

theorem cell23_5125293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_5125293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125293 prefixEnd_5125293 := by exact prefixLift 5125293
  have htrace : WordTrace (prefixWord ++ tailWord_5125293) baseStart_5125293 baseEnd_5125293 := by
    simpa [prefixWord, tailWord_5125293, baseEnd_5125293] using wordTrace_append hprefix tailTrace_5125293
  have hstable : (prefixWord ++ tailWord_5125293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125293).length < 2 ^ (prefixWord ++ tailWord_5125293).sum := by decide
  have hdescent : baseEnd_5125293 < baseStart_5125293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125309 : List Nat := [1, 4, 1, 2, 1, 1, 5, 2, 1, 1, 4]
def baseStart_5125309 : Nat := 118140960795 + 5125309 * 2 ^ 59
def prefixEnd_5125309 : Nat := 4983230072969 + 3 ^ 40 * 5125309 * 2
def baseEnd_5125309 : Nat := 2631747019814792938666639

theorem tailTrace_5125309 : CollatzResearch.WordTrace tailWord_5125309 prefixEnd_5125309 2631747019814792938666639 := by
  unfold tailWord_5125309
  simp only [CollatzResearch.WordTrace]
  refine ⟨186935376588888300933482981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124623584392592200622321987 186935376588888300933482981)
  ·
    refine ⟨35050383110416556425028059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186935376588888300933482981 35050383110416556425028059)
    ·
      refine ⟨52575574665624834637542089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35050383110416556425028059 52575574665624834637542089)
      ·
        refine ⟨39431680999218625978156567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52575574665624834637542089 39431680999218625978156567)
        ·
          refine ⟨59147521498827938967234851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39431680999218625978156567 59147521498827938967234851)
          ·
            refine ⟨88721282248241908450852277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59147521498827938967234851 88721282248241908450852277)
            ·
              refine ⟨8317620210772678917267401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88721282248241908450852277 8317620210772678917267401)
              ·
                refine ⟨6238215158079509187950551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8317620210772678917267401 6238215158079509187950551)
                ·
                  refine ⟨9357322737119263781925827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6238215158079509187950551 9357322737119263781925827)
                  ·
                    refine ⟨14035984105678895672888741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9357322737119263781925827 14035984105678895672888741)
                    ·
                      refine ⟨2631747019814792938666639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14035984105678895672888741 2631747019814792938666639)
                      ·
                        rfl

theorem cell23_5125309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_5125309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125309 prefixEnd_5125309 := by exact prefixLift 5125309
  have htrace : WordTrace (prefixWord ++ tailWord_5125309) baseStart_5125309 baseEnd_5125309 := by
    simpa [prefixWord, tailWord_5125309, baseEnd_5125309] using wordTrace_append hprefix tailTrace_5125309
  have hstable : (prefixWord ++ tailWord_5125309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125309).length < 2 ^ (prefixWord ++ tailWord_5125309).sum := by decide
  have hdescent : baseEnd_5125309 < baseStart_5125309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125313 : List Nat := [1, 2, 6, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_5125313 : Nat := 118140960795 + 5125313 * 2 ^ 59
def prefixEnd_5125313 : Nat := 4983230072969 + 3 ^ 40 * 5125313 * 2
def baseEnd_5125313 : Nat := 2631749073737410923016621

theorem tailTrace_5125313 : CollatzResearch.WordTrace tailWord_5125313 prefixEnd_5125313 2631749073737410923016621 := by
  unfold tailWord_5125313
  simp only [CollatzResearch.WordTrace]
  refine ⟨186935522480873809616628593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124623681653915873077752395 186935522480873809616628593)
  ·
    refine ⟨140201641860655357212471445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186935522480873809616628593 140201641860655357212471445)
    ·
      refine ⟨6571951962218219869334599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 140201641860655357212471445 6571951962218219869334599)
      ·
        refine ⟨9857927943327329804001899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6571951962218219869334599 9857927943327329804001899)
        ·
          refine ⟨14786891914990994706002849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9857927943327329804001899 14786891914990994706002849)
          ·
            refine ⟨11090168936243246029502137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14786891914990994706002849 11090168936243246029502137)
            ·
              refine ⟨8317626702182434522126603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11090168936243246029502137 8317626702182434522126603)
              ·
                refine ⟨12476440053273651783189905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8317626702182434522126603 12476440053273651783189905)
                ·
                  refine ⟨9357330039955238837392429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12476440053273651783189905 9357330039955238837392429)
                  ·
                    refine ⟨3508998764983214564022161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9357330039955238837392429 3508998764983214564022161)
                    ·
                      refine ⟨2631749073737410923016621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3508998764983214564022161 2631749073737410923016621)
                      ·
                        rfl

theorem cell23_5125313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_5125313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125313 prefixEnd_5125313 := by exact prefixLift 5125313
  have htrace : WordTrace (prefixWord ++ tailWord_5125313) baseStart_5125313 baseEnd_5125313 := by
    simpa [prefixWord, tailWord_5125313, baseEnd_5125313] using wordTrace_append hprefix tailTrace_5125313
  have hstable : (prefixWord ++ tailWord_5125313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125313).length < 2 ^ (prefixWord ++ tailWord_5125313).sum := by decide
  have hdescent : baseEnd_5125313 < baseStart_5125313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125322 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_5125322 : Nat := 118140960795 + 5125322 * 2 ^ 59
def prefixEnd_5125322 : Nat := 4983230072969 + 3 ^ 40 * 5125322 * 2
def baseEnd_5125322 : Nat := 2631753695063301387804079

theorem tailTrace_5125322 : CollatzResearch.WordTrace tailWord_5125322 prefixEnd_5125322 2631753695063301387804079 := by
  unfold tailWord_5125322
  simp only [CollatzResearch.WordTrace]
  refine ⟨46733962684460301038426555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124623900491894136102470813 46733962684460301038426555)
  ·
    refine ⟨70100944026690451557639833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46733962684460301038426555 70100944026690451557639833)
    ·
      refine ⟨52575708020017838668229875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70100944026690451557639833 52575708020017838668229875)
      ·
        refine ⟨78863562030026758002344813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52575708020017838668229875 78863562030026758002344813)
        ·
          refine ⟨29573835761260034250879305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78863562030026758002344813 29573835761260034250879305)
          ·
            refine ⟨22180376820945025688159479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29573835761260034250879305 22180376820945025688159479)
            ·
              refine ⟨33270565231417538532239219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22180376820945025688159479 33270565231417538532239219)
              ·
                refine ⟨49905847847126307798358829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33270565231417538532239219 49905847847126307798358829)
                ·
                  refine ⟨18714692942672365424384561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49905847847126307798358829 18714692942672365424384561)
                  ·
                    refine ⟨14036019707004274068288421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18714692942672365424384561 14036019707004274068288421)
                    ·
                      refine ⟨2631753695063301387804079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14036019707004274068288421 2631753695063301387804079)
                      ·
                        rfl

theorem cell23_5125322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_5125322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125322 prefixEnd_5125322 := by exact prefixLift 5125322
  have htrace : WordTrace (prefixWord ++ tailWord_5125322) baseStart_5125322 baseEnd_5125322 := by
    simpa [prefixWord, tailWord_5125322, baseEnd_5125322] using wordTrace_append hprefix tailTrace_5125322
  have hstable : (prefixWord ++ tailWord_5125322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125322).length < 2 ^ (prefixWord ++ tailWord_5125322).sum := by decide
  have hdescent : baseEnd_5125322 < baseStart_5125322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125332 : List Nat := [2, 4, 1, 4, 12]
def baseStart_5125332 : Nat := 118140960795 + 5125332 * 2 ^ 59
def prefixEnd_5125332 : Nat := 4983230072969 + 3 ^ 40 * 5125332 * 2
def baseEnd_5125332 : Nat := 3610094416831064950177

theorem tailTrace_5125332 : CollatzResearch.WordTrace tailWord_5125332 prefixEnd_5125332 3610094416831064950177 := by
  unfold tailWord_5125332
  simp only [CollatzResearch.WordTrace]
  refine ⟨93468107733902487930785125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124624143645203317241046833 93468107733902487930785125)
  ·
    refine ⟨17525270200106716487022211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93468107733902487930785125 17525270200106716487022211)
    ·
      refine ⟨26287905300160074730533317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17525270200106716487022211 26287905300160074730533317)
      ·
        refine ⟨4928982243780014011974997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26287905300160074730533317 4928982243780014011974997)
        ·
          refine ⟨3610094416831064950177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4928982243780014011974997 3610094416831064950177)
          ·
            rfl

theorem cell23_5125332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 12].length) (baseStart_5125332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125332 prefixEnd_5125332 := by exact prefixLift 5125332
  have htrace : WordTrace (prefixWord ++ tailWord_5125332) baseStart_5125332 baseEnd_5125332 := by
    simpa [prefixWord, tailWord_5125332, baseEnd_5125332] using wordTrace_append hprefix tailTrace_5125332
  have hstable : (prefixWord ++ tailWord_5125332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125332).length < 2 ^ (prefixWord ++ tailWord_5125332).sum := by decide
  have hdescent : baseEnd_5125332 < baseStart_5125332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125336 : List Nat := [2, 1, 2, 2, 5, 1, 2, 2, 2, 4]
def baseStart_5125336 : Nat := 118140960795 + 5125336 * 2 ^ 59
def prefixEnd_5125336 : Nat := 4983230072969 + 3 ^ 40 * 5125336 * 2
def baseEnd_5125336 : Nat := 877253627930821444343005

theorem tailTrace_5125336 : CollatzResearch.WordTrace tailWord_5125336 prefixEnd_5125336 877253627930821444343005 := by
  unfold tailWord_5125336
  simp only [CollatzResearch.WordTrace]
  refine ⟨93468180679895242272357931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124624240906526989696477241 93468180679895242272357931)
  ·
    refine ⟨140202271019842863408536897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93468180679895242272357931 140202271019842863408536897)
    ·
      refine ⟨105151703264882147556402673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140202271019842863408536897 105151703264882147556402673)
      ·
        refine ⟨78863777448661610667302005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105151703264882147556402673 78863777448661610667302005)
        ·
          refine ⟨7393479135812026000059563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78863777448661610667302005 7393479135812026000059563)
          ·
            refine ⟨11090218703718039000089345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7393479135812026000059563 11090218703718039000089345)
            ·
              refine ⟨8317664027788529250067009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11090218703718039000089345 8317664027788529250067009)
              ·
                refine ⟨6238248020841396937550257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8317664027788529250067009 6238248020841396937550257)
                ·
                  refine ⟨4678686015631047703162693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6238248020841396937550257 4678686015631047703162693)
                  ·
                    refine ⟨877253627930821444343005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4678686015631047703162693 877253627930821444343005)
                    ·
                      rfl

theorem cell23_5125336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 2, 4].length) (baseStart_5125336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125336 prefixEnd_5125336 := by exact prefixLift 5125336
  have htrace : WordTrace (prefixWord ++ tailWord_5125336) baseStart_5125336 baseEnd_5125336 := by
    simpa [prefixWord, tailWord_5125336, baseEnd_5125336] using wordTrace_append hprefix tailTrace_5125336
  have hstable : (prefixWord ++ tailWord_5125336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125336).length < 2 ^ (prefixWord ++ tailWord_5125336).sum := by decide
  have hdescent : baseEnd_5125336 < baseStart_5125336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125349 : List Nat := [1, 3, 1, 4, 3, 2, 1, 8]
def baseStart_5125349 : Nat := 118140960795 + 5125349 * 2 ^ 59
def prefixEnd_5125349 : Nat := 4983230072969 + 3 ^ 40 * 5125349 * 2
def baseEnd_5125349 : Nat := 97472872557073066006165

theorem tailTrace_5125349 : CollatzResearch.WordTrace tailWord_5125349 prefixEnd_5125349 97472872557073066006165 := by
  unfold tailWord_5125349
  simp only [CollatzResearch.WordTrace]
  refine ⟨186936835508743387764939101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124624557005828925176626067 186936835508743387764939101)
  ·
    refine ⟨70101313315778770411852163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186936835508743387764939101 70101313315778770411852163)
    ·
      refine ⟨105151969973668155617778245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70101313315778770411852163 105151969973668155617778245)
      ·
        refine ⟨19715994370062779178333421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105151969973668155617778245 19715994370062779178333421)
        ·
          refine ⟨7393497888773542191875033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19715994370062779178333421 7393497888773542191875033)
          ·
            refine ⟨5545123416580156643906275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7393497888773542191875033 5545123416580156643906275)
            ·
              refine ⟨8317685124870234965859413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5545123416580156643906275 8317685124870234965859413)
              ·
                refine ⟨97472872557073066006165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8317685124870234965859413 97472872557073066006165)
                ·
                  rfl

theorem cell23_5125349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 8].length) (baseStart_5125349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125349 prefixEnd_5125349 := by exact prefixLift 5125349
  have htrace : WordTrace (prefixWord ++ tailWord_5125349) baseStart_5125349 baseEnd_5125349 := by
    simpa [prefixWord, tailWord_5125349, baseEnd_5125349] using wordTrace_append hprefix tailTrace_5125349
  have hstable : (prefixWord ++ tailWord_5125349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125349).length < 2 ^ (prefixWord ++ tailWord_5125349).sum := by decide
  have hdescent : baseEnd_5125349 < baseStart_5125349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125364 : List Nat := [2, 6, 1, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_5125364 : Nat := 118140960795 + 5125364 * 2 ^ 59
def prefixEnd_5125364 : Nat := 4983230072969 + 3 ^ 40 * 5125364 * 2
def baseEnd_5125364 : Nat := 2631775261250790223478887

theorem tailTrace_5125364 : CollatzResearch.WordTrace tailWord_5125364 prefixEnd_5125364 2631775261250790223478887 := by
  unfold tailWord_5125364
  simp only [CollatzResearch.WordTrace]
  refine ⟨93468691301844522663367573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124624921735792696884490097 93468691301844522663367573)
  ·
    refine ⟨4381344904773961999845355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93468691301844522663367573 4381344904773961999845355)
    ·
      refine ⟨6572017357160942999768033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4381344904773961999845355 6572017357160942999768033)
      ·
        refine ⟨4929013017870707249826025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6572017357160942999768033 4929013017870707249826025)
        ·
          refine ⟨3696759763403030437369519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4929013017870707249826025 3696759763403030437369519)
          ·
            refine ⟨5545139645104545656054279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3696759763403030437369519 5545139645104545656054279)
            ·
              refine ⟨8317709467656818484081419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5545139645104545656054279 8317709467656818484081419)
              ·
                refine ⟨12476564201485227726122129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8317709467656818484081419 12476564201485227726122129)
                ·
                  refine ⟨9357423151113920794591597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12476564201485227726122129 9357423151113920794591597)
                  ·
                    refine ⟨3509033681667720297971849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9357423151113920794591597 3509033681667720297971849)
                    ·
                      refine ⟨2631775261250790223478887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3509033681667720297971849 2631775261250790223478887)
                      ·
                        rfl

theorem cell23_5125364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_5125364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125364 prefixEnd_5125364 := by exact prefixLift 5125364
  have htrace : WordTrace (prefixWord ++ tailWord_5125364) baseStart_5125364 baseEnd_5125364 := by
    simpa [prefixWord, tailWord_5125364, baseEnd_5125364] using wordTrace_append hprefix tailTrace_5125364
  have hstable : (prefixWord ++ tailWord_5125364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125364).length < 2 ^ (prefixWord ++ tailWord_5125364).sum := by decide
  have hdescent : baseEnd_5125364 < baseStart_5125364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125369 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 3, 3, 2]
def baseStart_5125369 : Nat := 118140960795 + 5125369 * 2 ^ 59
def prefixEnd_5125369 : Nat := 4983230072969 + 3 ^ 40 * 5125369 * 2
def baseEnd_5125369 : Nat := 2631777828654062703916363

theorem tailTrace_5125369 : CollatzResearch.WordTrace tailWord_5125369 prefixEnd_5125369 2631777828654062703916363 := by
  unfold tailWord_5125369
  simp only [CollatzResearch.WordTrace]
  refine ⟨186937564968670931180667161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124625043312447287453778107 186937564968670931180667161)
  ·
    refine ⟨140203173726503198385500371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186937564968670931180667161 140203173726503198385500371)
    ·
      refine ⟨210304760589754797578250557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140203173726503198385500371 210304760589754797578250557)
      ·
        refine ⟨78864285221158049091843959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210304760589754797578250557 78864285221158049091843959)
        ·
          refine ⟨118296427831737073637765939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78864285221158049091843959 118296427831737073637765939)
          ·
            refine ⟨177444641747605610456648909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118296427831737073637765939 177444641747605610456648909)
            ·
              refine ⟨66541740655352103921243341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177444641747605610456648909 66541740655352103921243341)
              ·
                refine ⟨24953152745757038970466253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66541740655352103921243341 24953152745757038970466253)
                ·
                  refine ⟨9357432279658889613924845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24953152745757038970466253 9357432279658889613924845)
                  ·
                    refine ⟨3509037104872083605221817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9357432279658889613924845 3509037104872083605221817)
                    ·
                      refine ⟨2631777828654062703916363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3509037104872083605221817 2631777828654062703916363)
                      ·
                        rfl

theorem cell23_5125369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_5125369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125369 prefixEnd_5125369 := by exact prefixLift 5125369
  have htrace : WordTrace (prefixWord ++ tailWord_5125369) baseStart_5125369 baseEnd_5125369 := by
    simpa [prefixWord, tailWord_5125369, baseEnd_5125369] using wordTrace_append hprefix tailTrace_5125369
  have hstable : (prefixWord ++ tailWord_5125369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125369).length < 2 ^ (prefixWord ++ tailWord_5125369).sum := by decide
  have hdescent : baseEnd_5125369 < baseStart_5125369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125410 : List Nat := [3, 3, 1, 1, 4, 1, 3, 1, 2, 1, 3]
def baseStart_5125410 : Nat := 118140960795 + 5125410 * 2 ^ 59
def prefixEnd_5125410 : Nat := 4983230072969 + 3 ^ 40 * 5125410 * 2
def baseEnd_5125410 : Nat := 2631798881360897043503675

theorem tailTrace_5125410 : CollatzResearch.WordTrace tailWord_5125410 prefixEnd_5125410 2631798881360897043503675 := by
  unfold tailWord_5125410
  simp only [CollatzResearch.WordTrace]
  refine ⟨46734765090380598795727421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124626040241014930121939789 46734765090380598795727421)
  ·
    refine ⟨17525536908892724548397783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46734765090380598795727421 17525536908892724548397783)
    ·
      refine ⟨26288305363339086822596675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17525536908892724548397783 26288305363339086822596675)
      ·
        refine ⟨39432458045008630233895013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26288305363339086822596675 39432458045008630233895013)
        ·
          refine ⟨7393585883439118168855315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39432458045008630233895013 7393585883439118168855315)
          ·
            refine ⟨11090378825158677253282973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7393585883439118168855315 11090378825158677253282973)
            ·
              refine ⟨4158892059434503969981115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11090378825158677253282973 4158892059434503969981115)
              ·
                refine ⟨6238338089151755954971673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4158892059434503969981115 6238338089151755954971673)
                ·
                  refine ⟨4678753566863816966228755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6238338089151755954971673 4678753566863816966228755)
                  ·
                    refine ⟨7018130350295725449343133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4678753566863816966228755 7018130350295725449343133)
                    ·
                      refine ⟨2631798881360897043503675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7018130350295725449343133 2631798881360897043503675)
                      ·
                        rfl

theorem cell23_5125410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_5125410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125410 prefixEnd_5125410 := by exact prefixLift 5125410
  have htrace : WordTrace (prefixWord ++ tailWord_5125410) baseStart_5125410 baseEnd_5125410 := by
    simpa [prefixWord, tailWord_5125410, baseEnd_5125410] using wordTrace_append hprefix tailTrace_5125410
  have hstable : (prefixWord ++ tailWord_5125410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125410).length < 2 ^ (prefixWord ++ tailWord_5125410).sum := by decide
  have hdescent : baseEnd_5125410 < baseStart_5125410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125456 : List Nat := [2, 1, 1, 1, 1, 5, 5, 2, 5]
def baseStart_5125456 : Nat := 118140960795 + 5125456 * 2 ^ 59
def prefixEnd_5125456 : Nat := 4983230072969 + 3 ^ 40 * 5125456 * 2
def baseEnd_5125456 : Nat := 292424722385667095947607

theorem tailTrace_5125456 : CollatzResearch.WordTrace tailWord_5125456 prefixEnd_5125456 292424722385667095947607 := by
  unfold tailWord_5125456
  simp only [CollatzResearch.WordTrace]
  refine ⟨93470369059677872519542111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124627158746237163359389481 93470369059677872519542111)
  ·
    refine ⟨140205553589516808779313167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93470369059677872519542111 140205553589516808779313167)
    ·
      refine ⟨210308330384275213168969751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140205553589516808779313167 210308330384275213168969751)
      ·
        refine ⟨315462495576412819753454627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210308330384275213168969751 315462495576412819753454627)
        ·
          refine ⟨473193743364619229630181941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315462495576412819753454627 473193743364619229630181941)
          ·
            refine ⟨44361913440433052777829557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 473193743364619229630181941 44361913440433052777829557)
            ·
              refine ⟨4158929385040598697921521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44361913440433052777829557 4158929385040598697921521)
              ·
                refine ⟨3119197038780449023441141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4158929385040598697921521 3119197038780449023441141)
                ·
                  refine ⟨292424722385667095947607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3119197038780449023441141 292424722385667095947607)
                  ·
                    rfl

theorem cell23_5125456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 5].length) (baseStart_5125456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125456 prefixEnd_5125456 := by exact prefixLift 5125456
  have htrace : WordTrace (prefixWord ++ tailWord_5125456) baseStart_5125456 baseEnd_5125456 := by
    simpa [prefixWord, tailWord_5125456, baseEnd_5125456] using wordTrace_append hprefix tailTrace_5125456
  have hstable : (prefixWord ++ tailWord_5125456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125456).length < 2 ^ (prefixWord ++ tailWord_5125456).sum := by decide
  have hdescent : baseEnd_5125456 < baseStart_5125456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125459 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 2, 5, 2]
def baseStart_5125459 : Nat := 118140960795 + 5125459 * 2 ^ 59
def prefixEnd_5125459 : Nat := 4983230072969 + 3 ^ 40 * 5125459 * 2
def baseEnd_5125459 : Nat := 2631824041912967351790949

theorem tailTrace_5125459 : CollatzResearch.WordTrace tailWord_5125459 prefixEnd_5125459 2631824041912967351790949 := by
  unfold tailWord_5125459
  simp only [CollatzResearch.WordTrace]
  refine ⟨186940847538344876551443431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124627231692229917700962287 186940847538344876551443431)
  ·
    refine ⟨280411271307517314827165147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186940847538344876551443431 280411271307517314827165147)
    ·
      refine ⟨420616906961275972240747721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280411271307517314827165147 420616906961275972240747721)
      ·
        refine ⟨315462680220956979180560791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420616906961275972240747721 315462680220956979180560791)
        ·
          refine ⟨473194020331435468770841187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315462680220956979180560791 473194020331435468770841187)
          ·
            refine ⟨709791030497153203156261781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473194020331435468770841187 709791030497153203156261781)
            ·
              refine ⟨33271454554554056397949771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 709791030497153203156261781 33271454554554056397949771)
              ·
                refine ⟨49907181831831084596924657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33271454554554056397949771 49907181831831084596924657)
                ·
                  refine ⟨37430386373873313447693493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49907181831831084596924657 37430386373873313447693493)
                  ·
                    refine ⟨3509098722550623135721265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37430386373873313447693493 3509098722550623135721265)
                    ·
                      refine ⟨2631824041912967351790949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3509098722550623135721265 2631824041912967351790949)
                      ·
                        rfl

theorem cell23_5125459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 5, 2].length) (baseStart_5125459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125459 prefixEnd_5125459 := by exact prefixLift 5125459
  have htrace : WordTrace (prefixWord ++ tailWord_5125459) baseStart_5125459 baseEnd_5125459 := by
    simpa [prefixWord, tailWord_5125459, baseEnd_5125459] using wordTrace_append hprefix tailTrace_5125459
  have hstable : (prefixWord ++ tailWord_5125459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125459).length < 2 ^ (prefixWord ++ tailWord_5125459).sum := by decide
  have hdescent : baseEnd_5125459 < baseStart_5125459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125489 : List Nat := [1, 2, 2, 2, 1, 2, 3, 3, 2, 1, 4]
def baseStart_5125489 : Nat := 118140960795 + 5125489 * 2 ^ 59
def prefixEnd_5125489 : Nat := 4983230072969 + 3 ^ 40 * 5125489 * 2
def baseEnd_5125489 : Nat := 2631839446332602234415811

theorem tailTrace_5125489 : CollatzResearch.WordTrace tailWord_5125489 prefixEnd_5125489 2631839446332602234415811 := by
  unfold tailWord_5125489
  simp only [CollatzResearch.WordTrace]
  refine ⟨186941941728236191675035521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124627961152157461116690347 186941941728236191675035521)
  ·
    refine ⟨140206456296177143756276641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186941941728236191675035521 140206456296177143756276641)
    ·
      refine ⟨105154842222132857817207481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140206456296177143756276641 105154842222132857817207481)
      ·
        refine ⟨78866131666599643362905611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105154842222132857817207481 78866131666599643362905611)
        ·
          refine ⟨118299197499899465044358417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78866131666599643362905611 118299197499899465044358417)
          ·
            refine ⟨88724398124924598783268813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118299197499899465044358417 88724398124924598783268813)
            ·
              refine ⟨33271649296846724543725805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88724398124924598783268813 33271649296846724543725805)
              ·
                refine ⟨12476868486317521703897177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33271649296846724543725805 12476868486317521703897177)
                ·
                  refine ⟨9357651364738141277922883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12476868486317521703897177 9357651364738141277922883)
                  ·
                    refine ⟨14036477047107211916884325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9357651364738141277922883 14036477047107211916884325)
                    ·
                      refine ⟨2631839446332602234415811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14036477047107211916884325 2631839446332602234415811)
                      ·
                        rfl

theorem cell23_5125489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_5125489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125489 prefixEnd_5125489 := by exact prefixLift 5125489
  have htrace : WordTrace (prefixWord ++ tailWord_5125489) baseStart_5125489 baseEnd_5125489 := by
    simpa [prefixWord, tailWord_5125489, baseEnd_5125489] using wordTrace_append hprefix tailTrace_5125489
  have hstable : (prefixWord ++ tailWord_5125489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125489).length < 2 ^ (prefixWord ++ tailWord_5125489).sum := by decide
  have hdescent : baseEnd_5125489 < baseStart_5125489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125529 : List Nat := [1, 2, 1, 2, 1, 5, 2, 3, 6]
def baseStart_5125529 : Nat := 118140960795 + 5125529 * 2 ^ 59
def prefixEnd_5125529 : Nat := 4983230072969 + 3 ^ 40 * 5125529 * 2
def baseEnd_5125529 : Nat := 292428887284309119768403

theorem tailTrace_5125529 : CollatzResearch.WordTrace tailWord_5125529 prefixEnd_5125529 292428887284309119768403 := by
  unfold tailWord_5125529
  simp only [CollatzResearch.WordTrace]
  refine ⟨186943400648091278506491641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124628933765394185670994427 186943400648091278506491641)
  ·
    refine ⟨140207550486068458879868731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186943400648091278506491641 140207550486068458879868731)
    ·
      refine ⟨210311325729102688319803097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140207550486068458879868731 210311325729102688319803097)
      ·
        refine ⟨157733494296827016239852323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210311325729102688319803097 157733494296827016239852323)
        ·
          refine ⟨236600241445240524359778485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157733494296827016239852323 236600241445240524359778485)
          ·
            refine ⟨22181272635491299158729233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 236600241445240524359778485 22181272635491299158729233)
            ·
              refine ⟨16635954476618474369046925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22181272635491299158729233 16635954476618474369046925)
              ·
                refine ⟨6238482928731927888392597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16635954476618474369046925 6238482928731927888392597)
                ·
                  refine ⟨292428887284309119768403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6238482928731927888392597 292428887284309119768403)
                  ·
                    rfl

theorem cell23_5125529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 6].length) (baseStart_5125529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125529 prefixEnd_5125529 := by exact prefixLift 5125529
  have htrace : WordTrace (prefixWord ++ tailWord_5125529) baseStart_5125529 baseEnd_5125529 := by
    simpa [prefixWord, tailWord_5125529, baseEnd_5125529] using wordTrace_append hprefix tailTrace_5125529
  have hstable : (prefixWord ++ tailWord_5125529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125529).length < 2 ^ (prefixWord ++ tailWord_5125529).sum := by decide
  have hdescent : baseEnd_5125529 < baseStart_5125529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125579 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 4]
def baseStart_5125579 : Nat := 118140960795 + 5125579 * 2 ^ 59
def prefixEnd_5125579 : Nat := 4983230072969 + 3 ^ 40 * 5125579 * 2
def baseEnd_5125579 : Nat := 2631885659591506882290397

theorem tailTrace_5125579 : CollatzResearch.WordTrace tailWord_5125579 prefixEnd_5125579 2631885659591506882290397 := by
  unfold tailWord_5125579
  simp only [CollatzResearch.WordTrace]
  refine ⟨186945224297910137045811791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124630149531940091363874527 186945224297910137045811791)
  ·
    refine ⟨280417836446865205568717687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186945224297910137045811791 280417836446865205568717687)
    ·
      refine ⟨420626754670297808353076531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280417836446865205568717687 420626754670297808353076531)
      ·
        refine ⟨630940132005446712529614797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420626754670297808353076531 630940132005446712529614797)
        ·
          refine ⟨236602549502042517198605549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 630940132005446712529614797 236602549502042517198605549)
          ·
            refine ⟨88725956063265943949477081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 236602549502042517198605549 88725956063265943949477081)
            ·
              refine ⟨66544467047449457962107811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88725956063265943949477081 66544467047449457962107811)
              ·
                refine ⟨99816700571174186943161717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66544467047449457962107811 99816700571174186943161717)
                ·
                  refine ⟨9357815678547580025921411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99816700571174186943161717 9357815678547580025921411)
                  ·
                    refine ⟨14036723517821370038882117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9357815678547580025921411 14036723517821370038882117)
                    ·
                      refine ⟨2631885659591506882290397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14036723517821370038882117 2631885659591506882290397)
                      ·
                        rfl

theorem cell23_5125579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 4].length) (baseStart_5125579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125579 prefixEnd_5125579 := by exact prefixLift 5125579
  have htrace : WordTrace (prefixWord ++ tailWord_5125579) baseStart_5125579 baseEnd_5125579 := by
    simpa [prefixWord, tailWord_5125579, baseEnd_5125579] using wordTrace_append hprefix tailTrace_5125579
  have hstable : (prefixWord ++ tailWord_5125579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125579).length < 2 ^ (prefixWord ++ tailWord_5125579).sum := by decide
  have hdescent : baseEnd_5125579 < baseStart_5125579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125590 : List Nat := [5, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_5125590 : Nat := 118140960795 + 5125590 * 2 ^ 59
def prefixEnd_5125590 : Nat := 4983230072969 + 3 ^ 40 * 5125590 * 2
def baseEnd_5125590 : Nat := 2631891307878706339252847

theorem tailTrace_5125590 : CollatzResearch.WordTrace tailWord_5125590 prefixEnd_5125590 2631891307878706339252847 := by
  unfold tailWord_5125590
  simp only [CollatzResearch.WordTrace]
  refine ⟨11684101593804392870278889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124630417000580190616308149 11684101593804392870278889)
  ·
    refine ⟨8763076195353294652709167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11684101593804392870278889 8763076195353294652709167)
    ·
      refine ⟨13144614293029941979063751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8763076195353294652709167 13144614293029941979063751)
      ·
        refine ⟨19716921439544912968595627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13144614293029941979063751 19716921439544912968595627)
        ·
          refine ⟨29575382159317369452893441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19716921439544912968595627 29575382159317369452893441)
          ·
            refine ⟨22181536619488027089670081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29575382159317369452893441 22181536619488027089670081)
            ·
              refine ⟨16636152464616020317252561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22181536619488027089670081 16636152464616020317252561)
              ·
                refine ⟨12477114348462015237939421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16636152464616020317252561 12477114348462015237939421)
                ·
                  refine ⟨4678917880673255714227283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12477114348462015237939421 4678917880673255714227283)
                  ·
                    refine ⟨7018376821009883571340925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4678917880673255714227283 7018376821009883571340925)
                    ·
                      refine ⟨2631891307878706339252847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7018376821009883571340925 2631891307878706339252847)
                      ·
                        rfl

theorem cell23_5125590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_5125590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125590 prefixEnd_5125590 := by exact prefixLift 5125590
  have htrace : WordTrace (prefixWord ++ tailWord_5125590) baseStart_5125590 baseEnd_5125590 := by
    simpa [prefixWord, tailWord_5125590, baseEnd_5125590] using wordTrace_append hprefix tailTrace_5125590
  have hstable : (prefixWord ++ tailWord_5125590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125590).length < 2 ^ (prefixWord ++ tailWord_5125590).sum := by decide
  have hdescent : baseEnd_5125590 < baseStart_5125590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125599 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 5]
def baseStart_5125599 : Nat := 118140960795 + 5125599 * 2 ^ 59
def prefixEnd_5125599 : Nat := 4983230072969 + 3 ^ 40 * 5125599 * 2
def baseEnd_5125599 : Nat := 2631895929204596804040305

theorem tailTrace_5125599 : CollatzResearch.WordTrace tailWord_5125599 prefixEnd_5125599 2631895929204596804040305 := by
  unfold tailWord_5125599
  simp only [CollatzResearch.WordTrace]
  refine ⟨186945953757837680461539851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124630635838558453641026567 186945953757837680461539851)
  ·
    refine ⟨280418930636756520692309777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186945953757837680461539851 280418930636756520692309777)
    ·
      refine ⟨210314197977567390519232333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280418930636756520692309777 210314197977567390519232333)
      ·
        refine ⟨78867824241587771444712125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210314197977567390519232333 78867824241587771444712125)
        ·
          refine ⟨29575434090595414291767047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78867824241587771444712125 29575434090595414291767047)
          ·
            refine ⟨44363151135893121437650571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29575434090595414291767047 44363151135893121437650571)
            ·
              refine ⟨66544726703839682156475857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44363151135893121437650571 66544726703839682156475857)
              ·
                refine ⟨49908545027879761617356893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66544726703839682156475857 49908545027879761617356893)
                ·
                  refine ⟨18715704385454910606508835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49908545027879761617356893 18715704385454910606508835)
                  ·
                    refine ⟨28073556578182365909763253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18715704385454910606508835 28073556578182365909763253)
                    ·
                      refine ⟨2631895929204596804040305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28073556578182365909763253 2631895929204596804040305)
                      ·
                        rfl

theorem cell23_5125599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_5125599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125599 prefixEnd_5125599 := by exact prefixLift 5125599
  have htrace : WordTrace (prefixWord ++ tailWord_5125599) baseStart_5125599 baseEnd_5125599 := by
    simpa [prefixWord, tailWord_5125599, baseEnd_5125599] using wordTrace_append hprefix tailTrace_5125599
  have hstable : (prefixWord ++ tailWord_5125599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125599).length < 2 ^ (prefixWord ++ tailWord_5125599).sum := by decide
  have hdescent : baseEnd_5125599 < baseStart_5125599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125607 : List Nat := [1, 1, 5, 2, 1, 4, 1, 3, 1, 1, 3]
def baseStart_5125607 : Nat := 118140960795 + 5125607 * 2 ^ 59
def prefixEnd_5125607 : Nat := 4983230072969 + 3 ^ 40 * 5125607 * 2
def baseEnd_5125607 : Nat := 2631900037049832772740269

theorem tailTrace_5125607 : CollatzResearch.WordTrace tailWord_5125607 prefixEnd_5125607 2631900037049832772740269 := by
  unfold tailWord_5125607
  simp only [CollatzResearch.WordTrace]
  refine ⟨186946245541808697827831075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124630830361205798551887383 186946245541808697827831075)
  ·
    refine ⟨280419368312713046741746613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186946245541808697827831075 280419368312713046741746613)
    ·
      refine ⟨26289315779316848132038745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 280419368312713046741746613 26289315779316848132038745)
      ·
        refine ⟨19716986834487636099029059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26289315779316848132038745 19716986834487636099029059)
        ·
          refine ⟨29575480251731454148543589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19716986834487636099029059 29575480251731454148543589)
          ·
            refine ⟨5545402547199647652851923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29575480251731454148543589 5545402547199647652851923)
            ·
              refine ⟨8318103820799471479277885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5545402547199647652851923 8318103820799471479277885)
              ·
                refine ⟨3119288932799801804729207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8318103820799471479277885 3119288932799801804729207)
                ·
                  refine ⟨4678933399199702707093811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3119288932799801804729207 4678933399199702707093811)
                  ·
                    refine ⟨7018400098799554060640717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4678933399199702707093811 7018400098799554060640717)
                    ·
                      refine ⟨2631900037049832772740269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7018400098799554060640717 2631900037049832772740269)
                      ·
                        rfl

theorem cell23_5125607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_5125607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125607 prefixEnd_5125607 := by exact prefixLift 5125607
  have htrace : WordTrace (prefixWord ++ tailWord_5125607) baseStart_5125607 baseEnd_5125607 := by
    simpa [prefixWord, tailWord_5125607, baseEnd_5125607] using wordTrace_append hprefix tailTrace_5125607
  have hstable : (prefixWord ++ tailWord_5125607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125607).length < 2 ^ (prefixWord ++ tailWord_5125607).sum := by decide
  have hdescent : baseEnd_5125607 < baseStart_5125607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125616 : List Nat := [2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 5]
def baseStart_5125616 : Nat := 118140960795 + 5125616 * 2 ^ 59
def prefixEnd_5125616 : Nat := 4983230072969 + 3 ^ 40 * 5125616 * 2
def baseEnd_5125616 : Nat := 2631904658375723237527727

theorem tailTrace_5125616 : CollatzResearch.WordTrace tailWord_5125616 prefixEnd_5125616 2631904658375723237527727 := by
  unfold tailWord_5125616
  simp only [CollatzResearch.WordTrace]
  refine ⟨93473286899388046182454351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124631049199184061576605801 93473286899388046182454351)
  ·
    refine ⟨140209930349082069273681527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93473286899388046182454351 140209930349082069273681527)
    ·
      refine ⟨210314895523623103910522291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140209930349082069273681527 210314895523623103910522291)
      ·
        refine ⟨315472343285434655865783437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210314895523623103910522291 315472343285434655865783437)
        ·
          refine ⟨118302128732037995949668789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 315472343285434655865783437 118302128732037995949668789)
          ·
            refine ⟨11090824568628562120281449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118302128732037995949668789 11090824568628562120281449)
            ·
              refine ⟨8318118426471421590211087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11090824568628562120281449 8318118426471421590211087)
              ·
                refine ⟨12477177639707132385316631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8318118426471421590211087 12477177639707132385316631)
                ·
                  refine ⟨18715766459560698577974947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12477177639707132385316631 18715766459560698577974947)
                  ·
                    refine ⟨28073649689341047866962421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18715766459560698577974947 28073649689341047866962421)
                    ·
                      refine ⟨2631904658375723237527727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28073649689341047866962421 2631904658375723237527727)
                      ·
                        rfl

theorem cell23_5125616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 5].length) (baseStart_5125616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125616 prefixEnd_5125616 := by exact prefixLift 5125616
  have htrace : WordTrace (prefixWord ++ tailWord_5125616) baseStart_5125616 baseEnd_5125616 := by
    simpa [prefixWord, tailWord_5125616, baseEnd_5125616] using wordTrace_append hprefix tailTrace_5125616
  have hstable : (prefixWord ++ tailWord_5125616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125616).length < 2 ^ (prefixWord ++ tailWord_5125616).sum := by decide
  have hdescent : baseEnd_5125616 < baseStart_5125616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125706 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 2, 4, 3]
def baseStart_5125706 : Nat := 118140960795 + 5125706 * 2 ^ 59
def prefixEnd_5125706 : Nat := 4983230072969 + 3 ^ 40 * 5125706 * 2
def baseEnd_5125706 : Nat := 2631950871634627885402313

theorem tailTrace_5125706 : CollatzResearch.WordTrace tailWord_5125706 prefixEnd_5125706 2631950871634627885402313 := by
  unfold tailWord_5125706
  simp only [CollatzResearch.WordTrace]
  refine ⟨46737464092112509433921243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124633237578966691823789981 46737464092112509433921243)
  ·
    refine ⟨70106196138168764150881865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46737464092112509433921243 70106196138168764150881865)
    ·
      refine ⟨52579647103626573113161399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70106196138168764150881865 52579647103626573113161399)
      ·
        refine ⟨78869470655439859669742099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52579647103626573113161399 78869470655439859669742099)
        ·
          refine ⟨118304205983159789504613149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78869470655439859669742099 118304205983159789504613149)
          ·
            refine ⟨44364077243684921064229931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118304205983159789504613149 44364077243684921064229931)
            ·
              refine ⟨66546115865527381596344897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44364077243684921064229931 66546115865527381596344897)
              ·
                refine ⟨49909586899145536197258673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66546115865527381596344897 49909586899145536197258673)
                ·
                  refine ⟨37432190174359152147944005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49909586899145536197258673 37432190174359152147944005)
                  ·
                    refine ⟨7018535657692341027739501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37432190174359152147944005 7018535657692341027739501)
                    ·
                      refine ⟨2631950871634627885402313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7018535657692341027739501 2631950871634627885402313)
                      ·
                        rfl

theorem cell23_5125706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_5125706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125706 prefixEnd_5125706 := by exact prefixLift 5125706
  have htrace : WordTrace (prefixWord ++ tailWord_5125706) baseStart_5125706 baseEnd_5125706 := by
    simpa [prefixWord, tailWord_5125706, baseEnd_5125706] using wordTrace_append hprefix tailTrace_5125706
  have hstable : (prefixWord ++ tailWord_5125706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125706).length < 2 ^ (prefixWord ++ tailWord_5125706).sum := by decide
  have hdescent : baseEnd_5125706 < baseStart_5125706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125716 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_5125716 : Nat := 118140960795 + 5125716 * 2 ^ 59
def prefixEnd_5125716 : Nat := 4983230072969 + 3 ^ 40 * 5125716 * 2
def baseEnd_5125716 : Nat := 2631956006441172846277267

theorem tailTrace_5125716 : CollatzResearch.WordTrace tailWord_5125716 prefixEnd_5125716 2631956006441172846277267 := by
  unfold tailWord_5125716
  simp only [CollatzResearch.WordTrace]
  refine ⟨93475110549206904721774501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124633480732275872962366001 93475110549206904721774501)
  ·
    refine ⟨17526583227976294635332719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93475110549206904721774501 17526583227976294635332719)
    ·
      refine ⟨26289874841964441952999079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17526583227976294635332719 26289874841964441952999079)
      ·
        refine ⟨39434812262946662929498619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26289874841964441952999079 39434812262946662929498619)
        ·
          refine ⟨59152218394419994394247929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39434812262946662929498619 59152218394419994394247929)
          ·
            refine ⟨44364163795814995795685947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59152218394419994394247929 44364163795814995795685947)
            ·
              refine ⟨66546245693722493693528921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44364163795814995795685947 66546245693722493693528921)
              ·
                refine ⟨49909684270291870270146691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66546245693722493693528921 49909684270291870270146691)
                ·
                  refine ⟨74864526405437805405220037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49909684270291870270146691 74864526405437805405220037)
                  ·
                    refine ⟨14037098701019588513478757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74864526405437805405220037 14037098701019588513478757)
                    ·
                      refine ⟨2631956006441172846277267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14037098701019588513478757 2631956006441172846277267)
                      ·
                        rfl

theorem cell23_5125716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_5125716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125716 prefixEnd_5125716 := by exact prefixLift 5125716
  have htrace : WordTrace (prefixWord ++ tailWord_5125716) baseStart_5125716 baseEnd_5125716 := by
    simpa [prefixWord, tailWord_5125716, baseEnd_5125716] using wordTrace_append hprefix tailTrace_5125716
  have hstable : (prefixWord ++ tailWord_5125716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125716).length < 2 ^ (prefixWord ++ tailWord_5125716).sum := by decide
  have hdescent : baseEnd_5125716 < baseStart_5125716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125718 : List Nat := [5, 2, 2, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_5125718 : Nat := 118140960795 + 5125718 * 2 ^ 59
def prefixEnd_5125718 : Nat := 4983230072969 + 3 ^ 40 * 5125718 * 2
def baseEnd_5125718 : Nat := 2631957033402481838452259

theorem tailTrace_5125718 : CollatzResearch.WordTrace tailWord_5125718 prefixEnd_5125718 2631957033402481838452259 := by
  unfold tailWord_5125718
  simp only [CollatzResearch.WordTrace]
  refine ⟨11684393377775410236570113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124633529362937709190081205 11684393377775410236570113)
  ·
    refine ⟨8763295033331557677427585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11684393377775410236570113 8763295033331557677427585)
    ·
      refine ⟨6572471274998668258070689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8763295033331557677427585 6572471274998668258070689)
      ·
        refine ⟨4929353456249001193553017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6572471274998668258070689 4929353456249001193553017)
        ·
          refine ⟨3697015092186750895164763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4929353456249001193553017 3697015092186750895164763)
          ·
            refine ⟨5545522638280126342747145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3697015092186750895164763 5545522638280126342747145)
            ·
              refine ⟨4159141978710094757060359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5545522638280126342747145 4159141978710094757060359)
              ·
                refine ⟨6238712968065142135590539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4159141978710094757060359 6238712968065142135590539)
                ·
                  refine ⟨9358069452097713203385809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6238712968065142135590539 9358069452097713203385809)
                  ·
                    refine ⟨7018552089073284902539357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9358069452097713203385809 7018552089073284902539357)
                    ·
                      refine ⟨2631957033402481838452259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7018552089073284902539357 2631957033402481838452259)
                      ·
                        rfl

theorem cell23_5125718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_5125718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125718 prefixEnd_5125718 := by exact prefixLift 5125718
  have htrace : WordTrace (prefixWord ++ tailWord_5125718) baseStart_5125718 baseEnd_5125718 := by
    simpa [prefixWord, tailWord_5125718, baseEnd_5125718] using wordTrace_append hprefix tailTrace_5125718
  have hstable : (prefixWord ++ tailWord_5125718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125718).length < 2 ^ (prefixWord ++ tailWord_5125718).sum := by decide
  have hdescent : baseEnd_5125718 < baseStart_5125718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125724 : List Nat := [2, 2, 4, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_5125724 : Nat := 118140960795 + 5125724 * 2 ^ 59
def prefixEnd_5125724 : Nat := 4983230072969 + 3 ^ 40 * 5125724 * 2
def baseEnd_5125724 : Nat := 2631960114286408814977231

theorem tailTrace_5125724 : CollatzResearch.WordTrace tailWord_5125724 prefixEnd_5125724 2631960114286408814977231 := by
  unfold tailWord_5125724
  simp only [CollatzResearch.WordTrace]
  refine ⟨93475256441192413404920113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124633675254923217873226817 93475256441192413404920113)
  ·
    refine ⟨70106442330894310053690085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93475256441192413404920113 70106442330894310053690085)
    ·
      refine ⟨13144957937042683135066891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70106442330894310053690085 13144957937042683135066891)
      ·
        refine ⟨19717436905564024702600337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13144957937042683135066891 19717436905564024702600337)
        ·
          refine ⟨14788077679173018526950253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19717436905564024702600337 14788077679173018526950253)
          ·
            refine ⟨5545529129689881947606345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14788077679173018526950253 5545529129689881947606345)
            ·
              refine ⟨4159146847267411460704759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5545529129689881947606345 4159146847267411460704759)
              ·
                refine ⟨6238720270901117191057139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4159146847267411460704759 6238720270901117191057139)
                ·
                  refine ⟨9358080406351675786585709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6238720270901117191057139 9358080406351675786585709)
                  ·
                    refine ⟨3509280152381878419969641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9358080406351675786585709 3509280152381878419969641)
                    ·
                      refine ⟨2631960114286408814977231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3509280152381878419969641 2631960114286408814977231)
                      ·
                        rfl

theorem cell23_5125724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_5125724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125724 prefixEnd_5125724 := by exact prefixLift 5125724
  have htrace : WordTrace (prefixWord ++ tailWord_5125724) baseStart_5125724 baseEnd_5125724 := by
    simpa [prefixWord, tailWord_5125724, baseEnd_5125724] using wordTrace_append hprefix tailTrace_5125724
  have hstable : (prefixWord ++ tailWord_5125724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125724).length < 2 ^ (prefixWord ++ tailWord_5125724).sum := by decide
  have hdescent : baseEnd_5125724 < baseStart_5125724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125776 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 4]
def baseStart_5125776 : Nat := 118140960795 + 5125776 * 2 ^ 59
def prefixEnd_5125776 : Nat := 4983230072969 + 3 ^ 40 * 5125776 * 2
def baseEnd_5125776 : Nat := 2631986815280442611526991

theorem tailTrace_5125776 : CollatzResearch.WordTrace tailWord_5125776 prefixEnd_5125776 2631986815280442611526991 := by
  unfold tailWord_5125776
  simp only [CollatzResearch.WordTrace]
  refine ⟨93476204739098219845366591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124634939652130959793822121 93476204739098219845366591)
  ·
    refine ⟨140214307108647329768049887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93476204739098219845366591 140214307108647329768049887)
    ·
      refine ⟨210321460662970994652074831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140214307108647329768049887 210321460662970994652074831)
      ·
        refine ⟨315482190994456491978112247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210321460662970994652074831 315482190994456491978112247)
        ·
          refine ⟨473223286491684737967168371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315482190994456491978112247 473223286491684737967168371)
          ·
            refine ⟨709834929737527106950752557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473223286491684737967168371 709834929737527106950752557)
            ·
              refine ⟨266188098651572665106532209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 709834929737527106950752557 266188098651572665106532209)
              ·
                refine ⟨199641073988679498829899157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266188098651572665106532209 199641073988679498829899157)
                ·
                  refine ⟨9358175343219351507651523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 199641073988679498829899157 9358175343219351507651523)
                  ·
                    refine ⟨14037263014829027261477285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9358175343219351507651523 14037263014829027261477285)
                    ·
                      refine ⟨2631986815280442611526991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14037263014829027261477285 2631986815280442611526991)
                      ·
                        rfl

theorem cell23_5125776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 4].length) (baseStart_5125776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125776 prefixEnd_5125776 := by exact prefixLift 5125776
  have htrace : WordTrace (prefixWord ++ tailWord_5125776) baseStart_5125776 baseEnd_5125776 := by
    simpa [prefixWord, tailWord_5125776, baseEnd_5125776] using wordTrace_append hprefix tailTrace_5125776
  have hstable : (prefixWord ++ tailWord_5125776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125776).length < 2 ^ (prefixWord ++ tailWord_5125776).sum := by decide
  have hdescent : baseEnd_5125776 < baseStart_5125776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125790 : List Nat := [4, 3, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_5125790 : Nat := 118140960795 + 5125790 * 2 ^ 59
def prefixEnd_5125790 : Nat := 4983230072969 + 3 ^ 40 * 5125790 * 2
def baseEnd_5125790 : Nat := 877331334669868518917309

theorem tailTrace_5125790 : CollatzResearch.WordTrace tailWord_5125790 prefixEnd_5125790 877331334669868518917309 := by
  unfold tailWord_5125790
  simp only [CollatzResearch.WordTrace]
  refine ⟨23369115012518215010217853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124635280066763813387828549 23369115012518215010217853)
  ·
    refine ⟨8763418129694330628831695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23369115012518215010217853 8763418129694330628831695)
    ·
      refine ⟨13145127194541495943247543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8763418129694330628831695 13145127194541495943247543)
      ·
        refine ⟨19717690791812243914871315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13145127194541495943247543 19717690791812243914871315)
        ·
          refine ⟨29576536187718365872306973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19717690791812243914871315 29576536187718365872306973)
          ·
            refine ⟨11091201070394387202115115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29576536187718365872306973 11091201070394387202115115)
            ·
              refine ⟨16636801605591580803172673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11091201070394387202115115 16636801605591580803172673)
              ·
                refine ⟨12477601204193685602379505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16636801605591580803172673 12477601204193685602379505)
                ·
                  refine ⟨9358200903145264201784629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12477601204193685602379505 9358200903145264201784629)
                  ·
                    refine ⟨877331334669868518917309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9358200903145264201784629 877331334669868518917309)
                    ·
                      rfl

theorem cell23_5125790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_5125790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125790 prefixEnd_5125790 := by exact prefixLift 5125790
  have htrace : WordTrace (prefixWord ++ tailWord_5125790) baseStart_5125790 baseEnd_5125790 := by
    simpa [prefixWord, tailWord_5125790, baseEnd_5125790] using wordTrace_append hprefix tailTrace_5125790
  have hstable : (prefixWord ++ tailWord_5125790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125790).length < 2 ^ (prefixWord ++ tailWord_5125790).sum := by decide
  have hdescent : baseEnd_5125790 < baseStart_5125790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125793 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 4, 1, 4]
def baseStart_5125793 : Nat := 118140960795 + 5125793 * 2 ^ 59
def prefixEnd_5125793 : Nat := 4983230072969 + 3 ^ 40 * 5125793 * 2
def baseEnd_5125793 : Nat := 2631995544451569045014413

theorem tailTrace_5125793 : CollatzResearch.WordTrace tailWord_5125793 prefixEnd_5125793 2631995544451569045014413 := by
  unfold tailWord_5125793
  simp only [CollatzResearch.WordTrace]
  refine ⟨186953029519134851594102033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124635353012756567729401355 186953029519134851594102033)
  ·
    refine ⟨140214772139351138695576525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186953029519134851594102033 140214772139351138695576525)
    ·
      refine ⟨52580539552256677010841197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140214772139351138695576525 52580539552256677010841197)
      ·
        refine ⟨19717702332096253879065449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52580539552256677010841197 19717702332096253879065449)
        ·
          refine ⟨14788276749072190409299087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19717702332096253879065449 14788276749072190409299087)
          ·
            refine ⟨22182415123608285613948631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14788276749072190409299087 22182415123608285613948631)
            ·
              refine ⟨33273622685412428420922947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22182415123608285613948631 33273622685412428420922947)
              ·
                refine ⟨49910434028118642631384421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33273622685412428420922947 49910434028118642631384421)
                ·
                  refine ⟨9358206380272245493384579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49910434028118642631384421 9358206380272245493384579)
                  ·
                    refine ⟨14037309570408368240076869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9358206380272245493384579 14037309570408368240076869)
                    ·
                      refine ⟨2631995544451569045014413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14037309570408368240076869 2631995544451569045014413)
                      ·
                        rfl

theorem cell23_5125793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_5125793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125793 prefixEnd_5125793 := by exact prefixLift 5125793
  have htrace : WordTrace (prefixWord ++ tailWord_5125793) baseStart_5125793 baseEnd_5125793 := by
    simpa [prefixWord, tailWord_5125793, baseEnd_5125793] using wordTrace_append hprefix tailTrace_5125793
  have hstable : (prefixWord ++ tailWord_5125793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125793).length < 2 ^ (prefixWord ++ tailWord_5125793).sum := by decide
  have hdescent : baseEnd_5125793 < baseStart_5125793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125794 : List Nat := [3, 3, 1, 4, 1, 1, 3, 2, 5]
def baseStart_5125794 : Nat := 118140960795 + 5125794 * 2 ^ 59
def prefixEnd_5125794 : Nat := 4983230072969 + 3 ^ 40 * 5125794 * 2
def baseEnd_5125794 : Nat := 292444006436913726789101

theorem tailTrace_5125794 : CollatzResearch.WordTrace tailWord_5125794 prefixEnd_5125794 292444006436913726789101 := by
  unfold tailWord_5125794
  simp only [CollatzResearch.WordTrace]
  refine ⟨46738266498032807191222109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124635377328087485843258957 46738266498032807191222109)
  ·
    refine ⟨17526849936762302696708291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46738266498032807191222109 17526849936762302696708291)
    ·
      refine ⟨26290274905143454045062437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17526849936762302696708291 26290274905143454045062437)
      ·
        refine ⟨4929426544714397633449207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26290274905143454045062437 4929426544714397633449207)
        ·
          refine ⟨7394139817071596450173811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4929426544714397633449207 7394139817071596450173811)
          ·
            refine ⟨11091209725607394675260717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7394139817071596450173811 11091209725607394675260717)
            ·
              refine ⟨4159203647102773003222769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11091209725607394675260717 4159203647102773003222769)
              ·
                refine ⟨3119402735327079752417077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4159203647102773003222769 3119402735327079752417077)
                ·
                  refine ⟨292444006436913726789101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3119402735327079752417077 292444006436913726789101)
                  ·
                    rfl

theorem cell23_5125794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_5125794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125794 prefixEnd_5125794 := by exact prefixLift 5125794
  have htrace : WordTrace (prefixWord ++ tailWord_5125794) baseStart_5125794 baseEnd_5125794 := by
    simpa [prefixWord, tailWord_5125794, baseEnd_5125794] using wordTrace_append hprefix tailTrace_5125794
  have hstable : (prefixWord ++ tailWord_5125794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125794).length < 2 ^ (prefixWord ++ tailWord_5125794).sum := by decide
  have hdescent : baseEnd_5125794 < baseStart_5125794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125860 : List Nat := [2, 3, 1, 1, 1, 3, 2, 3, 3, 1, 3]
def baseStart_5125860 : Nat := 118140960795 + 5125860 * 2 ^ 59
def prefixEnd_5125860 : Nat := 4983230072969 + 3 ^ 40 * 5125860 * 2
def baseEnd_5125860 : Nat := 2632029947655420282876605

theorem tailTrace_5125860 : CollatzResearch.WordTrace tailWord_5125860 prefixEnd_5125860 2632029947655420282876605 := by
  unfold tailWord_5125860
  simp only [CollatzResearch.WordTrace]
  refine ⟨93477736604946061018395517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124636982139928081357860689 93477736604946061018395517)
  ·
    refine ⟨35054151226854772881898319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93477736604946061018395517 35054151226854772881898319)
    ·
      refine ⟨52581226840282159322847479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35054151226854772881898319 52581226840282159322847479)
      ·
        refine ⟨78871840260423238984271219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52581226840282159322847479 78871840260423238984271219)
        ·
          refine ⟨118307760390634858476406829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78871840260423238984271219 118307760390634858476406829)
          ·
            refine ⟨44365410146488071928652561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118307760390634858476406829 44365410146488071928652561)
            ·
              refine ⟨33274057609866053946489421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44365410146488071928652561 33274057609866053946489421)
              ·
                refine ⟨12477771603699770229933533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33274057609866053946489421 12477771603699770229933533)
                ·
                  refine ⟨4679164351387413836225075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12477771603699770229933533 4679164351387413836225075)
                  ·
                    refine ⟨7018746527081120754337613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4679164351387413836225075 7018746527081120754337613)
                    ·
                      refine ⟨2632029947655420282876605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7018746527081120754337613 2632029947655420282876605)
                      ·
                        rfl

theorem cell23_5125860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_5125860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125860 prefixEnd_5125860 := by exact prefixLift 5125860
  have htrace : WordTrace (prefixWord ++ tailWord_5125860) baseStart_5125860 baseEnd_5125860 := by
    simpa [prefixWord, tailWord_5125860, baseEnd_5125860] using wordTrace_append hprefix tailTrace_5125860
  have hstable : (prefixWord ++ tailWord_5125860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125860).length < 2 ^ (prefixWord ++ tailWord_5125860).sum := by decide
  have hdescent : baseEnd_5125860 < baseStart_5125860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125870 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 1, 5, 2]
def baseStart_5125870 : Nat := 118140960795 + 5125870 * 2 ^ 59
def prefixEnd_5125870 : Nat := 4983230072969 + 3 ^ 40 * 5125870 * 2
def baseEnd_5125870 : Nat := 2632035082461965243751559

theorem tailTrace_5125870 : CollatzResearch.WordTrace tailWord_5125870 prefixEnd_5125870 2632035082461965243751559 := by
  unfold tailWord_5125870
  simp only [CollatzResearch.WordTrace]
  refine ⟨23369479742481986718081883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124637225293237262496436709 23369479742481986718081883)
  ·
    refine ⟨35054219613722980077122825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23369479742481986718081883 35054219613722980077122825)
    ·
      refine ⟨26290664710292235057842119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35054219613722980077122825 26290664710292235057842119)
      ·
        refine ⟨39435997065438352586763179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26290664710292235057842119 39435997065438352586763179)
        ·
          refine ⟨59153995598157528880144769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39435997065438352586763179 59153995598157528880144769)
          ·
            refine ⟨44365496698618146660108577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59153995598157528880144769 44365496698618146660108577)
            ·
              refine ⟨33274122523963609995081433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44365496698618146660108577 33274122523963609995081433)
              ·
                refine ⟨24955591892972707496311075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33274122523963609995081433 24955591892972707496311075)
                ·
                  refine ⟨37433387839459061244466613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24955591892972707496311075 37433387839459061244466613)
                  ·
                    refine ⟨3509380109949286991668745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37433387839459061244466613 3509380109949286991668745)
                    ·
                      refine ⟨2632035082461965243751559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3509380109949286991668745 2632035082461965243751559)
                      ·
                        rfl

theorem cell23_5125870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_5125870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125870 prefixEnd_5125870 := by exact prefixLift 5125870
  have htrace : WordTrace (prefixWord ++ tailWord_5125870) baseStart_5125870 baseEnd_5125870 := by
    simpa [prefixWord, tailWord_5125870, baseEnd_5125870] using wordTrace_append hprefix tailTrace_5125870
  have hstable : (prefixWord ++ tailWord_5125870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125870).length < 2 ^ (prefixWord ++ tailWord_5125870).sum := by decide
  have hdescent : baseEnd_5125870 < baseStart_5125870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125883 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 1, 8, 2]
def baseStart_5125883 : Nat := 118140960795 + 5125883 * 2 ^ 59
def prefixEnd_5125883 : Nat := 4983230072969 + 3 ^ 40 * 5125883 * 2
def baseEnd_5125883 : Nat := 2632041757710473692888999

theorem tailTrace_5125883 : CollatzResearch.WordTrace tailWord_5125883 prefixEnd_5125883 2632041757710473692888999 := by
  unfold tailWord_5125883
  simp only [CollatzResearch.WordTrace]
  refine ⟨186956312088808796964878303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124637541392539197976585535 186956312088808796964878303)
  ·
    refine ⟨280434468133213195447317455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186956312088808796964878303 280434468133213195447317455)
    ·
      refine ⟨420651702199819793170976183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280434468133213195447317455 420651702199819793170976183)
      ·
        refine ⟨630977553299729689756464275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420651702199819793170976183 630977553299729689756464275)
        ·
          refine ⟨946466329949594534634696413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630977553299729689756464275 946466329949594534634696413)
          ·
            refine ⟨354924873731097950488011155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 946466329949594534634696413 354924873731097950488011155)
            ·
              refine ⟨532387310596646925732016733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354924873731097950488011155 532387310596646925732016733)
              ·
                refine ⟨199645241473742597149506275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 532387310596646925732016733 199645241473742597149506275)
                ·
                  refine ⟨299467862210613895724259413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 199645241473742597149506275 299467862210613895724259413)
                  ·
                    refine ⟨3509389010280631590518665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 299467862210613895724259413 3509389010280631590518665)
                    ·
                      refine ⟨2632041757710473692888999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3509389010280631590518665 2632041757710473692888999)
                      ·
                        rfl

theorem cell23_5125883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 8, 2].length) (baseStart_5125883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125883 prefixEnd_5125883 := by exact prefixLift 5125883
  have htrace : WordTrace (prefixWord ++ tailWord_5125883) baseStart_5125883 baseEnd_5125883 := by
    simpa [prefixWord, tailWord_5125883, baseEnd_5125883] using wordTrace_append hprefix tailTrace_5125883
  have hstable : (prefixWord ++ tailWord_5125883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125883).length < 2 ^ (prefixWord ++ tailWord_5125883).sum := by decide
  have hdescent : baseEnd_5125883 < baseStart_5125883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125903 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 3]
def baseStart_5125903 : Nat := 118140960795 + 5125903 * 2 ^ 59
def prefixEnd_5125903 : Nat := 4983230072969 + 3 ^ 40 * 5125903 * 2
def baseEnd_5125903 : Nat := 2632052027323563614638907

theorem tailTrace_5125903 : CollatzResearch.WordTrace tailWord_5125903 prefixEnd_5125903 2632052027323563614638907 := by
  unfold tailWord_5125903
  simp only [CollatzResearch.WordTrace]
  refine ⟨186957041548736340380606363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124638027699157560253737575 186957041548736340380606363)
  ·
    refine ⟨280435562323104510570909545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186957041548736340380606363 280435562323104510570909545)
    ·
      refine ⟨210326671742328382928182159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280435562323104510570909545 210326671742328382928182159)
      ·
        refine ⟨315490007613492574392273239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210326671742328382928182159 315490007613492574392273239)
        ·
          refine ⟨473235011420238861588409859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315490007613492574392273239 473235011420238861588409859)
          ·
            refine ⟨709852517130358292382614789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473235011420238861588409859 709852517130358292382614789)
            ·
              refine ⟨133097346961942179821740273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 709852517130358292382614789 133097346961942179821740273)
              ·
                refine ⟨99823010221456634866305205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133097346961942179821740273 99823010221456634866305205)
                ·
                  refine ⟨9358407208261559518716113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99823010221456634866305205 9358407208261559518716113)
                  ·
                    refine ⟨7018805406196169639037085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9358407208261559518716113 7018805406196169639037085)
                    ·
                      refine ⟨2632052027323563614638907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7018805406196169639037085 2632052027323563614638907)
                      ·
                        rfl

theorem cell23_5125903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 3].length) (baseStart_5125903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125903 prefixEnd_5125903 := by exact prefixLift 5125903
  have htrace : WordTrace (prefixWord ++ tailWord_5125903) baseStart_5125903 baseEnd_5125903 := by
    simpa [prefixWord, tailWord_5125903, baseEnd_5125903] using wordTrace_append hprefix tailTrace_5125903
  have hstable : (prefixWord ++ tailWord_5125903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125903).length < 2 ^ (prefixWord ++ tailWord_5125903).sum := by decide
  have hdescent : baseEnd_5125903 < baseStart_5125903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125934 : List Nat := [4, 1, 3, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_5125934 : Nat := 118140960795 + 5125934 * 2 ^ 59
def prefixEnd_5125934 : Nat := 4983230072969 + 3 ^ 40 * 5125934 * 2
def baseEnd_5125934 : Nat := 2632067945223852993351265

theorem tailTrace_5125934 : CollatzResearch.WordTrace tailWord_5125934 prefixEnd_5125934 2632067945223852993351265 := by
  unfold tailWord_5125934
  simp only [CollatzResearch.WordTrace]
  refine ⟨23369771526453004084373107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124638781474416021783323237 23369771526453004084373107)
  ·
    refine ⟨35054657289679506126559661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23369771526453004084373107 35054657289679506126559661)
    ·
      refine ⟨13145496483629814797459873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35054657289679506126559661 13145496483629814797459873)
      ·
        refine ⟨9859122362722361098094905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13145496483629814797459873 9859122362722361098094905)
        ·
          refine ⟨7394341772041770823571179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9859122362722361098094905 7394341772041770823571179)
          ·
            refine ⟨11091512658062656235356769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7394341772041770823571179 11091512658062656235356769)
            ·
              refine ⟨8318634493546992176517577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11091512658062656235356769 8318634493546992176517577)
              ·
                refine ⟨6238975870160244132388183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8318634493546992176517577 6238975870160244132388183)
                ·
                  refine ⟨9358463805240366198582275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6238975870160244132388183 9358463805240366198582275)
                  ·
                    refine ⟨14037695707860549297873413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9358463805240366198582275 14037695707860549297873413)
                    ·
                      refine ⟨2632067945223852993351265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14037695707860549297873413 2632067945223852993351265)
                      ·
                        rfl

theorem cell23_5125934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_5125934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125934 prefixEnd_5125934 := by exact prefixLift 5125934
  have htrace : WordTrace (prefixWord ++ tailWord_5125934) baseStart_5125934 baseEnd_5125934 := by
    simpa [prefixWord, tailWord_5125934, baseEnd_5125934] using wordTrace_append hprefix tailTrace_5125934
  have hstable : (prefixWord ++ tailWord_5125934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125934).length < 2 ^ (prefixWord ++ tailWord_5125934).sum := by decide
  have hdescent : baseEnd_5125934 < baseStart_5125934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125937 : List Nat := [1, 2, 2, 3, 2, 3, 2, 2, 1, 2, 3]
def baseStart_5125937 : Nat := 118140960795 + 5125937 * 2 ^ 59
def prefixEnd_5125937 : Nat := 4983230072969 + 3 ^ 40 * 5125937 * 2
def baseEnd_5125937 : Nat := 2632069485665816481613751

theorem tailTrace_5125937 : CollatzResearch.WordTrace tailWord_5125937 prefixEnd_5125937 2632069485665816481613751 := by
  unfold tailWord_5125937
  simp only [CollatzResearch.WordTrace]
  refine ⟨186958281630613164187344065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124638854420408776124896043 186958281630613164187344065)
  ·
    refine ⟨140218711222959873140508049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186958281630613164187344065 140218711222959873140508049)
    ·
      refine ⟨105164033417219904855381037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140218711222959873140508049 105164033417219904855381037)
      ·
        refine ⟨39436512531457464320767889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105164033417219904855381037 39436512531457464320767889)
        ·
          refine ⟨29577384398593098240575917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39436512531457464320767889 29577384398593098240575917)
          ·
            refine ⟨11091519149472411840215969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29577384398593098240575917 11091519149472411840215969)
            ·
              refine ⟨8318639362104308880161977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11091519149472411840215969 8318639362104308880161977)
              ·
                refine ⟨6238979521578231660121483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8318639362104308880161977 6238979521578231660121483)
                ·
                  refine ⟨9358469282367347490182225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6238979521578231660121483 9358469282367347490182225)
                  ·
                    refine ⟨7018851961775510617636669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9358469282367347490182225 7018851961775510617636669)
                    ·
                      refine ⟨2632069485665816481613751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7018851961775510617636669 2632069485665816481613751)
                      ·
                        rfl

theorem cell23_5125937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_5125937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125937 prefixEnd_5125937 := by exact prefixLift 5125937
  have htrace : WordTrace (prefixWord ++ tailWord_5125937) baseStart_5125937 baseEnd_5125937 := by
    simpa [prefixWord, tailWord_5125937, baseEnd_5125937] using wordTrace_append hprefix tailTrace_5125937
  have hstable : (prefixWord ++ tailWord_5125937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125937).length < 2 ^ (prefixWord ++ tailWord_5125937).sum := by decide
  have hdescent : baseEnd_5125937 < baseStart_5125937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125940 : List Nat := [2, 5, 1, 1, 2, 2, 1, 9]
def baseStart_5125940 : Nat := 118140960795 + 5125940 * 2 ^ 59
def prefixEnd_5125940 : Nat := 4983230072969 + 3 ^ 40 * 5125940 * 2
def baseEnd_5125940 : Nat := 97484112078065924810231

theorem tailTrace_5125940 : CollatzResearch.WordTrace tailWord_5125940 prefixEnd_5125940 97484112078065924810231 := by
  unfold tailWord_5125940
  simp only [CollatzResearch.WordTrace]
  refine ⟨93479195524801147849851637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124638927366401530466468849 93479195524801147849851637)
  ·
    refine ⟨8763674580450107610923591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93479195524801147849851637 8763674580450107610923591)
    ·
      refine ⟨13145511870675161416385387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8763674580450107610923591 13145511870675161416385387)
      ·
        refine ⟨19718267806012742124578081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13145511870675161416385387 19718267806012742124578081)
        ·
          refine ⟨14788700854509556593433561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19718267806012742124578081 14788700854509556593433561)
          ·
            refine ⟨11091525640882167445075171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14788700854509556593433561 11091525640882167445075171)
            ·
              refine ⟨16637288461323251167612757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11091525640882167445075171 16637288461323251167612757)
              ·
                refine ⟨97484112078065924810231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16637288461323251167612757 97484112078065924810231)
                ·
                  rfl

theorem cell23_5125940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 9].length) (baseStart_5125940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125940 prefixEnd_5125940 := by exact prefixLift 5125940
  have htrace : WordTrace (prefixWord ++ tailWord_5125940) baseStart_5125940 baseEnd_5125940 := by
    simpa [prefixWord, tailWord_5125940, baseEnd_5125940] using wordTrace_append hprefix tailTrace_5125940
  have hstable : (prefixWord ++ tailWord_5125940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125940).length < 2 ^ (prefixWord ++ tailWord_5125940).sum := by decide
  have hdescent : baseEnd_5125940 < baseStart_5125940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125984 : List Nat := [2, 1, 1, 3, 3, 2, 4, 1, 2, 1, 3]
def baseStart_5125984 : Nat := 118140960795 + 5125984 * 2 ^ 59
def prefixEnd_5125984 : Nat := 4983230072969 + 3 ^ 40 * 5125984 * 2
def baseEnd_5125984 : Nat := 2632093619256577797726035

theorem tailTrace_5125984 : CollatzResearch.WordTrace tailWord_5125984 prefixEnd_5125984 2632093619256577797726035 := by
  unfold tailWord_5125984
  simp only [CollatzResearch.WordTrace]
  refine ⟨93479997930721445607152503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124639997240961927476203337 93479997930721445607152503)
  ·
    refine ⟨140219996896082168410728755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93479997930721445607152503 140219996896082168410728755)
    ·
      refine ⟨210329995344123252616093133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140219996896082168410728755 210329995344123252616093133)
      ·
        refine ⟨78873748254046219731034925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210329995344123252616093133 78873748254046219731034925)
        ·
          refine ⟨29577655595267332399138097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78873748254046219731034925 29577655595267332399138097)
          ·
            refine ⟨22183241696450499299353573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29577655595267332399138097 22183241696450499299353573)
            ·
              refine ⟨4159357818084468618628795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22183241696450499299353573 4159357818084468618628795)
              ·
                refine ⟨6239036727126702927943193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4159357818084468618628795 6239036727126702927943193)
                ·
                  refine ⟨4679277545345027195957395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6239036727126702927943193 4679277545345027195957395)
                  ·
                    refine ⟨7018916318017540793936093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4679277545345027195957395 7018916318017540793936093)
                    ·
                      refine ⟨2632093619256577797726035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7018916318017540793936093 2632093619256577797726035)
                      ·
                        rfl

theorem cell23_5125984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_5125984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125984 prefixEnd_5125984 := by exact prefixLift 5125984
  have htrace : WordTrace (prefixWord ++ tailWord_5125984) baseStart_5125984 baseEnd_5125984 := by
    simpa [prefixWord, tailWord_5125984, baseEnd_5125984] using wordTrace_append hprefix tailTrace_5125984
  have hstable : (prefixWord ++ tailWord_5125984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125984).length < 2 ^ (prefixWord ++ tailWord_5125984).sum := by decide
  have hdescent : baseEnd_5125984 < baseStart_5125984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126003 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 4]
def baseStart_5126003 : Nat := 118140960795 + 5126003 * 2 ^ 59
def prefixEnd_5126003 : Nat := 4983230072969 + 3 ^ 40 * 5126003 * 2
def baseEnd_5126003 : Nat := 2632103375389013223388447

theorem tailTrace_5126003 : CollatzResearch.WordTrace tailWord_5126003 prefixEnd_5126003 2632103375389013223388447 := by
  unfold tailWord_5126003
  simp only [CollatzResearch.WordTrace]
  refine ⟨186960688848374057459246663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124640459232249371639497775 186960688848374057459246663)
  ·
    refine ⟨280441033272561086188869995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186960688848374057459246663 280441033272561086188869995)
    ·
      refine ⟨420661549908841629283304993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280441033272561086188869995 420661549908841629283304993)
      ·
        refine ⟨315496162431631221962478745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420661549908841629283304993 315496162431631221962478745)
        ·
          refine ⟨236622121823723416471859059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315496162431631221962478745 236622121823723416471859059)
          ·
            refine ⟨354933182735585124707788589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236622121823723416471859059 354933182735585124707788589)
            ·
              refine ⟨133099943525844421765420721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 354933182735585124707788589 133099943525844421765420721)
              ·
                refine ⟨99824957644383316324065541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133099943525844421765420721 99824957644383316324065541)
                ·
                  refine ⟨18717179558321871810762289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99824957644383316324065541 18717179558321871810762289)
                  ·
                    refine ⟨14037884668741403858071717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18717179558321871810762289 14037884668741403858071717)
                    ·
                      refine ⟨2632103375389013223388447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14037884668741403858071717 2632103375389013223388447)
                      ·
                        rfl

theorem cell23_5126003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 4].length) (baseStart_5126003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126003 prefixEnd_5126003 := by exact prefixLift 5126003
  have htrace : WordTrace (prefixWord ++ tailWord_5126003) baseStart_5126003 baseEnd_5126003 := by
    simpa [prefixWord, tailWord_5126003, baseEnd_5126003] using wordTrace_append hprefix tailTrace_5126003
  have hstable : (prefixWord ++ tailWord_5126003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126003).length < 2 ^ (prefixWord ++ tailWord_5126003).sum := by decide
  have hdescent : baseEnd_5126003 < baseStart_5126003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126053 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 1, 1, 7]
def baseStart_5126053 : Nat := 118140960795 + 5126053 * 2 ^ 59
def prefixEnd_5126053 : Nat := 4983230072969 + 3 ^ 40 * 5126053 * 2
def baseEnd_5126053 : Nat := 2632129049421738027763217

theorem tailTrace_5126053 : CollatzResearch.WordTrace tailWord_5126053 prefixEnd_5126053 2632129049421738027763217 := by
  unfold tailWord_5126053
  simp only [CollatzResearch.WordTrace]
  refine ⟨186962512498192915998566813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124641674998795277332377875 186962512498192915998566813)
  ·
    refine ⟨70110942186822343499462555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186962512498192915998566813 70110942186822343499462555)
    ·
      refine ⟨105166413280233515249193833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70110942186822343499462555 105166413280233515249193833)
      ·
        refine ⟨78874809960175136436895375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105166413280233515249193833 78874809960175136436895375)
        ·
          refine ⟨118312214940262704655343063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78874809960175136436895375 118312214940262704655343063)
          ·
            refine ⟨177468322410394056983014595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118312214940262704655343063 177468322410394056983014595)
            ·
              refine ⟨266202483615591085474521893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177468322410394056983014595 266202483615591085474521893)
              ·
                refine ⟨49912965677923328526472855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266202483615591085474521893 49912965677923328526472855)
                ·
                  refine ⟨74869448516884992789709283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49912965677923328526472855 74869448516884992789709283)
                  ·
                    refine ⟨112304172775327489184563925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74869448516884992789709283 112304172775327489184563925)
                    ·
                      refine ⟨2632129049421738027763217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112304172775327489184563925 2632129049421738027763217)
                      ·
                        rfl

theorem cell23_5126053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_5126053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126053 prefixEnd_5126053 := by exact prefixLift 5126053
  have htrace : WordTrace (prefixWord ++ tailWord_5126053) baseStart_5126053 baseEnd_5126053 := by
    simpa [prefixWord, tailWord_5126053, baseEnd_5126053] using wordTrace_append hprefix tailTrace_5126053
  have hstable : (prefixWord ++ tailWord_5126053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126053).length < 2 ^ (prefixWord ++ tailWord_5126053).sum := by decide
  have hdescent : baseEnd_5126053 < baseStart_5126053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126062 : List Nat := [4, 1, 5, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_5126062 : Nat := 118140960795 + 5126062 * 2 ^ 59
def prefixEnd_5126062 : Nat := 4983230072969 + 3 ^ 40 * 5126062 * 2
def baseEnd_5126062 : Nat := 2632133670747628492550677

theorem tailTrace_5126062 : CollatzResearch.WordTrace tailWord_5126062 prefixEnd_5126062 2632133670747628492550677 := by
  unfold tailWord_5126062
  simp only [CollatzResearch.WordTrace]
  refine ⟨23370355094395038816955555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124641893836773540357096293 23370355094395038816955555)
  ·
    refine ⟨35055532641592558225433333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23370355094395038816955555 35055532641592558225433333)
    ·
      refine ⟨3286456185149302333634375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35055532641592558225433333 3286456185149302333634375)
      ·
        refine ⟨4929684277723953500451563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3286456185149302333634375 4929684277723953500451563)
        ·
          refine ⟨7394526416585930250677345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4929684277723953500451563 7394526416585930250677345)
          ·
            refine ⟨5545894812439447688008009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7394526416585930250677345 5545894812439447688008009)
            ·
              refine ⟨4159421109329585766006007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5545894812439447688008009 4159421109329585766006007)
              ·
                refine ⟨6239131663994378649009011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4159421109329585766006007 6239131663994378649009011)
                ·
                  refine ⟨9358697495991567973513517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6239131663994378649009011 9358697495991567973513517)
                  ·
                    refine ⟨3509511560996837990067569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9358697495991567973513517 3509511560996837990067569)
                    ·
                      refine ⟨2632133670747628492550677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3509511560996837990067569 2632133670747628492550677)
                      ·
                        rfl

theorem cell23_5126062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_5126062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126062 prefixEnd_5126062 := by exact prefixLift 5126062
  have htrace : WordTrace (prefixWord ++ tailWord_5126062) baseStart_5126062 baseEnd_5126062 := by
    simpa [prefixWord, tailWord_5126062, baseEnd_5126062] using wordTrace_append hprefix tailTrace_5126062
  have hstable : (prefixWord ++ tailWord_5126062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126062).length < 2 ^ (prefixWord ++ tailWord_5126062).sum := by decide
  have hdescent : baseEnd_5126062 < baseStart_5126062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126080 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 4]
def baseStart_5126080 : Nat := 118140960795 + 5126080 * 2 ^ 59
def prefixEnd_5126080 : Nat := 4983230072969 + 3 ^ 40 * 5126080 * 2
def baseEnd_5126080 : Nat := 2632142913399409422125593

theorem tailTrace_5126080 : CollatzResearch.WordTrace tailWord_5126080 prefixEnd_5126080 2632142913399409422125593 := by
  unfold tailWord_5126080
  simp only [CollatzResearch.WordTrace]
  refine ⟨93481748634547549804899847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124642331512730066406533129 93481748634547549804899847)
  ·
    refine ⟨140222622951821324707349771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93481748634547549804899847 140222622951821324707349771)
    ·
      refine ⟨210333934427731987061024657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140222622951821324707349771 210333934427731987061024657)
      ·
        refine ⟨157750450820798990295768493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210333934427731987061024657 157750450820798990295768493)
        ·
          refine ⟨59156419057799621360913185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157750450820798990295768493 59156419057799621360913185)
          ·
            refine ⟨44367314293349716020684889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59156419057799621360913185 44367314293349716020684889)
            ·
              refine ⟨33275485720012287015513667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44367314293349716020684889 33275485720012287015513667)
              ·
                refine ⟨49913228580018430523270501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33275485720012287015513667 49913228580018430523270501)
                ·
                  refine ⟨9358730358753455723113219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49913228580018430523270501 9358730358753455723113219)
                  ·
                    refine ⟨14038095538130183584669829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9358730358753455723113219 14038095538130183584669829)
                    ·
                      refine ⟨2632142913399409422125593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14038095538130183584669829 2632142913399409422125593)
                      ·
                        rfl

theorem cell23_5126080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_5126080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126080 prefixEnd_5126080 := by exact prefixLift 5126080
  have htrace : WordTrace (prefixWord ++ tailWord_5126080) baseStart_5126080 baseEnd_5126080 := by
    simpa [prefixWord, tailWord_5126080, baseEnd_5126080] using wordTrace_append hprefix tailTrace_5126080
  have hstable : (prefixWord ++ tailWord_5126080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126080).length < 2 ^ (prefixWord ++ tailWord_5126080).sum := by decide
  have hdescent : baseEnd_5126080 < baseStart_5126080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126197 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 4, 4]
def baseStart_5126197 : Nat := 118140960795 + 5126197 * 2 ^ 59
def prefixEnd_5126197 : Nat := 4983230072969 + 3 ^ 40 * 5126197 * 2
def baseEnd_5126197 : Nat := 877400996878661821454185

theorem tailTrace_5126197 : CollatzResearch.WordTrace tailWord_5126197 prefixEnd_5126197 877400996878661821454185 := by
  unfold tailWord_5126197
  simp only [CollatzResearch.WordTrace]
  refine ⟨186967764609671228591808845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124645176406447485727872563 186967764609671228591808845)
  ·
    refine ⟨70112911728626710721928317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186967764609671228591808845 70112911728626710721928317)
    ·
      refine ⟨26292341898235016520723119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70112911728626710721928317 26292341898235016520723119)
      ·
        refine ⟨39438512847352524781084679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26292341898235016520723119 39438512847352524781084679)
        ·
          refine ⟨59157769271028787171627019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39438512847352524781084679 59157769271028787171627019)
          ·
            refine ⟨88736653906543180757440529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59157769271028787171627019 88736653906543180757440529)
            ·
              refine ⟨66552490429907385568080397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88736653906543180757440529 66552490429907385568080397)
              ·
                refine ⟨24957183911215269588030149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66552490429907385568080397 24957183911215269588030149)
                ·
                  refine ⟨4679471983352863047755653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24957183911215269588030149 4679471983352863047755653)
                  ·
                    refine ⟨877400996878661821454185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4679471983352863047755653 877400996878661821454185)
                    ·
                      rfl

theorem cell23_5126197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_5126197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126197 prefixEnd_5126197 := by exact prefixLift 5126197
  have htrace : WordTrace (prefixWord ++ tailWord_5126197) baseStart_5126197 baseEnd_5126197 := by
    simpa [prefixWord, tailWord_5126197, baseEnd_5126197] using wordTrace_append hprefix tailTrace_5126197
  have hstable : (prefixWord ++ tailWord_5126197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126197).length < 2 ^ (prefixWord ++ tailWord_5126197).sum := by decide
  have hdescent : baseEnd_5126197 < baseStart_5126197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126198 : List Nat := [5, 1, 2, 1, 1, 1, 3, 4, 1, 1, 3]
def baseStart_5126198 : Nat := 118140960795 + 5126198 * 2 ^ 59
def prefixEnd_5126198 : Nat := 4983230072969 + 3 ^ 40 * 5126198 * 2
def baseEnd_5126198 : Nat := 2632203504116639960450051

theorem tailTrace_5126198 : CollatzResearch.WordTrace tailWord_5126198 prefixEnd_5126198 2632203504116639960450051 := by
  unfold tailWord_5126198
  simp only [CollatzResearch.WordTrace]
  refine ⟨11685487567666725360162203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124645200721778403841730165 11685487567666725360162203)
  ·
    refine ⟨17528231351500088040243305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11685487567666725360162203 17528231351500088040243305)
    ·
      refine ⟨13146173513625066030182479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17528231351500088040243305 13146173513625066030182479)
      ·
        refine ⟨19719260270437599045273719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13146173513625066030182479 19719260270437599045273719)
        ·
          refine ⟨29578890405656398567910579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19719260270437599045273719 29578890405656398567910579)
          ·
            refine ⟨44368335608484597851865869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29578890405656398567910579 44368335608484597851865869)
            ·
              refine ⟨16638125853181724194449701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44368335608484597851865869 16638125853181724194449701)
              ·
                refine ⟨3119648597471573286459319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16638125853181724194449701 3119648597471573286459319)
                ·
                  refine ⟨4679472896207359929688979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3119648597471573286459319 4679472896207359929688979)
                  ·
                    refine ⟨7019209344311039894533469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4679472896207359929688979 7019209344311039894533469)
                    ·
                      refine ⟨2632203504116639960450051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7019209344311039894533469 2632203504116639960450051)
                      ·
                        rfl

theorem cell23_5126198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_5126198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126198 prefixEnd_5126198 := by exact prefixLift 5126198
  have htrace : WordTrace (prefixWord ++ tailWord_5126198) baseStart_5126198 baseEnd_5126198 := by
    simpa [prefixWord, tailWord_5126198, baseEnd_5126198] using wordTrace_append hprefix tailTrace_5126198
  have hstable : (prefixWord ++ tailWord_5126198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126198).length < 2 ^ (prefixWord ++ tailWord_5126198).sum := by decide
  have hdescent : baseEnd_5126198 < baseStart_5126198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126207 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 3]
def baseStart_5126207 : Nat := 118140960795 + 5126207 * 2 ^ 59
def prefixEnd_5126207 : Nat := 4983230072969 + 3 ^ 40 * 5126207 * 2
def baseEnd_5126207 : Nat := 2632208125442530425237509

theorem tailTrace_5126207 : CollatzResearch.WordTrace tailWord_5126207 prefixEnd_5126207 2632208125442530425237509 := by
  unfold tailWord_5126207
  simp only [CollatzResearch.WordTrace]
  refine ⟨186968129339635000299672875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124645419559756666866448583 186968129339635000299672875)
  ·
    refine ⟨280452194009452500449509313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186968129339635000299672875 280452194009452500449509313)
    ·
      refine ⟨210339145507089375337131985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280452194009452500449509313 210339145507089375337131985)
      ·
        refine ⟨157754359130317031502848989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210339145507089375337131985 157754359130317031502848989)
        ·
          refine ⟨59157884673868886813568371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157754359130317031502848989 59157884673868886813568371)
          ·
            refine ⟨88736827010803330220352557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59157884673868886813568371 88736827010803330220352557)
            ·
              refine ⟨33276310129051248832632209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88736827010803330220352557 33276310129051248832632209)
              ·
                refine ⟨24957232596788436624474157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33276310129051248832632209 24957232596788436624474157)
                ·
                  refine ⟨9358962223795663734177809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24957232596788436624474157 9358962223795663734177809)
                  ·
                    refine ⟨7019221667846747800633357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9358962223795663734177809 7019221667846747800633357)
                    ·
                      refine ⟨2632208125442530425237509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7019221667846747800633357 2632208125442530425237509)
                      ·
                        rfl

theorem cell23_5126207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_5126207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126207 prefixEnd_5126207 := by exact prefixLift 5126207
  have htrace : WordTrace (prefixWord ++ tailWord_5126207) baseStart_5126207 baseEnd_5126207 := by
    simpa [prefixWord, tailWord_5126207, baseEnd_5126207] using wordTrace_append hprefix tailTrace_5126207
  have hstable : (prefixWord ++ tailWord_5126207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126207).length < 2 ^ (prefixWord ++ tailWord_5126207).sum := by decide
  have hdescent : baseEnd_5126207 < baseStart_5126207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126217 : List Nat := [1, 2, 1, 1, 2, 2, 6, 1, 1, 2, 4]
def baseStart_5126217 : Nat := 118140960795 + 5126217 * 2 ^ 59
def prefixEnd_5126217 : Nat := 4983230072969 + 3 ^ 40 * 5126217 * 2
def baseEnd_5126217 : Nat := 2632213260249075386112463

theorem tailTrace_5126217 : CollatzResearch.WordTrace tailWord_5126217 prefixEnd_5126217 2632213260249075386112463 := by
  unfold tailWord_5126217
  simp only [CollatzResearch.WordTrace]
  refine ⟨186968494069598772007536905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124645662713065848005024603 186968494069598772007536905)
  ·
    refine ⟨140226370552199079005652679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186968494069598772007536905 140226370552199079005652679)
    ·
      refine ⟨210339555828298618508479019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140226370552199079005652679 210339555828298618508479019)
      ·
        refine ⟨315509333742447927762718529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210339555828298618508479019 315509333742447927762718529)
        ·
          refine ⟨236632000306835945822038897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315509333742447927762718529 236632000306835945822038897)
          ·
            refine ⟨177474000230126959366529173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236632000306835945822038897 177474000230126959366529173)
            ·
              refine ⟨8319093760787201220306055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 177474000230126959366529173 8319093760787201220306055)
              ·
                refine ⟨12478640641180801830459083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8319093760787201220306055 12478640641180801830459083)
                ·
                  refine ⟨18717960961771202745688625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12478640641180801830459083 18717960961771202745688625)
                  ·
                    refine ⟨14038470721328402059266469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18717960961771202745688625 14038470721328402059266469)
                    ·
                      refine ⟨2632213260249075386112463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14038470721328402059266469 2632213260249075386112463)
                      ·
                        rfl

theorem cell23_5126217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 2, 4].length) (baseStart_5126217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126217 prefixEnd_5126217 := by exact prefixLift 5126217
  have htrace : WordTrace (prefixWord ++ tailWord_5126217) baseStart_5126217 baseEnd_5126217 := by
    simpa [prefixWord, tailWord_5126217, baseEnd_5126217] using wordTrace_append hprefix tailTrace_5126217
  have hstable : (prefixWord ++ tailWord_5126217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126217).length < 2 ^ (prefixWord ++ tailWord_5126217).sum := by decide
  have hdescent : baseEnd_5126217 < baseStart_5126217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126281 : List Nat := [1, 2, 1, 1, 4, 2, 4, 2, 1, 3, 2]
def baseStart_5126281 : Nat := 118140960795 + 5126281 * 2 ^ 59
def prefixEnd_5126281 : Nat := 4983230072969 + 3 ^ 40 * 5126281 * 2
def baseEnd_5126281 : Nat := 2632246123010963135712169

theorem tailTrace_5126281 : CollatzResearch.WordTrace tailWord_5126281 prefixEnd_5126281 2632246123010963135712169 := by
  unfold tailWord_5126281
  simp only [CollatzResearch.WordTrace]
  refine ⟨186970828341366910937866697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124647218894244607291911131 186970828341366910937866697)
  ·
    refine ⟨140228121256025183203400023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186970828341366910937866697 140228121256025183203400023)
    ·
      refine ⟨210342181884037774805100035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140228121256025183203400023 210342181884037774805100035)
      ·
        refine ⟨315513272826056662207650053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210342181884037774805100035 315513272826056662207650053)
        ·
          refine ⟨59158738654885624163934385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 315513272826056662207650053 59158738654885624163934385)
          ·
            refine ⟨44369053991164218122950789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59158738654885624163934385 44369053991164218122950789)
            ·
              refine ⟨8319197623343290898053273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44369053991164218122950789 8319197623343290898053273)
              ·
                refine ⟨6239398217507468173539955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8319197623343290898053273 6239398217507468173539955)
                ·
                  refine ⟨9359097326261202260309933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6239398217507468173539955 9359097326261202260309933)
                  ·
                    refine ⟨3509661497347950847616225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9359097326261202260309933 3509661497347950847616225)
                    ·
                      refine ⟨2632246123010963135712169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3509661497347950847616225 2632246123010963135712169)
                      ·
                        rfl

theorem cell23_5126281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 3, 2].length) (baseStart_5126281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126281 prefixEnd_5126281 := by exact prefixLift 5126281
  have htrace : WordTrace (prefixWord ++ tailWord_5126281) baseStart_5126281 baseEnd_5126281 := by
    simpa [prefixWord, tailWord_5126281, baseEnd_5126281] using wordTrace_append hprefix tailTrace_5126281
  have hstable : (prefixWord ++ tailWord_5126281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126281).length < 2 ^ (prefixWord ++ tailWord_5126281).sum := by decide
  have hdescent : baseEnd_5126281 < baseStart_5126281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126367 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 4]
def baseStart_5126367 : Nat := 118140960795 + 5126367 * 2 ^ 59
def prefixEnd_5126367 : Nat := 4983230072969 + 3 ^ 40 * 5126367 * 2
def baseEnd_5126367 : Nat := 2632290282347249799236773

theorem tailTrace_5126367 : CollatzResearch.WordTrace tailWord_5126367 prefixEnd_5126367 2632290282347249799236773 := by
  unfold tailWord_5126367
  simp only [CollatzResearch.WordTrace]
  refine ⟨186973965019055347625497355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124649310012703565083664903 186973965019055347625497355)
  ·
    refine ⟨280460947528583021438246033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186973965019055347625497355 280460947528583021438246033)
    ·
      refine ⟨210345710646437266078684525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280460947528583021438246033 210345710646437266078684525)
      ·
        refine ⟨78879641492413974779506697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210345710646437266078684525 78879641492413974779506697)
        ·
          refine ⟨59159731119310481084630023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78879641492413974779506697 59159731119310481084630023)
          ·
            refine ⟨88739596678965721626945035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59159731119310481084630023 88739596678965721626945035)
            ·
              refine ⟨133109395018448582440417553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88739596678965721626945035 133109395018448582440417553)
              ·
                refine ⟨99832046263836436830313165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133109395018448582440417553 99832046263836436830313165)
                ·
                  refine ⟨37437017348938663811367437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99832046263836436830313165 37437017348938663811367437)
                  ·
                    refine ⟨14038881505851998929262789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37437017348938663811367437 14038881505851998929262789)
                    ·
                      refine ⟨2632290282347249799236773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14038881505851998929262789 2632290282347249799236773)
                      ·
                        rfl

theorem cell23_5126367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_5126367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126367 prefixEnd_5126367 := by exact prefixLift 5126367
  have htrace : WordTrace (prefixWord ++ tailWord_5126367) baseStart_5126367 baseEnd_5126367 := by
    simpa [prefixWord, tailWord_5126367, baseEnd_5126367] using wordTrace_append hprefix tailTrace_5126367
  have hstable : (prefixWord ++ tailWord_5126367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126367).length < 2 ^ (prefixWord ++ tailWord_5126367).sum := by decide
  have hdescent : baseEnd_5126367 < baseStart_5126367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126394 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 5, 4]
def baseStart_5126394 : Nat := 118140960795 + 5126394 * 2 ^ 59
def prefixEnd_5126394 : Nat := 4983230072969 + 3 ^ 40 * 5126394 * 2
def baseEnd_5126394 : Nat := 877434715441640397866383

theorem tailTrace_5126394 : CollatzResearch.WordTrace tailWord_5126394 prefixEnd_5126394 877434715441640397866383 := by
  unfold tailWord_5126394
  simp only [CollatzResearch.WordTrace]
  refine ⟨46743737447489382809182559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124649966526638354157820157 46743737447489382809182559)
  ·
    refine ⟨70115606171234074213773839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46743737447489382809182559 70115606171234074213773839)
    ·
      refine ⟨105173409256851111320660759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70115606171234074213773839 105173409256851111320660759)
      ·
        refine ⟨157760113885276666980991139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105173409256851111320660759 157760113885276666980991139)
        ·
          refine ⟨236640170827915000471486709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157760113885276666980991139 236640170827915000471486709)
          ·
            refine ⟨22185016015117031294201879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 236640170827915000471486709 22185016015117031294201879)
            ·
              refine ⟨33277524022675546941302819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22185016015117031294201879 33277524022675546941302819)
              ·
                refine ⟨49916286034013320411954229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33277524022675546941302819 49916286034013320411954229)
                ·
                  refine ⟨4679651815688748788620709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49916286034013320411954229 4679651815688748788620709)
                  ·
                    refine ⟨877434715441640397866383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4679651815688748788620709 877434715441640397866383)
                    ·
                      rfl

theorem cell23_5126394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 5, 4].length) (baseStart_5126394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126394 prefixEnd_5126394 := by exact prefixLift 5126394
  have htrace : WordTrace (prefixWord ++ tailWord_5126394) baseStart_5126394 baseEnd_5126394 := by
    simpa [prefixWord, tailWord_5126394, baseEnd_5126394] using wordTrace_append hprefix tailTrace_5126394
  have hstable : (prefixWord ++ tailWord_5126394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126394).length < 2 ^ (prefixWord ++ tailWord_5126394).sum := by decide
  have hdescent : baseEnd_5126394 < baseStart_5126394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126397 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_5126397 : Nat := 118140960795 + 5126397 * 2 ^ 59
def prefixEnd_5126397 : Nat := 4983230072969 + 3 ^ 40 * 5126397 * 2
def baseEnd_5126397 : Nat := 2632305686766884681861635

theorem tailTrace_5126397 : CollatzResearch.WordTrace tailWord_5126397 prefixEnd_5126397 2632305686766884681861635 := by
  unfold tailWord_5126397
  simp only [CollatzResearch.WordTrace]
  refine ⟨186975059208946662749089445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124650039472631108499392963 186975059208946662749089445)
  ·
    refine ⟨35057823601677499265454271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186975059208946662749089445 35057823601677499265454271)
    ·
      refine ⟨52586735402516248898181407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35057823601677499265454271 52586735402516248898181407)
      ·
        refine ⟨78880103103774373347272111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52586735402516248898181407 78880103103774373347272111)
        ·
          refine ⟨118320154655661560020908167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78880103103774373347272111 118320154655661560020908167)
          ·
            refine ⟨177480231983492340031362251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118320154655661560020908167 177480231983492340031362251)
            ·
              refine ⟨266220347975238510047043377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177480231983492340031362251 266220347975238510047043377)
              ·
                refine ⟨199665260981428882535282533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266220347975238510047043377 199665260981428882535282533)
                ·
                  refine ⟨37437236434017915475365475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 199665260981428882535282533 37437236434017915475365475)
                  ·
                    refine ⟨56155854651026873213048213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37437236434017915475365475 56155854651026873213048213)
                    ·
                      refine ⟨2632305686766884681861635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56155854651026873213048213 2632305686766884681861635)
                      ·
                        rfl

theorem cell23_5126397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_5126397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126397 prefixEnd_5126397 := by exact prefixLift 5126397
  have htrace : WordTrace (prefixWord ++ tailWord_5126397) baseStart_5126397 baseEnd_5126397 := by
    simpa [prefixWord, tailWord_5126397, baseEnd_5126397] using wordTrace_append hprefix tailTrace_5126397
  have hstable : (prefixWord ++ tailWord_5126397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126397).length < 2 ^ (prefixWord ++ tailWord_5126397).sum := by decide
  have hdescent : baseEnd_5126397 < baseStart_5126397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126427 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 6]
def baseStart_5126427 : Nat := 118140960795 + 5126427 * 2 ^ 59
def prefixEnd_5126427 : Nat := 4983230072969 + 3 ^ 40 * 5126427 * 2
def baseEnd_5126427 : Nat := 2632321091186519564486497

theorem tailTrace_5126427 : CollatzResearch.WordTrace tailWord_5126427 prefixEnd_5126427 2632321091186519564486497 := by
  unfold tailWord_5126427
  simp only [CollatzResearch.WordTrace]
  refine ⟨186976153398837977872681535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124650768932558651915121023 186976153398837977872681535)
  ·
    refine ⟨280464230098256966809022303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186976153398837977872681535 280464230098256966809022303)
    ·
      refine ⟨420696345147385450213533455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280464230098256966809022303 420696345147385450213533455)
      ·
        refine ⟨631044517721078175320300183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420696345147385450213533455 631044517721078175320300183)
        ·
          refine ⟨946566776581617262980450275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 631044517721078175320300183 946566776581617262980450275)
          ·
            refine ⟨1419850164872425894470675413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 946566776581617262980450275 1419850164872425894470675413)
            ·
              refine ⟨33277738239197481901656455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1419850164872425894470675413 33277738239197481901656455)
              ·
                refine ⟨49916607358796222852484683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33277738239197481901656455 49916607358796222852484683)
                ·
                  refine ⟨74874911038194334278727025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49916607358796222852484683 74874911038194334278727025)
                  ·
                    refine ⟨56156183278645750709045269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74874911038194334278727025 56156183278645750709045269)
                    ·
                      refine ⟨2632321091186519564486497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56156183278645750709045269 2632321091186519564486497)
                      ·
                        rfl

theorem cell23_5126427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 6].length) (baseStart_5126427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126427 prefixEnd_5126427 := by exact prefixLift 5126427
  have htrace : WordTrace (prefixWord ++ tailWord_5126427) baseStart_5126427 baseEnd_5126427 := by
    simpa [prefixWord, tailWord_5126427, baseEnd_5126427] using wordTrace_append hprefix tailTrace_5126427
  have hstable : (prefixWord ++ tailWord_5126427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126427).length < 2 ^ (prefixWord ++ tailWord_5126427).sum := by decide
  have hdescent : baseEnd_5126427 < baseStart_5126427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126447 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 7]
def baseStart_5126447 : Nat := 118140960795 + 5126447 * 2 ^ 59
def prefixEnd_5126447 : Nat := 4983230072969 + 3 ^ 40 * 5126447 * 2
def baseEnd_5126447 : Nat := 2632331360799609486236405

theorem tailTrace_5126447 : CollatzResearch.WordTrace tailWord_5126447 prefixEnd_5126447 2632331360799609486236405 := by
  unfold tailWord_5126447
  simp only [CollatzResearch.WordTrace]
  refine ⟨186976882858765521288409595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124651255239177014192273063 186976882858765521288409595)
  ·
    refine ⟨280465324288148281932614393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186976882858765521288409595 280465324288148281932614393)
    ·
      refine ⟨210348993216111211449460795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280465324288148281932614393 210348993216111211449460795)
      ·
        refine ⟨315523489824166817174191193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210348993216111211449460795 315523489824166817174191193)
        ·
          refine ⟨236642617368125112880643395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315523489824166817174191193 236642617368125112880643395)
          ·
            refine ⟨354963926052187669320965093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236642617368125112880643395 354963926052187669320965093)
            ·
              refine ⟨66555736134785187997680955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 354963926052187669320965093 66555736134785187997680955)
              ·
                refine ⟨99833604202177781996521433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66555736134785187997680955 99833604202177781996521433)
                ·
                  refine ⟨74875203151633336497391075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99833604202177781996521433 74875203151633336497391075)
                  ·
                    refine ⟨112312804727450004746086613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74875203151633336497391075 112312804727450004746086613)
                    ·
                      refine ⟨2632331360799609486236405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112312804727450004746086613 2632331360799609486236405)
                      ·
                        rfl

theorem cell23_5126447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_5126447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126447 prefixEnd_5126447 := by exact prefixLift 5126447
  have htrace : WordTrace (prefixWord ++ tailWord_5126447) baseStart_5126447 baseEnd_5126447 := by
    simpa [prefixWord, tailWord_5126447, baseEnd_5126447] using wordTrace_append hprefix tailTrace_5126447
  have hstable : (prefixWord ++ tailWord_5126447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126447).length < 2 ^ (prefixWord ++ tailWord_5126447).sum := by decide
  have hdescent : baseEnd_5126447 < baseStart_5126447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126451 : List Nat := [1, 1, 1, 2, 5, 1, 1, 4, 3, 1, 3]
def baseStart_5126451 : Nat := 118140960795 + 5126451 * 2 ^ 59
def prefixEnd_5126451 : Nat := 4983230072969 + 3 ^ 40 * 5126451 * 2
def baseEnd_5126451 : Nat := 2632333414722227470586387

theorem tailTrace_5126451 : CollatzResearch.WordTrace tailWord_5126451 prefixEnd_5126451 2632333414722227470586387 := by
  unfold tailWord_5126451
  simp only [CollatzResearch.WordTrace]
  refine ⟨186977028750751029971555207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124651352500500686647703471 186977028750751029971555207)
  ·
    refine ⟨280465543126126544957332811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186977028750751029971555207 280465543126126544957332811)
    ·
      refine ⟨420698314689189817435999217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280465543126126544957332811 420698314689189817435999217)
      ·
        refine ⟨315523736016892363076999413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420698314689189817435999217 315523736016892363076999413)
        ·
          refine ⟨29580350251583659038468695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 315523736016892363076999413 29580350251583659038468695)
          ·
            refine ⟨44370525377375488557703043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29580350251583659038468695 44370525377375488557703043)
            ·
              refine ⟨66555788066063232836554565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44370525377375488557703043 66555788066063232836554565)
              ·
                refine ⟨12479210262386856156853981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66555788066063232836554565 12479210262386856156853981)
                ·
                  refine ⟨4679703848395071058820243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12479210262386856156853981 4679703848395071058820243)
                  ·
                    refine ⟨7019555772592606588230365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4679703848395071058820243 7019555772592606588230365)
                    ·
                      refine ⟨2632333414722227470586387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7019555772592606588230365 2632333414722227470586387)
                      ·
                        rfl

theorem cell23_5126451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 1, 3].length) (baseStart_5126451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126451 prefixEnd_5126451 := by exact prefixLift 5126451
  have htrace : WordTrace (prefixWord ++ tailWord_5126451) baseStart_5126451 baseEnd_5126451 := by
    simpa [prefixWord, tailWord_5126451, baseEnd_5126451] using wordTrace_append hprefix tailTrace_5126451
  have hstable : (prefixWord ++ tailWord_5126451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126451).length < 2 ^ (prefixWord ++ tailWord_5126451).sum := by decide
  have hdescent : baseEnd_5126451 < baseStart_5126451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126474 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 7, 1, 4]
def baseStart_5126474 : Nat := 118140960795 + 5126474 * 2 ^ 59
def prefixEnd_5126474 : Nat := 4983230072969 + 3 ^ 40 * 5126474 * 2
def baseEnd_5126474 : Nat := 2632345224777280880598781

theorem tailTrace_5126474 : CollatzResearch.WordTrace tailWord_5126474 prefixEnd_5126474 2632345224777280880598781 := by
  unfold tailWord_5126474
  simp only [CollatzResearch.WordTrace]
  refine ⟨46744466907416926224910619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124651911753111803266428317 46744466907416926224910619)
  ·
    refine ⟨70116700361125389337365929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46744466907416926224910619 70116700361125389337365929)
    ·
      refine ⟨52587525270844042003024447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70116700361125389337365929 52587525270844042003024447)
      ·
        refine ⟨78881287906266063004536671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52587525270844042003024447 78881287906266063004536671)
        ·
          refine ⟨118321931859399094506805007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78881287906266063004536671 118321931859399094506805007)
          ·
            refine ⟨177482897789098641760207511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118321931859399094506805007 177482897789098641760207511)
            ·
              refine ⟨266224346683647962640311267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177482897789098641760207511 266224346683647962640311267)
              ·
                refine ⟨399336520025471943960466901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266224346683647962640311267 399336520025471943960466901)
                ·
                  refine ⟨9359449688096998686573443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 399336520025471943960466901 9359449688096998686573443)
                  ·
                    refine ⟨14039174532145498029860165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9359449688096998686573443 14039174532145498029860165)
                    ·
                      refine ⟨2632345224777280880598781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14039174532145498029860165 2632345224777280880598781)
                      ·
                        rfl

theorem cell23_5126474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_5126474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126474 prefixEnd_5126474 := by exact prefixLift 5126474
  have htrace : WordTrace (prefixWord ++ tailWord_5126474) baseStart_5126474 baseEnd_5126474 := by
    simpa [prefixWord, tailWord_5126474, baseEnd_5126474] using wordTrace_append hprefix tailTrace_5126474
  have hstable : (prefixWord ++ tailWord_5126474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126474).length < 2 ^ (prefixWord ++ tailWord_5126474).sum := by decide
  have hdescent : baseEnd_5126474 < baseStart_5126474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126485 : List Nat := [1, 3, 2, 2, 4, 2, 1, 1, 3, 1, 3]
def baseStart_5126485 : Nat := 118140960795 + 5126485 * 2 ^ 59
def prefixEnd_5126485 : Nat := 4983230072969 + 3 ^ 40 * 5126485 * 2
def baseEnd_5126485 : Nat := 2632350873064480337561231

theorem tailTrace_5126485 : CollatzResearch.WordTrace tailWord_5126485 prefixEnd_5126485 2632350873064480337561231 := by
  unfold tailWord_5126485
  simp only [CollatzResearch.WordTrace]
  refine ⟨186978268832627853778292909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124652179221751902518861939 186978268832627853778292909)
  ·
    refine ⟨70116850812235445166859841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186978268832627853778292909 70116850812235445166859841)
    ·
      refine ⟨52587638109176583875144881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70116850812235445166859841 52587638109176583875144881)
      ·
        refine ⟨39440728581882437906358661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52587638109176583875144881 39440728581882437906358661)
        ·
          refine ⟨7395136609102957107442249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39440728581882437906358661 7395136609102957107442249)
          ·
            refine ⟨5546352456827217830581687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7395136609102957107442249 5546352456827217830581687)
            ·
              refine ⟨8319528685240826745872531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5546352456827217830581687 8319528685240826745872531)
              ·
                refine ⟨12479293027861240118808797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8319528685240826745872531 12479293027861240118808797)
                ·
                  refine ⟨4679734885447965044553299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12479293027861240118808797 4679734885447965044553299)
                  ·
                    refine ⟨7019602328171947566829949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4679734885447965044553299 7019602328171947566829949)
                    ·
                      refine ⟨2632350873064480337561231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7019602328171947566829949 2632350873064480337561231)
                      ·
                        rfl

theorem cell23_5126485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_5126485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126485 prefixEnd_5126485 := by exact prefixLift 5126485
  have htrace : WordTrace (prefixWord ++ tailWord_5126485) baseStart_5126485 baseEnd_5126485 := by
    simpa [prefixWord, tailWord_5126485, baseEnd_5126485] using wordTrace_append hprefix tailTrace_5126485
  have hstable : (prefixWord ++ tailWord_5126485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126485).length < 2 ^ (prefixWord ++ tailWord_5126485).sum := by decide
  have hdescent : baseEnd_5126485 < baseStart_5126485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126492 : List Nat := [2, 2, 4, 3, 2, 1, 2, 1, 6]
def baseStart_5126492 : Nat := 118140960795 + 5126492 * 2 ^ 59
def prefixEnd_5126492 : Nat := 4983230072969 + 3 ^ 40 * 5126492 * 2
def baseEnd_5126492 : Nat := 292483829714340201130411

theorem tailTrace_5126492 : CollatzResearch.WordTrace tailWord_5126492 prefixEnd_5126492 292483829714340201130411 := by
  unfold tailWord_5126492
  simp only [CollatzResearch.WordTrace]
  refine ⟨93489262071801246986898865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124652349429068329315865153 93489262071801246986898865)
  ·
    refine ⟨70116946553850935240174149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93489262071801246986898865 70116946553850935240174149)
    ·
      refine ⟨13146927478847050357532653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70116946553850935240174149 13146927478847050357532653)
      ·
        refine ⟨4930097804567643884074745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13146927478847050357532653 4930097804567643884074745)
        ·
          refine ⟨3697573353425732913056059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4930097804567643884074745 3697573353425732913056059)
          ·
            refine ⟨5546360030138599369584089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3697573353425732913056059 5546360030138599369584089)
            ·
              refine ⟨4159770022603949527188067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5546360030138599369584089 4159770022603949527188067)
              ·
                refine ⟨6239655033905924290782101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4159770022603949527188067 6239655033905924290782101)
                ·
                  refine ⟨292483829714340201130411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6239655033905924290782101 292483829714340201130411)
                  ·
                    rfl

theorem cell23_5126492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 6].length) (baseStart_5126492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126492 prefixEnd_5126492 := by exact prefixLift 5126492
  have htrace : WordTrace (prefixWord ++ tailWord_5126492) baseStart_5126492 baseEnd_5126492 := by
    simpa [prefixWord, tailWord_5126492, baseEnd_5126492] using wordTrace_append hprefix tailTrace_5126492
  have hstable : (prefixWord ++ tailWord_5126492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126492).length < 2 ^ (prefixWord ++ tailWord_5126492).sum := by decide
  have hdescent : baseEnd_5126492 < baseStart_5126492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126511 : List Nat := [1, 1, 2, 1, 3, 1, 2, 6, 1, 2, 3]
def baseStart_5126511 : Nat := 118140960795 + 5126511 * 2 ^ 59
def prefixEnd_5126511 : Nat := 4983230072969 + 3 ^ 40 * 5126511 * 2
def baseEnd_5126511 : Nat := 2632364223561497235836111

theorem tailTrace_5126511 : CollatzResearch.WordTrace tailWord_5126511 prefixEnd_5126511 2632364223561497235836111 := by
  unfold tailWord_5126511
  simp only [CollatzResearch.WordTrace]
  refine ⟨186979217130533660218739387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124652811420355773479159591 186979217130533660218739387)
  ·
    refine ⟨280468825695800490328109081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186979217130533660218739387 280468825695800490328109081)
    ·
      refine ⟨210351619271850367746081811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280468825695800490328109081 210351619271850367746081811)
      ·
        refine ⟨315527428907775551619122717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210351619271850367746081811 315527428907775551619122717)
        ·
          refine ⟨118322785840415831857171019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 315527428907775551619122717 118322785840415831857171019)
          ·
            refine ⟨177484178760623747785756529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118322785840415831857171019 177484178760623747785756529)
            ·
              refine ⟨133113134070467810839317397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177484178760623747785756529 133113134070467810839317397)
              ·
                refine ⟨6239678159553178633093003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 133113134070467810839317397 6239678159553178633093003)
                ·
                  refine ⟨9359517239329767949639505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6239678159553178633093003 9359517239329767949639505)
                  ·
                    refine ⟨7019637929497325962229629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9359517239329767949639505 7019637929497325962229629)
                    ·
                      refine ⟨2632364223561497235836111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7019637929497325962229629 2632364223561497235836111)
                      ·
                        rfl

theorem cell23_5126511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 2, 3].length) (baseStart_5126511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126511 prefixEnd_5126511 := by exact prefixLift 5126511
  have htrace : WordTrace (prefixWord ++ tailWord_5126511) baseStart_5126511 baseEnd_5126511 := by
    simpa [prefixWord, tailWord_5126511, baseEnd_5126511] using wordTrace_append hprefix tailTrace_5126511
  have hstable : (prefixWord ++ tailWord_5126511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126511).length < 2 ^ (prefixWord ++ tailWord_5126511).sum := by decide
  have hdescent : baseEnd_5126511 < baseStart_5126511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126514 : List Nat := [3, 2, 1, 2, 1, 3, 2, 9]
def baseStart_5126514 : Nat := 118140960795 + 5126514 * 2 ^ 59
def prefixEnd_5126514 : Nat := 4983230072969 + 3 ^ 40 * 5126514 * 2
def baseEnd_5126514 : Nat := 97495028296424471262911

theorem tailTrace_5126514 : CollatzResearch.WordTrace tailWord_5126514 prefixEnd_5126514 97495028296424471262911 := by
  unfold tailWord_5126514
  simp only [CollatzResearch.WordTrace]
  refine ⟨46744831637380697932774649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124652884366348527820732397 46744831637380697932774649)
  ·
    refine ⟨35058623728035523449580987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46744831637380697932774649 35058623728035523449580987)
    ·
      refine ⟨52587935592053285174371481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35058623728035523449580987 52587935592053285174371481)
      ·
        refine ⟨39440951694039963880778611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52587935592053285174371481 39440951694039963880778611)
        ·
          refine ⟨59161427541059945821167917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39440951694039963880778611 59161427541059945821167917)
          ·
            refine ⟨22185535327897479682937969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59161427541059945821167917 22185535327897479682937969)
            ·
              refine ⟨16639151495923109762203477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22185535327897479682937969 16639151495923109762203477)
              ·
                refine ⟨97495028296424471262911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16639151495923109762203477 97495028296424471262911)
                ·
                  rfl

theorem cell23_5126514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 9].length) (baseStart_5126514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126514 prefixEnd_5126514 := by exact prefixLift 5126514
  have htrace : WordTrace (prefixWord ++ tailWord_5126514) baseStart_5126514 baseEnd_5126514 := by
    simpa [prefixWord, tailWord_5126514, baseEnd_5126514] using wordTrace_append hprefix tailTrace_5126514
  have hstable : (prefixWord ++ tailWord_5126514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126514).length < 2 ^ (prefixWord ++ tailWord_5126514).sum := by decide
  have hdescent : baseEnd_5126514 < baseStart_5126514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126548 : List Nat := [2, 4, 2, 1, 3, 2, 1, 8]
def baseStart_5126548 : Nat := 118140960795 + 5126548 * 2 ^ 59
def prefixEnd_5126548 : Nat := 4983230072969 + 3 ^ 40 * 5126548 * 2
def baseEnd_5126548 : Nat := 97495674901693095965683

theorem tailTrace_5126548 : CollatzResearch.WordTrace tailWord_5126548 prefixEnd_5126548 97495674901693095965683 := by
  unfold tailWord_5126548
  simp only [CollatzResearch.WordTrace]
  refine ⟨93490283315699807768918149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124653711087599743691890865 93490283315699807768918149)
  ·
    refine ⟨17529428121693713956672153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93490283315699807768918149 17529428121693713956672153)
    ·
      refine ⟨13147071091270285467504115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17529428121693713956672153 13147071091270285467504115)
      ·
        refine ⟨19720606636905428201256173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13147071091270285467504115 19720606636905428201256173)
        ·
          refine ⟨7395227488839535575471065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19720606636905428201256173 7395227488839535575471065)
          ·
            refine ⟨5546420616629651681603299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7395227488839535575471065 5546420616629651681603299)
            ·
              refine ⟨8319630924944477522404949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5546420616629651681603299 8319630924944477522404949)
              ·
                refine ⟨97495674901693095965683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8319630924944477522404949 97495674901693095965683)
                ·
                  rfl

theorem cell23_5126548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 8].length) (baseStart_5126548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126548 prefixEnd_5126548 := by exact prefixLift 5126548
  have htrace : WordTrace (prefixWord ++ tailWord_5126548) baseStart_5126548 baseEnd_5126548 := by
    simpa [prefixWord, tailWord_5126548, baseEnd_5126548] using wordTrace_append hprefix tailTrace_5126548
  have hstable : (prefixWord ++ tailWord_5126548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126548).length < 2 ^ (prefixWord ++ tailWord_5126548).sum := by decide
  have hdescent : baseEnd_5126548 < baseStart_5126548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126584 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 1, 3, 5]
def baseStart_5126584 : Nat := 118140960795 + 5126584 * 2 ^ 59
def prefixEnd_5126584 : Nat := 4983230072969 + 3 ^ 40 * 5126584 * 2
def baseEnd_5126584 : Nat := 2632401707649275450223275

theorem tailTrace_5126584 : CollatzResearch.WordTrace tailWord_5126584 prefixEnd_5126584 2632401707649275450223275 := by
  unfold tailWord_5126584
  simp only [CollatzResearch.WordTrace]
  refine ⟨93490939829634596843073403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124654586439512795790764537 93490939829634596843073403)
  ·
    refine ⟨140236409744451895264610105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93490939829634596843073403 140236409744451895264610105)
    ·
      refine ⟨105177307308338921448457579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140236409744451895264610105 105177307308338921448457579)
      ·
        refine ⟨157765960962508382172686369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105177307308338921448457579 157765960962508382172686369)
        ·
          refine ⟨118324470721881286629514777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157765960962508382172686369 118324470721881286629514777)
          ·
            refine ⟨88743353041410964972136083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118324470721881286629514777 88743353041410964972136083)
            ·
              refine ⟨133115029562116447458204125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88743353041410964972136083 133115029562116447458204125)
              ·
                refine ⟨49918136085793667796826547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133115029562116447458204125 49918136085793667796826547)
                ·
                  refine ⟨74877204128690501695239821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49918136085793667796826547 74877204128690501695239821)
                  ·
                    refine ⟨28078951548258938135714933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74877204128690501695239821 28078951548258938135714933)
                    ·
                      refine ⟨2632401707649275450223275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28078951548258938135714933 2632401707649275450223275)
                      ·
                        rfl

theorem cell23_5126584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_5126584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126584 prefixEnd_5126584 := by exact prefixLift 5126584
  have htrace : WordTrace (prefixWord ++ tailWord_5126584) baseStart_5126584 baseEnd_5126584 := by
    simpa [prefixWord, tailWord_5126584, baseEnd_5126584] using wordTrace_append hprefix tailTrace_5126584
  have hstable : (prefixWord ++ tailWord_5126584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126584).length < 2 ^ (prefixWord ++ tailWord_5126584).sum := by decide
  have hdescent : baseEnd_5126584 < baseStart_5126584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126585 : List Nat := [1, 2, 1, 4, 3, 2, 1, 3, 1, 3, 2]
def baseStart_5126585 : Nat := 118140960795 + 5126585 * 2 ^ 59
def prefixEnd_5126585 : Nat := 4983230072969 + 3 ^ 40 * 5126585 * 2
def baseEnd_5126585 : Nat := 2632402221129929946310771

theorem tailTrace_5126585 : CollatzResearch.WordTrace tailWord_5126585 prefixEnd_5126585 2632402221129929946310771 := by
  unfold tailWord_5126585
  simp only [CollatzResearch.WordTrace]
  refine ⟨186981916132265570856933209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124654610754843713904622139 186981916132265570856933209)
  ·
    refine ⟨140236437099199178142699907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186981916132265570856933209 140236437099199178142699907)
    ·
      refine ⟨210354655648798767214049861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140236437099199178142699907 210354655648798767214049861)
      ·
        refine ⟨39441497934149768852634349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210354655648798767214049861 39441497934149768852634349)
        ·
          refine ⟨14790561725306163319737881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39441497934149768852634349 14790561725306163319737881)
          ·
            refine ⟨11092921293979622489803411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14790561725306163319737881 11092921293979622489803411)
            ·
              refine ⟨16639381940969433734705117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11092921293979622489803411 16639381940969433734705117)
              ·
                refine ⟨6239768227863537650514419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16639381940969433734705117 6239768227863537650514419)
                ·
                  refine ⟨9359652341795306475771629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6239768227863537650514419 9359652341795306475771629)
                  ·
                    refine ⟨3509869628173239928414361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9359652341795306475771629 3509869628173239928414361)
                    ·
                      refine ⟨2632402221129929946310771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3509869628173239928414361 2632402221129929946310771)
                      ·
                        rfl

theorem cell23_5126585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_5126585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126585 prefixEnd_5126585 := by exact prefixLift 5126585
  have htrace : WordTrace (prefixWord ++ tailWord_5126585) baseStart_5126585 baseEnd_5126585 := by
    simpa [prefixWord, tailWord_5126585, baseEnd_5126585] using wordTrace_append hprefix tailTrace_5126585
  have hstable : (prefixWord ++ tailWord_5126585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126585).length < 2 ^ (prefixWord ++ tailWord_5126585).sum := by decide
  have hdescent : baseEnd_5126585 < baseStart_5126585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126621 : List Nat := [1, 4, 3, 1, 1, 1, 1, 4, 7]
def baseStart_5126621 : Nat := 118140960795 + 5126621 * 2 ^ 59
def prefixEnd_5126621 : Nat := 4983230072969 + 3 ^ 40 * 5126621 * 2
def baseEnd_5126621 : Nat := 292491189603721311717845

theorem tailTrace_5126621 : CollatzResearch.WordTrace tailWord_5126621 prefixEnd_5126621 292491189603721311717845 := by
  unfold tailWord_5126621
  simp only [CollatzResearch.WordTrace]
  refine ⟨186983229160135149005243717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124655486106756766003495811 186983229160135149005243717)
  ·
    refine ⟨35059355467525340438483197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186983229160135149005243717 35059355467525340438483197)
    ·
      refine ⟨13147258300322002664431199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35059355467525340438483197 13147258300322002664431199)
      ·
        refine ⟨19720887450483003996646799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13147258300322002664431199 19720887450483003996646799)
        ·
          refine ⟨29581331175724505994970199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19720887450483003996646799 29581331175724505994970199)
          ·
            refine ⟨44371996763586758992455299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29581331175724505994970199 44371996763586758992455299)
            ·
              refine ⟨66557995145380138488682949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44371996763586758992455299 66557995145380138488682949)
              ·
                refine ⟨12479624089758775966628053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66557995145380138488682949 12479624089758775966628053)
                ·
                  refine ⟨292491189603721311717845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12479624089758775966628053 292491189603721311717845)
                  ·
                    rfl

theorem cell23_5126621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_5126621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126621 prefixEnd_5126621 := by exact prefixLift 5126621
  have htrace : WordTrace (prefixWord ++ tailWord_5126621) baseStart_5126621 baseEnd_5126621 := by
    simpa [prefixWord, tailWord_5126621, baseEnd_5126621] using wordTrace_append hprefix tailTrace_5126621
  have hstable : (prefixWord ++ tailWord_5126621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126621).length < 2 ^ (prefixWord ++ tailWord_5126621).sum := by decide
  have hdescent : baseEnd_5126621 < baseStart_5126621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126795 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 5, 2, 2]
def baseStart_5126795 : Nat := 118140960795 + 5126795 * 2 ^ 59
def prefixEnd_5126795 : Nat := 4983230072969 + 3 ^ 40 * 5126795 * 2
def baseEnd_5126795 : Nat := 2632510052067374124684805

theorem tailTrace_5126795 : CollatzResearch.WordTrace tailWord_5126795 prefixEnd_5126795 2632510052067374124684805 := by
  unfold tailWord_5126795
  simp only [CollatzResearch.WordTrace]
  refine ⟨186989575461504776722077839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124659716974336517814718559 186989575461504776722077839)
  ·
    refine ⟨280484363192257165083116759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186989575461504776722077839 280484363192257165083116759)
    ·
      refine ⟨420726544788385747624675139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280484363192257165083116759 420726544788385747624675139)
      ·
        refine ⟨631089817182578621437012709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420726544788385747624675139 631089817182578621437012709)
        ·
          refine ⟨118329340721733491519439883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 631089817182578621437012709 118329340721733491519439883)
          ·
            refine ⟨177494011082600237279159825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118329340721733491519439883 177494011082600237279159825)
            ·
              refine ⟨133120508311950177959369869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177494011082600237279159825 133120508311950177959369869)
              ·
                refine ⟨49920190616981316734763701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133120508311950177959369869 49920190616981316734763701)
                ·
                  refine ⟨4680017870341998443884097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49920190616981316734763701 4680017870341998443884097)
                  ·
                    refine ⟨3510013402756498832913073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4680017870341998443884097 3510013402756498832913073)
                    ·
                      refine ⟨2632510052067374124684805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3510013402756498832913073 2632510052067374124684805)
                      ·
                        rfl

theorem cell23_5126795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 2, 2].length) (baseStart_5126795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126795 prefixEnd_5126795 := by exact prefixLift 5126795
  have htrace : WordTrace (prefixWord ++ tailWord_5126795) baseStart_5126795 baseEnd_5126795 := by
    simpa [prefixWord, tailWord_5126795, baseEnd_5126795] using wordTrace_append hprefix tailTrace_5126795
  have hstable : (prefixWord ++ tailWord_5126795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126795).length < 2 ^ (prefixWord ++ tailWord_5126795).sum := by decide
  have hdescent : baseEnd_5126795 < baseStart_5126795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126798 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_5126798 : Nat := 118140960795 + 5126798 * 2 ^ 59
def prefixEnd_5126798 : Nat := 4983230072969 + 3 ^ 40 * 5126798 * 2
def baseEnd_5126798 : Nat := 2632511592509337612947291

theorem tailTrace_5126798 : CollatzResearch.WordTrace tailWord_5126798 prefixEnd_5126798 2632511592509337612947291 := by
  unfold tailWord_5126798
  simp only [CollatzResearch.WordTrace]
  refine ⟨23373710610061738529304631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124659789920329272156291365 23373710610061738529304631)
  ·
    refine ⟨35060565915092607793956947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23373710610061738529304631 35060565915092607793956947)
    ·
      refine ⟨52590848872638911690935421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35060565915092607793956947 52590848872638911690935421)
      ·
        refine ⟨19721568327239591884100783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52590848872638911690935421 19721568327239591884100783)
        ·
          refine ⟨29582352490859387826151175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19721568327239591884100783 29582352490859387826151175)
          ·
            refine ⟨44373528736289081739226763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29582352490859387826151175 44373528736289081739226763)
            ·
              refine ⟨66560293104433622608840145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44373528736289081739226763 66560293104433622608840145)
              ·
                refine ⟨49920219828325216956630109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66560293104433622608840145 49920219828325216956630109)
                ·
                  refine ⟨18720082435621956358736291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49920219828325216956630109 18720082435621956358736291)
                  ·
                    refine ⟨28080123653432934538104437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18720082435621956358736291 28080123653432934538104437)
                    ·
                      refine ⟨2632511592509337612947291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28080123653432934538104437 2632511592509337612947291)
                      ·
                        rfl

theorem cell23_5126798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_5126798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126798 prefixEnd_5126798 := by exact prefixLift 5126798
  have htrace : WordTrace (prefixWord ++ tailWord_5126798) baseStart_5126798 baseEnd_5126798 := by
    simpa [prefixWord, tailWord_5126798, baseEnd_5126798] using wordTrace_append hprefix tailTrace_5126798
  have hstable : (prefixWord ++ tailWord_5126798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126798).length < 2 ^ (prefixWord ++ tailWord_5126798).sum := by decide
  have hdescent : baseEnd_5126798 < baseStart_5126798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126808 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 3, 2, 4]
def baseStart_5126808 : Nat := 118140960795 + 5126808 * 2 ^ 59
def prefixEnd_5126808 : Nat := 4983230072969 + 3 ^ 40 * 5126808 * 2
def baseEnd_5126808 : Nat := 2632516727315882573822245

theorem tailTrace_5126808 : CollatzResearch.WordTrace tailWord_5126808 prefixEnd_5126808 2632516727315882573822245 := by
  unfold tailWord_5126808
  simp only [CollatzResearch.WordTrace]
  refine ⟨93495024805228839971150539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124660033073638453294867385 93495024805228839971150539)
  ·
    refine ⟨140242537207843259956725809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93495024805228839971150539 140242537207843259956725809)
    ·
      refine ⟨105181902905882444967544357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140242537207843259956725809 105181902905882444967544357)
      ·
        refine ⟨19721606794852958431414567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105181902905882444967544357 19721606794852958431414567)
        ·
          refine ⟨29582410192279437647121851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19721606794852958431414567 29582410192279437647121851)
          ·
            refine ⟨44373615288419156470682777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29582410192279437647121851 44373615288419156470682777)
            ·
              refine ⟨33280211466314367353012083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44373615288419156470682777 33280211466314367353012083)
              ·
                refine ⟨49920317199471551029518125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33280211466314367353012083 49920317199471551029518125)
                ·
                  refine ⟨18720118949801831636069297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49920317199471551029518125 18720118949801831636069297)
                  ·
                    refine ⟨14040089212351373727051973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18720118949801831636069297 14040089212351373727051973)
                    ·
                      refine ⟨2632516727315882573822245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14040089212351373727051973 2632516727315882573822245)
                      ·
                        rfl

theorem cell23_5126808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_5126808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126808 prefixEnd_5126808 := by exact prefixLift 5126808
  have htrace : WordTrace (prefixWord ++ tailWord_5126808) baseStart_5126808 baseEnd_5126808 := by
    simpa [prefixWord, tailWord_5126808, baseEnd_5126808] using wordTrace_append hprefix tailTrace_5126808
  have hstable : (prefixWord ++ tailWord_5126808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126808).length < 2 ^ (prefixWord ++ tailWord_5126808).sum := by decide
  have hdescent : baseEnd_5126808 < baseStart_5126808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126823 : List Nat := [1, 1, 6, 3, 1, 1, 3, 2, 1, 1, 3]
def baseStart_5126823 : Nat := 118140960795 + 5126823 * 2 ^ 59
def prefixEnd_5126823 : Nat := 4983230072969 + 3 ^ 40 * 5126823 * 2
def baseEnd_5126823 : Nat := 2632524429525700015134677

theorem tailTrace_5126823 : CollatzResearch.WordTrace tailWord_5126823 prefixEnd_5126823 2632524429525700015134677 := by
  unfold tailWord_5126823
  simp only [CollatzResearch.WordTrace]
  refine ⟨186990596705403337504097123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124660397803602225002731415 186990596705403337504097123)
  ·
    refine ⟨280485895058105006256145685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186990596705403337504097123 280485895058105006256145685)
    ·
      refine ⟨13147776330848672168256829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 280485895058105006256145685 13147776330848672168256829)
      ·
        refine ⟨4930416124068252063096311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13147776330848672168256829 4930416124068252063096311)
        ·
          refine ⟨7395624186102378094644467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4930416124068252063096311 7395624186102378094644467)
          ·
            refine ⟨11093436279153567141966701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7395624186102378094644467 11093436279153567141966701)
            ·
              refine ⟨4160038604682587678237513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11093436279153567141966701 4160038604682587678237513)
              ·
                refine ⟨3120028953511940758678135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4160038604682587678237513 3120028953511940758678135)
                ·
                  refine ⟨4680043430267911138017203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3120028953511940758678135 4680043430267911138017203)
                  ·
                    refine ⟨7020065145401866707025805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4680043430267911138017203 7020065145401866707025805)
                    ·
                      refine ⟨2632524429525700015134677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7020065145401866707025805 2632524429525700015134677)
                      ·
                        rfl

theorem cell23_5126823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_5126823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126823 prefixEnd_5126823 := by exact prefixLift 5126823
  have htrace : WordTrace (prefixWord ++ tailWord_5126823) baseStart_5126823 baseEnd_5126823 := by
    simpa [prefixWord, tailWord_5126823, baseEnd_5126823] using wordTrace_append hprefix tailTrace_5126823
  have hstable : (prefixWord ++ tailWord_5126823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126823).length < 2 ^ (prefixWord ++ tailWord_5126823).sum := by decide
  have hdescent : baseEnd_5126823 < baseStart_5126823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126829 : List Nat := [1, 5, 2, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_5126829 : Nat := 118140960795 + 5126829 * 2 ^ 59
def prefixEnd_5126829 : Nat := 4983230072969 + 3 ^ 40 * 5126829 * 2
def baseEnd_5126829 : Nat := 2632527510409626991659649

theorem tailTrace_5126829 : CollatzResearch.WordTrace tailWord_5126829 prefixEnd_5126829 2632527510409626991659649 := by
  unfold tailWord_5126829
  simp only [CollatzResearch.WordTrace]
  refine ⟨186990815543381600528815541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124660543695587733685877027 186990815543381600528815541)
  ·
    refine ⟨17530388957192025049576457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 186990815543381600528815541 17530388957192025049576457)
    ·
      refine ⟨13147791717894018787182343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17530388957192025049576457 13147791717894018787182343)
      ·
        refine ⟨19721687576841028180773515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13147791717894018787182343 19721687576841028180773515)
        ·
          refine ⟨29582531365261542271160273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19721687576841028180773515 29582531365261542271160273)
          ·
            refine ⟨22186898523946156703370205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29582531365261542271160273 22186898523946156703370205)
            ·
              refine ⟨8320086946479808763763827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22186898523946156703370205 8320086946479808763763827)
              ·
                refine ⟨12480130419719713145645741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8320086946479808763763827 12480130419719713145645741)
                ·
                  refine ⟨4680048907394892429617153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12480130419719713145645741 4680048907394892429617153)
                  ·
                    refine ⟨3510036680546169322212865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4680048907394892429617153 3510036680546169322212865)
                    ·
                      refine ⟨2632527510409626991659649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3510036680546169322212865 2632527510409626991659649)
                      ·
                        rfl

theorem cell23_5126829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_5126829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126829 prefixEnd_5126829 := by exact prefixLift 5126829
  have htrace : WordTrace (prefixWord ++ tailWord_5126829) baseStart_5126829 baseEnd_5126829 := by
    simpa [prefixWord, tailWord_5126829, baseEnd_5126829] using wordTrace_append hprefix tailTrace_5126829
  have hstable : (prefixWord ++ tailWord_5126829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126829).length < 2 ^ (prefixWord ++ tailWord_5126829).sum := by decide
  have hdescent : baseEnd_5126829 < baseStart_5126829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126839 : List Nat := [1, 1, 3, 1, 6, 2, 2, 1, 2, 4]
def baseStart_5126839 : Nat := 118140960795 + 5126839 * 2 ^ 59
def prefixEnd_5126839 : Nat := 4983230072969 + 3 ^ 40 * 5126839 * 2
def baseEnd_5126839 : Nat := 877510881738723984178201

theorem tailTrace_5126839 : CollatzResearch.WordTrace tailWord_5126839 prefixEnd_5126839 877510881738723984178201 := by
  unfold tailWord_5126839
  simp only [CollatzResearch.WordTrace]
  refine ⟨186991180273345372236679571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124660786848896914824453047 186991180273345372236679571)
  ·
    refine ⟨280486770410018058355019357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186991180273345372236679571 280486770410018058355019357)
    ·
      refine ⟨105182538903756771883132259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280486770410018058355019357 105182538903756771883132259)
      ·
        refine ⟨157773808355635157824698389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105182538903756771883132259 157773808355635157824698389)
        ·
          refine ⟨7395647266670398023032737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 157773808355635157824698389 7395647266670398023032737)
          ·
            refine ⟨5546735450002798517274553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7395647266670398023032737 5546735450002798517274553)
            ·
              refine ⟨4160051587502098887955915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5546735450002798517274553 4160051587502098887955915)
              ·
                refine ⟨6240077381253148331933873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4160051587502098887955915 6240077381253148331933873)
                ·
                  refine ⟨4680058035939861248950405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6240077381253148331933873 4680058035939861248950405)
                  ·
                    refine ⟨877510881738723984178201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4680058035939861248950405 877510881738723984178201)
                    ·
                      rfl

theorem cell23_5126839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 2, 4].length) (baseStart_5126839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126839 prefixEnd_5126839 := by exact prefixLift 5126839
  have htrace : WordTrace (prefixWord ++ tailWord_5126839) baseStart_5126839 baseEnd_5126839 := by
    simpa [prefixWord, tailWord_5126839, baseEnd_5126839] using wordTrace_append hprefix tailTrace_5126839
  have hstable : (prefixWord ++ tailWord_5126839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126839).length < 2 ^ (prefixWord ++ tailWord_5126839).sum := by decide
  have hdescent : baseEnd_5126839 < baseStart_5126839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126849 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_5126849 : Nat := 118140960795 + 5126849 * 2 ^ 59
def prefixEnd_5126849 : Nat := 4983230072969 + 3 ^ 40 * 5126849 * 2
def baseEnd_5126849 : Nat := 2632537780022716913409557

theorem tailTrace_5126849 : CollatzResearch.WordTrace tailWord_5126849 prefixEnd_5126849 2632537780022716913409557 := by
  unfold tailWord_5126849
  simp only [CollatzResearch.WordTrace]
  refine ⟨186991545003309143944543601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124661030002206095963029067 186991545003309143944543601)
  ·
    refine ⟨140243658752481857958407701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186991545003309143944543601 140243658752481857958407701)
    ·
      refine ⟨6573921504022587091800361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 140243658752481857958407701 6573921504022587091800361)
      ·
        refine ⟨4930441128016940318850271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6573921504022587091800361 4930441128016940318850271)
        ·
          refine ⟨7395661692025410478275407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4930441128016940318850271 7395661692025410478275407)
          ·
            refine ⟨11093492538038115717413111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7395661692025410478275407 11093492538038115717413111)
            ·
              refine ⟨16640238807057173576119667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11093492538038115717413111 16640238807057173576119667)
              ·
                refine ⟨24960358210585760364179501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16640238807057173576119667 24960358210585760364179501)
                ·
                  refine ⟨9360134328969660136567313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24960358210585760364179501 9360134328969660136567313)
                  ·
                    refine ⟨7020100746727245102425485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9360134328969660136567313 7020100746727245102425485)
                    ·
                      refine ⟨2632537780022716913409557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7020100746727245102425485 2632537780022716913409557)
                      ·
                        rfl

theorem cell23_5126849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_5126849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126849 prefixEnd_5126849 := by exact prefixLift 5126849
  have htrace : WordTrace (prefixWord ++ tailWord_5126849) baseStart_5126849 baseEnd_5126849 := by
    simpa [prefixWord, tailWord_5126849, baseEnd_5126849] using wordTrace_append hprefix tailTrace_5126849
  have hstable : (prefixWord ++ tailWord_5126849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126849).length < 2 ^ (prefixWord ++ tailWord_5126849).sum := by decide
  have hdescent : baseEnd_5126849 < baseStart_5126849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126908 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 9]
def baseStart_5126908 : Nat := 118140960795 + 5126908 * 2 ^ 59
def prefixEnd_5126908 : Nat := 4983230072969 + 3 ^ 40 * 5126908 * 2
def baseEnd_5126908 : Nat := 292507563931259131396865

theorem tailTrace_5126908 : CollatzResearch.WordTrace tailWord_5126908 prefixEnd_5126908 292507563931259131396865 := by
  unfold tailWord_5126908
  simp only [CollatzResearch.WordTrace]
  refine ⟨93496848455047698510470689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124662464606730264680627585 93496848455047698510470689)
  ·
    refine ⟨70122636341285773882853017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93496848455047698510470689 70122636341285773882853017)
    ·
      refine ⟨52591977255964330412139763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70122636341285773882853017 52591977255964330412139763)
      ·
        refine ⟨78887965883946495618209645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52591977255964330412139763 78887965883946495618209645)
        ·
          refine ⟨29582987206479935856828617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78887965883946495618209645 29582987206479935856828617)
          ·
            refine ⟨22187240404859951892621463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29582987206479935856828617 22187240404859951892621463)
            ·
              refine ⟨33280860607289927838932195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22187240404859951892621463 33280860607289927838932195)
              ·
                refine ⟨49921290910934891758398293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33280860607289927838932195 49921290910934891758398293)
                ·
                  refine ⟨292507563931259131396865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49921290910934891758398293 292507563931259131396865)
                  ·
                    rfl

theorem cell23_5126908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 9].length) (baseStart_5126908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126908 prefixEnd_5126908 := by exact prefixLift 5126908
  have htrace : WordTrace (prefixWord ++ tailWord_5126908) baseStart_5126908 baseEnd_5126908 := by
    simpa [prefixWord, tailWord_5126908, baseEnd_5126908] using wordTrace_append hprefix tailTrace_5126908
  have hstable : (prefixWord ++ tailWord_5126908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126908).length < 2 ^ (prefixWord ++ tailWord_5126908).sum := by decide
  have hdescent : baseEnd_5126908 < baseStart_5126908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126968 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 2, 8]
def baseStart_5126968 : Nat := 118140960795 + 5126968 * 2 ^ 59
def prefixEnd_5126968 : Nat := 4983230072969 + 3 ^ 40 * 5126968 * 2
def baseEnd_5126968 : Nat := 877532961406867315940503

theorem tailTrace_5126968 : CollatzResearch.WordTrace tailWord_5126968 prefixEnd_5126968 877532961406867315940503 := by
  unfold tailWord_5126968
  simp only [CollatzResearch.WordTrace]
  refine ⟨93497942644939013634062779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124663923526585351512083705 93497942644939013634062779)
  ·
    refine ⟨140246913967408520451094169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93497942644939013634062779 140246913967408520451094169)
    ·
      refine ⟨105185185475556390338320627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140246913967408520451094169 105185185475556390338320627)
      ·
        refine ⟨157777778213334585507480941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105185185475556390338320627 157777778213334585507480941)
        ·
          refine ⟨59166666830000469565305353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157777778213334585507480941 59166666830000469565305353)
          ·
            refine ⟨44375000122500352173979015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59166666830000469565305353 44375000122500352173979015)
            ·
              refine ⟨66562500183750528260968523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44375000122500352173979015 66562500183750528260968523)
              ·
                refine ⟨99843750275625792391452785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66562500183750528260968523 99843750275625792391452785)
                ·
                  refine ⟨74882812706719344293589589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99843750275625792391452785 74882812706719344293589589)
                  ·
                    refine ⟨877532961406867315940503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74882812706719344293589589 877532961406867315940503)
                    ·
                      rfl

theorem cell23_5126968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_5126968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126968 prefixEnd_5126968 := by exact prefixLift 5126968
  have htrace : WordTrace (prefixWord ++ tailWord_5126968) baseStart_5126968 baseEnd_5126968 := by
    simpa [prefixWord, tailWord_5126968, baseEnd_5126968] using wordTrace_append hprefix tailTrace_5126968
  have hstable : (prefixWord ++ tailWord_5126968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126968).length < 2 ^ (prefixWord ++ tailWord_5126968).sum := by decide
  have hdescent : baseEnd_5126968 < baseStart_5126968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126975 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 4]
def baseStart_5126975 : Nat := 118140960795 + 5126975 * 2 ^ 59
def prefixEnd_5126975 : Nat := 4983230072969 + 3 ^ 40 * 5126975 * 2
def baseEnd_5126975 : Nat := 2632602478585183420433977

theorem tailTrace_5126975 : CollatzResearch.WordTrace tailWord_5126975 prefixEnd_5126975 2632602478585183420433977 := by
  unfold tailWord_5126975
  simp only [CollatzResearch.WordTrace]
  refine ⟨186996140600852667463630379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124664093733901778309086919 186996140600852667463630379)
  ·
    refine ⟨280494210901279001195445569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186996140600852667463630379 280494210901279001195445569)
    ·
      refine ⟨210370658175959250896584177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280494210901279001195445569 210370658175959250896584177)
      ·
        refine ⟨157777993631969438172438133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210370658175959250896584177 157777993631969438172438133)
        ·
          refine ⟨14791686902997134828666075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157777993631969438172438133 14791686902997134828666075)
          ·
            refine ⟨22187530354495702242999113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14791686902997134828666075 22187530354495702242999113)
            ·
              refine ⟨16640647765871776682249335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22187530354495702242999113 16640647765871776682249335)
              ·
                refine ⟨24960971648807665023374003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16640647765871776682249335 24960971648807665023374003)
                ·
                  refine ⟨37441457473211497535061005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24960971648807665023374003 37441457473211497535061005)
                  ·
                    refine ⟨14040546552454311575647877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37441457473211497535061005 14040546552454311575647877)
                    ·
                      refine ⟨2632602478585183420433977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14040546552454311575647877 2632602478585183420433977)
                      ·
                        rfl

theorem cell23_5126975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_5126975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126975 prefixEnd_5126975 := by exact prefixLift 5126975
  have htrace : WordTrace (prefixWord ++ tailWord_5126975) baseStart_5126975 baseEnd_5126975 := by
    simpa [prefixWord, tailWord_5126975, baseEnd_5126975] using wordTrace_append hprefix tailTrace_5126975
  have hstable : (prefixWord ++ tailWord_5126975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126975).length < 2 ^ (prefixWord ++ tailWord_5126975).sum := by decide
  have hdescent : baseEnd_5126975 < baseStart_5126975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5126989 : List Nat := [1, 6, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_5126989 : Nat := 118140960795 + 5126989 * 2 ^ 59
def prefixEnd_5126989 : Nat := 4983230072969 + 3 ^ 40 * 5126989 * 2
def baseEnd_5126989 : Nat := 877536555771448788552971

theorem tailTrace_5126989 : CollatzResearch.WordTrace tailWord_5126989 prefixEnd_5126989 877536555771448788552971 := by
  unfold tailWord_5126989
  simp only [CollatzResearch.WordTrace]
  refine ⟨186996651222801947854640021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124664434148534631903093347 186996651222801947854640021)
  ·
    refine ⟨8765468026068841305686251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 186996651222801947854640021 8765468026068841305686251)
    ·
      refine ⟨13148202039103261958529377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8765468026068841305686251 13148202039103261958529377)
      ·
        refine ⟨9861151529327446468897033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13148202039103261958529377 9861151529327446468897033)
        ·
          refine ⟨7395863646995584851672775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9861151529327446468897033 7395863646995584851672775)
          ·
            refine ⟨11093795470493377277509163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7395863646995584851672775 11093795470493377277509163)
            ·
              refine ⟨16640693205740065916263745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11093795470493377277509163 16640693205740065916263745)
              ·
                refine ⟨12480519904305049437197809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16640693205740065916263745 12480519904305049437197809)
                ·
                  refine ⟨9360389928228787077898357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12480519904305049437197809 9360389928228787077898357)
                  ·
                    refine ⟨877536555771448788552971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9360389928228787077898357 877536555771448788552971)
                    ·
                      rfl

theorem cell23_5126989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_5126989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5126989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5126989 prefixEnd_5126989 := by exact prefixLift 5126989
  have htrace : WordTrace (prefixWord ++ tailWord_5126989) baseStart_5126989 baseEnd_5126989 := by
    simpa [prefixWord, tailWord_5126989, baseEnd_5126989] using wordTrace_append hprefix tailTrace_5126989
  have hstable : (prefixWord ++ tailWord_5126989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5126989).length < 2 ^ (prefixWord ++ tailWord_5126989).sum := by decide
  have hdescent : baseEnd_5126989 < baseStart_5126989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5126989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127002 : List Nat := [3, 1, 1, 2, 1, 4, 3, 1, 3, 4]
def baseStart_5127002 : Nat := 118140960795 + 5127002 * 2 ^ 59
def prefixEnd_5127002 : Nat := 4983230072969 + 3 ^ 40 * 5127002 * 2
def baseEnd_5127002 : Nat := 877538780854284938265451

theorem tailTrace_5127002 : CollatzResearch.WordTrace tailWord_5127002 prefixEnd_5127002 877538780854284938265451 := by
  unfold tailWord_5127002
  simp only [CollatzResearch.WordTrace]
  refine ⟨46749281342938712768715815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124664750247836567383242173 46749281342938712768715815)
  ·
    refine ⟨70123922014408069153073723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46749281342938712768715815 70123922014408069153073723)
    ·
      refine ⟨105185883021612103729610585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70123922014408069153073723 105185883021612103729610585)
      ·
        refine ⟨78889412266209077797207939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105185883021612103729610585 78889412266209077797207939)
        ·
          refine ⟨118334118399313616695811909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78889412266209077797207939 118334118399313616695811909)
          ·
            refine ⟨22187647199871303130464733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118334118399313616695811909 22187647199871303130464733)
            ·
              refine ⟨8320367699951738673924275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22187647199871303130464733 8320367699951738673924275)
              ·
                refine ⟨12480551549927608010886413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8320367699951738673924275 12480551549927608010886413)
                ·
                  refine ⟨4680206831222853004082405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12480551549927608010886413 4680206831222853004082405)
                  ·
                    refine ⟨877538780854284938265451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4680206831222853004082405 877538780854284938265451)
                    ·
                      rfl

theorem cell23_5127002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 3, 4].length) (baseStart_5127002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127002 prefixEnd_5127002 := by exact prefixLift 5127002
  have htrace : WordTrace (prefixWord ++ tailWord_5127002) baseStart_5127002 baseEnd_5127002 := by
    simpa [prefixWord, tailWord_5127002, baseEnd_5127002] using wordTrace_append hprefix tailTrace_5127002
  have hstable : (prefixWord ++ tailWord_5127002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127002).length < 2 ^ (prefixWord ++ tailWord_5127002).sum := by decide
  have hdescent : baseEnd_5127002 < baseStart_5127002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127029 : List Nat := [1, 3, 4, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_5127029 : Nat := 118140960795 + 5127029 * 2 ^ 59
def prefixEnd_5127029 : Nat := 4983230072969 + 3 ^ 40 * 5127029 * 2
def baseEnd_5127029 : Nat := 2632630206540526209158729

theorem tailTrace_5127029 : CollatzResearch.WordTrace tailWord_5127029 prefixEnd_5127029 2632630206540526209158729 := by
  unfold tailWord_5127029
  simp only [CollatzResearch.WordTrace]
  refine ⟨186998110142657034686096141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124665406761771356457397427 186998110142657034686096141)
  ·
    refine ⟨70124291303496388007286053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186998110142657034686096141 70124291303496388007286053)
    ·
      refine ⟨13148304619405572751366135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70124291303496388007286053 13148304619405572751366135)
      ·
        refine ⟨19722456929108359127049203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13148304619405572751366135 19722456929108359127049203)
        ·
          refine ⟨29583685393662538690573805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19722456929108359127049203 29583685393662538690573805)
          ·
            refine ⟨11093882022623452008965177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29583685393662538690573805 11093882022623452008965177)
            ·
              refine ⟨8320411516967589006723883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11093882022623452008965177 8320411516967589006723883)
              ·
                refine ⟨12480617275451383510085825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8320411516967589006723883 12480617275451383510085825)
                ·
                  refine ⟨9360462956588537632564369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12480617275451383510085825 9360462956588537632564369)
                  ·
                    refine ⟨7020347217441403224423277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9360462956588537632564369 7020347217441403224423277)
                    ·
                      refine ⟨2632630206540526209158729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7020347217441403224423277 2632630206540526209158729)
                      ·
                        rfl

theorem cell23_5127029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_5127029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127029 prefixEnd_5127029 := by exact prefixLift 5127029
  have htrace : WordTrace (prefixWord ++ tailWord_5127029) baseStart_5127029 baseEnd_5127029 := by
    simpa [prefixWord, tailWord_5127029, baseEnd_5127029] using wordTrace_append hprefix tailTrace_5127029
  have hstable : (prefixWord ++ tailWord_5127029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127029).length < 2 ^ (prefixWord ++ tailWord_5127029).sum := by decide
  have hdescent : baseEnd_5127029 < baseStart_5127029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127075 : List Nat := [1, 1, 1, 4, 1, 2, 3, 3, 1, 6]
def baseStart_5127075 : Nat := 118140960795 + 5127075 * 2 ^ 59
def prefixEnd_5127075 : Nat := 4983230072969 + 3 ^ 40 * 5127075 * 2
def baseEnd_5127075 : Nat := 877551275550211009727839

theorem tailTrace_5127075 : CollatzResearch.WordTrace tailWord_5127075 prefixEnd_5127075 877551275550211009727839 := by
  unfold tailWord_5127075
  simp only [CollatzResearch.WordTrace]
  refine ⟨186999787900490384542270679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124666525266993589694847119 186999787900490384542270679)
  ·
    refine ⟨280499681850735576813406019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186999787900490384542270679 280499681850735576813406019)
    ·
      refine ⟨420749522776103365220109029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280499681850735576813406019 420749522776103365220109029)
      ·
        refine ⟨78890535520519380978770443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 420749522776103365220109029 78890535520519380978770443)
        ·
          refine ⟨118335803280779071468155665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78890535520519380978770443 118335803280779071468155665)
          ·
            refine ⟨88751852460584303601116749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118335803280779071468155665 88751852460584303601116749)
            ·
              refine ⟨33281944672719113850418781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88751852460584303601116749 33281944672719113850418781)
              ·
                refine ⟨12480729252269667693907043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33281944672719113850418781 12480729252269667693907043)
                ·
                  refine ⟨18721093878404501540860565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12480729252269667693907043 18721093878404501540860565)
                  ·
                    refine ⟨877551275550211009727839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18721093878404501540860565 877551275550211009727839)
                    ·
                      rfl

theorem cell23_5127075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 6].length) (baseStart_5127075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127075 prefixEnd_5127075 := by exact prefixLift 5127075
  have htrace : WordTrace (prefixWord ++ tailWord_5127075) baseStart_5127075 baseEnd_5127075 := by
    simpa [prefixWord, tailWord_5127075, baseEnd_5127075] using wordTrace_append hprefix tailTrace_5127075
  have hstable : (prefixWord ++ tailWord_5127075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127075).length < 2 ^ (prefixWord ++ tailWord_5127075).sum := by decide
  have hdescent : baseEnd_5127075 < baseStart_5127075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127102 : List Nat := [4, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_5127102 : Nat := 118140960795 + 5127102 * 2 ^ 59
def prefixEnd_5127102 : Nat := 4983230072969 + 3 ^ 40 * 5127102 * 2
def baseEnd_5127102 : Nat := 2632667690628304423545893

theorem tailTrace_5127102 : CollatzResearch.WordTrace tailWord_5127102 prefixEnd_5127102 2632667690628304423545893 := by
  unfold tailWord_5127102
  simp only [CollatzResearch.WordTrace]
  refine ⟨23375096583924071019187945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124667181780928378769002373 23375096583924071019187945)
  ·
    refine ⟨17531322437943053264390959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23375096583924071019187945 17531322437943053264390959)
    ·
      refine ⟨26296983656914579896586439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17531322437943053264390959 26296983656914579896586439)
      ·
        refine ⟨39445475485371869844879659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26296983656914579896586439 39445475485371869844879659)
        ·
          refine ⟨59168213228057804767319489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39445475485371869844879659 59168213228057804767319489)
          ·
            refine ⟨44376159921043353575489617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59168213228057804767319489 44376159921043353575489617)
            ·
              refine ⟨33282119940782515181617213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44376159921043353575489617 33282119940782515181617213)
              ·
                refine ⟨12480794977793443193106455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33282119940782515181617213 12480794977793443193106455)
                ·
                  refine ⟨18721192466690164789659683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12480794977793443193106455 18721192466690164789659683)
                  ·
                    refine ⟨28081788700035247184489525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18721192466690164789659683 28081788700035247184489525)
                    ·
                      refine ⟨2632667690628304423545893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28081788700035247184489525 2632667690628304423545893)
                      ·
                        rfl

theorem cell23_5127102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_5127102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127102 prefixEnd_5127102 := by exact prefixLift 5127102
  have htrace : WordTrace (prefixWord ++ tailWord_5127102) baseStart_5127102 baseEnd_5127102 := by
    simpa [prefixWord, tailWord_5127102, baseEnd_5127102] using wordTrace_append hprefix tailTrace_5127102
  have hstable : (prefixWord ++ tailWord_5127102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127102).length < 2 ^ (prefixWord ++ tailWord_5127102).sum := by decide
  have hdescent : baseEnd_5127102 < baseStart_5127102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127116 : List Nat := [2, 2, 1, 4, 1, 1, 4, 1, 3, 2, 2]
def baseStart_5127116 : Nat := 118140960795 + 5127116 * 2 ^ 59
def prefixEnd_5127116 : Nat := 4983230072969 + 3 ^ 40 * 5127116 * 2
def baseEnd_5127116 : Nat := 2632674879357467368770829

theorem tailTrace_5127116 : CollatzResearch.WordTrace tailWord_5127116 prefixEnd_5127116 2632674879357467368770829 := by
  unfold tailWord_5127116
  simp only [CollatzResearch.WordTrace]
  refine ⟨93500641646670924272256601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124667522195561232363008801 93500641646670924272256601)
  ·
    refine ⟨70125481235003193204192451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93500641646670924272256601 70125481235003193204192451)
    ·
      refine ⟨105188221852504789806288677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70125481235003193204192451 105188221852504789806288677)
      ·
        refine ⟨19722791597344648088679127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105188221852504789806288677 19722791597344648088679127)
        ·
          refine ⟨29584187396016972133018691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19722791597344648088679127 29584187396016972133018691)
          ·
            refine ⟨44376281094025458199528037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29584187396016972133018691 44376281094025458199528037)
            ·
              refine ⟨8320552705129773412411507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44376281094025458199528037 8320552705129773412411507)
              ·
                refine ⟨12480829057694660118617261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8320552705129773412411507 12480829057694660118617261)
                ·
                  refine ⟨4680310896635497544481473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12480829057694660118617261 4680310896635497544481473)
                  ·
                    refine ⟨3510233172476623158361105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4680310896635497544481473 3510233172476623158361105)
                    ·
                      refine ⟨2632674879357467368770829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3510233172476623158361105 2632674879357467368770829)
                      ·
                        rfl

theorem cell23_5127116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_5127116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127116 prefixEnd_5127116 := by exact prefixLift 5127116
  have htrace : WordTrace (prefixWord ++ tailWord_5127116) baseStart_5127116 baseEnd_5127116 := by
    simpa [prefixWord, tailWord_5127116, baseEnd_5127116] using wordTrace_append hprefix tailTrace_5127116
  have hstable : (prefixWord ++ tailWord_5127116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127116).length < 2 ^ (prefixWord ++ tailWord_5127116).sum := by decide
  have hdescent : baseEnd_5127116 < baseStart_5127116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127126 : List Nat := [5, 2, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_5127126 : Nat := 118140960795 + 5127126 * 2 ^ 59
def prefixEnd_5127126 : Nat := 4983230072969 + 3 ^ 40 * 5127126 * 2
def baseEnd_5127126 : Nat := 877560004721337443215261

theorem tailTrace_5127126 : CollatzResearch.WordTrace tailWord_5127126 prefixEnd_5127126 877560004721337443215261 := by
  unfold tailWord_5127126
  simp only [CollatzResearch.WordTrace]
  refine ⟨11687603001456601265773577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124667765348870413501584821 11687603001456601265773577)
  ·
    refine ⟨8765702251092450949330183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11687603001456601265773577 8765702251092450949330183)
    ·
      refine ⟨13148553376638676423995275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8765702251092450949330183 13148553376638676423995275)
      ·
        refine ⟨19722830064958014635992913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13148553376638676423995275 19722830064958014635992913)
        ·
          refine ⟨14792122548718510976994685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19722830064958014635992913 14792122548718510976994685)
          ·
            refine ⟨5547045955769441616373007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14792122548718510976994685 5547045955769441616373007)
            ·
              refine ⟨8320568933654162424559511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5547045955769441616373007 8320568933654162424559511)
              ·
                refine ⟨12480853400481243636839267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8320568933654162424559511 12480853400481243636839267)
                ·
                  refine ⟨18721280100721865455258901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12480853400481243636839267 18721280100721865455258901)
                  ·
                    refine ⟨877560004721337443215261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18721280100721865455258901 877560004721337443215261)
                    ·
                      rfl

theorem cell23_5127126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_5127126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127126 prefixEnd_5127126 := by exact prefixLift 5127126
  have htrace : WordTrace (prefixWord ++ tailWord_5127126) baseStart_5127126 baseEnd_5127126 := by
    simpa [prefixWord, tailWord_5127126, baseEnd_5127126] using wordTrace_append hprefix tailTrace_5127126
  have hstable : (prefixWord ++ tailWord_5127126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127126).length < 2 ^ (prefixWord ++ tailWord_5127126).sum := by decide
  have hdescent : baseEnd_5127126 < baseStart_5127126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127129 : List Nat := [1, 2, 1, 2, 5, 3, 1, 1, 1, 2, 4]
def baseStart_5127129 : Nat := 118140960795 + 5127129 * 2 ^ 59
def prefixEnd_5127129 : Nat := 4983230072969 + 3 ^ 40 * 5127129 * 2
def baseEnd_5127129 : Nat := 2632681554605975817908269

theorem tailTrace_5127129 : CollatzResearch.WordTrace tailWord_5127129 prefixEnd_5127129 2632681554605975817908269 := by
  unfold tailWord_5127129
  simp only [CollatzResearch.WordTrace]
  refine ⟨187001757442294751764736441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124667838294863167843157627 187001757442294751764736441)
  ·
    refine ⟨140251318081721063823552331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187001757442294751764736441 140251318081721063823552331)
    ·
      refine ⟨210376977122581595735328497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140251318081721063823552331 210376977122581595735328497)
      ·
        refine ⟨157782732841936196801496373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210376977122581595735328497 157782732841936196801496373)
        ·
          refine ⟨14792131203931518450140285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157782732841936196801496373 14792131203931518450140285)
          ·
            refine ⟨5547049201474319418802607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14792131203931518450140285 5547049201474319418802607)
            ·
              refine ⟨8320573802211479128203911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5547049201474319418802607 8320573802211479128203911)
              ·
                refine ⟨12480860703317218692305867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8320573802211479128203911 12480860703317218692305867)
                ·
                  refine ⟨18721291054975828038458801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12480860703317218692305867 18721291054975828038458801)
                  ·
                    refine ⟨14040968291231871028844101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18721291054975828038458801 14040968291231871028844101)
                    ·
                      refine ⟨2632681554605975817908269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14040968291231871028844101 2632681554605975817908269)
                      ·
                        rfl

theorem cell23_5127129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 2, 4].length) (baseStart_5127129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127129 prefixEnd_5127129 := by exact prefixLift 5127129
  have htrace : WordTrace (prefixWord ++ tailWord_5127129) baseStart_5127129 baseEnd_5127129 := by
    simpa [prefixWord, tailWord_5127129, baseEnd_5127129] using wordTrace_append hprefix tailTrace_5127129
  have hstable : (prefixWord ++ tailWord_5127129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127129).length < 2 ^ (prefixWord ++ tailWord_5127129).sum := by decide
  have hdescent : baseEnd_5127129 < baseStart_5127129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127155 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 4]
def baseStart_5127155 : Nat := 118140960795 + 5127155 * 2 ^ 59
def prefixEnd_5127155 : Nat := 4983230072969 + 3 ^ 40 * 5127155 * 2
def baseEnd_5127155 : Nat := 2632694905102992716183149

theorem tailTrace_5127155 : CollatzResearch.WordTrace tailWord_5127155 prefixEnd_5127155 2632694905102992716183149 := by
  unfold tailWord_5127155
  simp only [CollatzResearch.WordTrace]
  refine ⟨187002705740200558205182919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124668470493467038803455279 187002705740200558205182919)
  ·
    refine ⟨280504058610300837307774379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187002705740200558205182919 280504058610300837307774379)
    ·
      refine ⟨420756087915451255961661569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280504058610300837307774379 420756087915451255961661569)
      ·
        refine ⟨315567065936588441971246177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420756087915451255961661569 315567065936588441971246177)
        ·
          refine ⟨236675299452441331478434633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315567065936588441971246177 236675299452441331478434633)
          ·
            refine ⟨177506474589330998608825975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236675299452441331478434633 177506474589330998608825975)
            ·
              refine ⟨266259711883996497913238963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177506474589330998608825975 266259711883996497913238963)
              ·
                refine ⟨399389567825994746869858445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266259711883996497913238963 399389567825994746869858445)
                ·
                  refine ⟨149771087934748030076196917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399389567825994746869858445 149771087934748030076196917)
                  ·
                    refine ⟨14041039493882627819643461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 149771087934748030076196917 14041039493882627819643461)
                    ·
                      refine ⟨2632694905102992716183149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14041039493882627819643461 2632694905102992716183149)
                      ·
                        rfl

theorem cell23_5127155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_5127155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127155 prefixEnd_5127155 := by exact prefixLift 5127155
  have htrace : WordTrace (prefixWord ++ tailWord_5127155) baseStart_5127155 baseEnd_5127155 := by
    simpa [prefixWord, tailWord_5127155, baseEnd_5127155] using wordTrace_append hprefix tailTrace_5127155
  have hstable : (prefixWord ++ tailWord_5127155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127155).length < 2 ^ (prefixWord ++ tailWord_5127155).sum := by decide
  have hdescent : baseEnd_5127155 < baseStart_5127155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127185 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 6]
def baseStart_5127185 : Nat := 118140960795 + 5127185 * 2 ^ 59
def prefixEnd_5127185 : Nat := 4983230072969 + 3 ^ 40 * 5127185 * 2
def baseEnd_5127185 : Nat := 2632710309522627598808011

theorem tailTrace_5127185 : CollatzResearch.WordTrace tailWord_5127185 prefixEnd_5127185 2632710309522627598808011 := by
  unfold tailWord_5127185
  simp only [CollatzResearch.WordTrace]
  refine ⟨187003799930091873328775009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124669199953394582219183339 187003799930091873328775009)
  ·
    refine ⟨140252849947568904996581257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187003799930091873328775009 140252849947568904996581257)
    ·
      refine ⟨105189637460676678747435943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140252849947568904996581257 105189637460676678747435943)
      ·
        refine ⟨157784456191015018121153915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105189637460676678747435943 157784456191015018121153915)
        ·
          refine ⟨236676684286522527181730873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157784456191015018121153915 236676684286522527181730873)
          ·
            refine ⟨177507513214891895386298155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236676684286522527181730873 177507513214891895386298155)
            ·
              refine ⟨266261269822337843079447233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177507513214891895386298155 266261269822337843079447233)
              ·
                refine ⟨199695952366753382309585425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266261269822337843079447233 199695952366753382309585425)
                ·
                  refine ⟨149771964275065036732189069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199695952366753382309585425 149771964275065036732189069)
                  ·
                    refine ⟨56164486603149388774570901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 149771964275065036732189069 56164486603149388774570901)
                    ·
                      refine ⟨2632710309522627598808011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56164486603149388774570901 2632710309522627598808011)
                      ·
                        rfl

theorem cell23_5127185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_5127185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127185 prefixEnd_5127185 := by exact prefixLift 5127185
  have htrace : WordTrace (prefixWord ++ tailWord_5127185) baseStart_5127185 baseEnd_5127185 := by
    simpa [prefixWord, tailWord_5127185, baseEnd_5127185] using wordTrace_append hprefix tailTrace_5127185
  have hstable : (prefixWord ++ tailWord_5127185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127185).length < 2 ^ (prefixWord ++ tailWord_5127185).sum := by decide
  have hdescent : baseEnd_5127185 < baseStart_5127185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127192 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 2, 1, 5]
def baseStart_5127192 : Nat := 118140960795 + 5127192 * 2 ^ 59
def prefixEnd_5127192 : Nat := 4983230072969 + 3 ^ 40 * 5127192 * 2
def baseEnd_5127192 : Nat := 2632713903887209071420479

theorem tailTrace_5127192 : CollatzResearch.WordTrace tailWord_5127192 prefixEnd_5127192 2632713903887209071420479 := by
  unfold tailWord_5127192
  simp only [CollatzResearch.WordTrace]
  refine ⟨93502027620533256762139915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124669370160711009016186553 93502027620533256762139915)
  ·
    refine ⟨140253041430799885143209873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93502027620533256762139915 140253041430799885143209873)
    ·
      refine ⟨105189781073099913857407405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140253041430799885143209873 105189781073099913857407405)
      ·
        refine ⟨39446167902412467696527777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105189781073099913857407405 39446167902412467696527777)
        ·
          refine ⟨29584625926809350772395833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39446167902412467696527777 29584625926809350772395833)
          ·
            refine ⟨22188469445107013079296875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29584625926809350772395833 22188469445107013079296875)
            ·
              refine ⟨33282704167660519618945313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22188469445107013079296875 33282704167660519618945313)
              ·
                refine ⟨24962028125745389714208985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33282704167660519618945313 24962028125745389714208985)
                ·
                  refine ⟨18721521094309042285656739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24962028125745389714208985 18721521094309042285656739)
                  ·
                    refine ⟨28082281641463563428485109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18721521094309042285656739 28082281641463563428485109)
                    ·
                      refine ⟨2632713903887209071420479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28082281641463563428485109 2632713903887209071420479)
                      ·
                        rfl

theorem cell23_5127192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_5127192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127192 prefixEnd_5127192 := by exact prefixLift 5127192
  have htrace : WordTrace (prefixWord ++ tailWord_5127192) baseStart_5127192 baseEnd_5127192 := by
    simpa [prefixWord, tailWord_5127192, baseEnd_5127192] using wordTrace_append hprefix tailTrace_5127192
  have hstable : (prefixWord ++ tailWord_5127192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127192).length < 2 ^ (prefixWord ++ tailWord_5127192).sum := by decide
  have hdescent : baseEnd_5127192 < baseStart_5127192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127210 : List Nat := [3, 1, 4, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_5127210 : Nat := 118140960795 + 5127210 * 2 ^ 59
def prefixEnd_5127210 : Nat := 4983230072969 + 3 ^ 40 * 5127210 * 2
def baseEnd_5127210 : Nat := 2632723146538990000995397

theorem tailTrace_5127210 : CollatzResearch.WordTrace tailWord_5127210 prefixEnd_5127210 2632723146538990000995397 := by
  unfold tailWord_5127210
  simp only [CollatzResearch.WordTrace]
  refine ⟨46751177938750325649608771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124669807836667535065623389 46751177938750325649608771)
  ·
    refine ⟨70126766908125488474413157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46751177938750325649608771 70126766908125488474413157)
    ·
      refine ⟨13148768795273529088952467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70126766908125488474413157 13148768795273529088952467)
      ·
        refine ⟨19723153192910293633428701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13148768795273529088952467 19723153192910293633428701)
        ·
          refine ⟨7396182447341360112535763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19723153192910293633428701 7396182447341360112535763)
          ·
            refine ⟨11094273671012040168803645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7396182447341360112535763 11094273671012040168803645)
            ·
              refine ⟨4160352626629515063301367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11094273671012040168803645 4160352626629515063301367)
              ·
                refine ⟨6240528939944272594952051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4160352626629515063301367 6240528939944272594952051)
                ·
                  refine ⟨9360793409916408892428077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6240528939944272594952051 9360793409916408892428077)
                  ·
                    refine ⟨3510297528718653334660529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9360793409916408892428077 3510297528718653334660529)
                    ·
                      refine ⟨2632723146538990000995397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3510297528718653334660529 2632723146538990000995397)
                      ·
                        rfl

theorem cell23_5127210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_5127210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127210 prefixEnd_5127210 := by exact prefixLift 5127210
  have htrace : WordTrace (prefixWord ++ tailWord_5127210) baseStart_5127210 baseEnd_5127210 := by
    simpa [prefixWord, tailWord_5127210, baseEnd_5127210] using wordTrace_append hprefix tailTrace_5127210
  have hstable : (prefixWord ++ tailWord_5127210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127210).length < 2 ^ (prefixWord ++ tailWord_5127210).sum := by decide
  have hdescent : baseEnd_5127210 < baseStart_5127210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127215 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 8]
def baseStart_5127215 : Nat := 118140960795 + 5127215 * 2 ^ 59
def prefixEnd_5127215 : Nat := 4983230072969 + 3 ^ 40 * 5127215 * 2
def baseEnd_5127215 : Nat := 2632725713942262481432873

theorem tailTrace_5127215 : CollatzResearch.WordTrace tailWord_5127215 prefixEnd_5127215 2632725713942262481432873 := by
  unfold tailWord_5127215
  simp only [CollatzResearch.WordTrace]
  refine ⟨187004894119983188452367099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124669929413322125634911399 187004894119983188452367099)
  ·
    refine ⟨280507341179974782678550649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187004894119983188452367099 280507341179974782678550649)
    ·
      refine ⟨210380505884981087008912987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280507341179974782678550649 210380505884981087008912987)
      ·
        refine ⟨315570758827471630513369481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210380505884981087008912987 315570758827471630513369481)
        ·
          refine ⟨236678069120603722885027111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315570758827471630513369481 236678069120603722885027111)
          ·
            refine ⟨355017103680905584327540667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236678069120603722885027111 355017103680905584327540667)
            ·
              refine ⟨532525655521358376491311001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355017103680905584327540667 532525655521358376491311001)
              ·
                refine ⟨399394241641018782368483251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 532525655521358376491311001 399394241641018782368483251)
                ·
                  refine ⟨599091362461528173552724877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 399394241641018782368483251 599091362461528173552724877)
                  ·
                    refine ⟨224659260923073065082271829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 599091362461528173552724877 224659260923073065082271829)
                    ·
                      refine ⟨2632725713942262481432873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 224659260923073065082271829 2632725713942262481432873)
                      ·
                        rfl

theorem cell23_5127215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_5127215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127215 prefixEnd_5127215 := by exact prefixLift 5127215
  have htrace : WordTrace (prefixWord ++ tailWord_5127215) baseStart_5127215 baseEnd_5127215 := by
    simpa [prefixWord, tailWord_5127215, baseEnd_5127215] using wordTrace_append hprefix tailTrace_5127215
  have hstable : (prefixWord ++ tailWord_5127215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127215).length < 2 ^ (prefixWord ++ tailWord_5127215).sum := by decide
  have hdescent : baseEnd_5127215 < baseStart_5127215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127239 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 3]
def baseStart_5127239 : Nat := 118140960795 + 5127239 * 2 ^ 59
def prefixEnd_5127239 : Nat := 4983230072969 + 3 ^ 40 * 5127239 * 2
def baseEnd_5127239 : Nat := 2632738037477970387532763

theorem tailTrace_5127239 : CollatzResearch.WordTrace tailWord_5127239 prefixEnd_5127239 2632738037477970387532763 := by
  unfold tailWord_5127239
  simp only [CollatzResearch.WordTrace]
  refine ⟨187005769471896240551240771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124670512981264160367493847 187005769471896240551240771)
  ·
    refine ⟨280508654207844360826861157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187005769471896240551240771 280508654207844360826861157)
    ·
      refine ⟨52595372663970817655036467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 280508654207844360826861157 52595372663970817655036467)
      ·
        refine ⟨78893058995956226482554701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52595372663970817655036467 78893058995956226482554701)
        ·
          refine ⟨29584897123483584930958013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78893058995956226482554701 29584897123483584930958013)
          ·
            refine ⟨11094336421306344349109255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29584897123483584930958013 11094336421306344349109255)
            ·
              refine ⟨16641504631959516523663883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11094336421306344349109255 16641504631959516523663883)
              ·
                refine ⟨24962256947939274785495825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16641504631959516523663883 24962256947939274785495825)
                ·
                  refine ⟨18721692710954456089121869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24962256947939274785495825 18721692710954456089121869)
                  ·
                    refine ⟨7020634766607921033420701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18721692710954456089121869 7020634766607921033420701)
                    ·
                      refine ⟨2632738037477970387532763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7020634766607921033420701 2632738037477970387532763)
                      ·
                        rfl

theorem cell23_5127239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_5127239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127239 prefixEnd_5127239 := by exact prefixLift 5127239
  have htrace : WordTrace (prefixWord ++ tailWord_5127239) baseStart_5127239 baseEnd_5127239 := by
    simpa [prefixWord, tailWord_5127239, baseEnd_5127239] using wordTrace_append hprefix tailTrace_5127239
  have hstable : (prefixWord ++ tailWord_5127239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127239).length < 2 ^ (prefixWord ++ tailWord_5127239).sum := by decide
  have hdescent : baseEnd_5127239 < baseStart_5127239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127242 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 4, 5]
def baseStart_5127242 : Nat := 118140960795 + 5127242 * 2 ^ 59
def prefixEnd_5127242 : Nat := 4983230072969 + 3 ^ 40 * 5127242 * 2
def baseEnd_5127242 : Nat := 877579859306644625265083

theorem tailTrace_5127242 : CollatzResearch.WordTrace tailWord_5127242 prefixEnd_5127242 877579859306644625265083 := by
  unfold tailWord_5127242
  simp only [CollatzResearch.WordTrace]
  refine ⟨46751469722721343015899995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124670585927256914709066653 46751469722721343015899995)
  ·
    refine ⟨70127204584082014523849993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46751469722721343015899995 70127204584082014523849993)
    ·
      refine ⟨52595403438061510892887495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70127204584082014523849993 52595403438061510892887495)
      ·
        refine ⟨78893105157092266339331243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52595403438061510892887495 78893105157092266339331243)
        ·
          refine ⟨118339657735638399508996865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78893105157092266339331243 118339657735638399508996865)
          ·
            refine ⟨88754743301728799631747649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118339657735638399508996865 88754743301728799631747649)
            ·
              refine ⟨66566057476296599723810737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88754743301728799631747649 66566057476296599723810737)
              ·
                refine ⟨49924543107222449792858053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66566057476296599723810737 49924543107222449792858053)
                ·
                  refine ⟨9360851832604209336160885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49924543107222449792858053 9360851832604209336160885)
                  ·
                    refine ⟨877579859306644625265083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9360851832604209336160885 877579859306644625265083)
                    ·
                      rfl

theorem cell23_5127242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_5127242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127242 prefixEnd_5127242 := by exact prefixLift 5127242
  have htrace : WordTrace (prefixWord ++ tailWord_5127242) baseStart_5127242 baseEnd_5127242 := by
    simpa [prefixWord, tailWord_5127242, baseEnd_5127242] using wordTrace_append hprefix tailTrace_5127242
  have hstable : (prefixWord ++ tailWord_5127242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127242).length < 2 ^ (prefixWord ++ tailWord_5127242).sum := by decide
  have hdescent : baseEnd_5127242 < baseStart_5127242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127252 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_5127252 : Nat := 118140960795 + 5127252 * 2 ^ 59
def prefixEnd_5127252 : Nat := 4983230072969 + 3 ^ 40 * 5127252 * 2
def baseEnd_5127252 : Nat := 2632744712726478836670203

theorem tailTrace_5127252 : CollatzResearch.WordTrace tailWord_5127252 prefixEnd_5127252 2632744712726478836670203 := by
  unfold tailWord_5127252
  simp only [CollatzResearch.WordTrace]
  refine ⟨93503121810424571885732005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124670829080566095847642673 93503121810424571885732005)
  ·
    refine ⟨17531835339454607228574751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93503121810424571885732005 17531835339454607228574751)
    ·
      refine ⟨26297753009181910842862127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17531835339454607228574751 26297753009181910842862127)
      ·
        refine ⟨39446629513772866264293191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26297753009181910842862127 39446629513772866264293191)
        ·
          refine ⟨59169944270659299396439787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39446629513772866264293191 59169944270659299396439787)
          ·
            refine ⟨88754916405988949094659681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59169944270659299396439787 88754916405988949094659681)
            ·
              refine ⟨66566187304491711820994761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88754916405988949094659681 66566187304491711820994761)
              ·
                refine ⟨49924640478368783865746071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66566187304491711820994761 49924640478368783865746071)
                ·
                  refine ⟨74886960717553175798619107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49924640478368783865746071 74886960717553175798619107)
                  ·
                    refine ⟨112330441076329763697928661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74886960717553175798619107 112330441076329763697928661)
                    ·
                      refine ⟨2632744712726478836670203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112330441076329763697928661 2632744712726478836670203)
                      ·
                        rfl

theorem cell23_5127252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_5127252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127252 prefixEnd_5127252 := by exact prefixLift 5127252
  have htrace : WordTrace (prefixWord ++ tailWord_5127252) baseStart_5127252 baseEnd_5127252 := by
    simpa [prefixWord, tailWord_5127252, baseEnd_5127252] using wordTrace_append hprefix tailTrace_5127252
  have hstable : (prefixWord ++ tailWord_5127252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127252).length < 2 ^ (prefixWord ++ tailWord_5127252).sum := by decide
  have hdescent : baseEnd_5127252 < baseStart_5127252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127279 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 4, 4, 2]
def baseStart_5127279 : Nat := 118140960795 + 5127279 * 2 ^ 59
def prefixEnd_5127279 : Nat := 4983230072969 + 3 ^ 40 * 5127279 * 2
def baseEnd_5127279 : Nat := 2632758576704150231032579

theorem tailTrace_5127279 : CollatzResearch.WordTrace tailWord_5127279 prefixEnd_5127279 2632758576704150231032579 := by
  unfold tailWord_5127279
  simp only [CollatzResearch.WordTrace]
  refine ⟨187007228391751327382696891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124671485594500884921797927 187007228391751327382696891)
  ·
    refine ⟨280510842587626991074045337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187007228391751327382696891 280510842587626991074045337)
    ·
      refine ⟨210383131940720243305534003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280510842587626991074045337 210383131940720243305534003)
      ·
        refine ⟨315574697911080364958301005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210383131940720243305534003 315574697911080364958301005)
        ·
          refine ⟨118340511716655136859362877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 315574697911080364958301005 118340511716655136859362877)
          ·
            refine ⟨44377691893745676322261079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118340511716655136859362877 44377691893745676322261079)
            ·
              refine ⟨66566537840618514483391619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44377691893745676322261079 66566537840618514483391619)
              ·
                refine ⟨99849806760927771725087429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66566537840618514483391619 99849806760927771725087429)
                ·
                  refine ⟨18721838767673957198453893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99849806760927771725087429 18721838767673957198453893)
                  ·
                    refine ⟨3510344768938866974710105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18721838767673957198453893 3510344768938866974710105)
                    ·
                      refine ⟨2632758576704150231032579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3510344768938866974710105 2632758576704150231032579)
                      ·
                        rfl

theorem cell23_5127279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 4, 2].length) (baseStart_5127279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127279 prefixEnd_5127279 := by exact prefixLift 5127279
  have htrace : WordTrace (prefixWord ++ tailWord_5127279) baseStart_5127279 baseEnd_5127279 := by
    simpa [prefixWord, tailWord_5127279, baseEnd_5127279] using wordTrace_append hprefix tailTrace_5127279
  have hstable : (prefixWord ++ tailWord_5127279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127279).length < 2 ^ (prefixWord ++ tailWord_5127279).sum := by decide
  have hdescent : baseEnd_5127279 < baseStart_5127279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127292 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_5127292 : Nat := 118140960795 + 5127292 * 2 ^ 59
def prefixEnd_5127292 : Nat := 4983230072969 + 3 ^ 40 * 5127292 * 2
def baseEnd_5127292 : Nat := 2632765251952658680170019

theorem tailTrace_5127292 : CollatzResearch.WordTrace tailWord_5127292 prefixEnd_5127292 2632765251952658680170019 := by
  unfold tailWord_5127292
  simp only [CollatzResearch.WordTrace]
  refine ⟨93503851270352115301460065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124671801693802820401946753 93503851270352115301460065)
  ·
    refine ⟨70127888452764086476095049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93503851270352115301460065 70127888452764086476095049)
    ·
      refine ⟨52595916339573064857071287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70127888452764086476095049 52595916339573064857071287)
      ·
        refine ⟨78893874509359597285606931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52595916339573064857071287 78893874509359597285606931)
        ·
          refine ⟨118340811764039395928410397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78893874509359597285606931 118340811764039395928410397)
          ·
            refine ⟨44377804411514773473153899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118340811764039395928410397 44377804411514773473153899)
            ·
              refine ⟨66566706617272160209730849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44377804411514773473153899 66566706617272160209730849)
              ·
                refine ⟨49925029962954120157298137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66566706617272160209730849 49925029962954120157298137)
                ·
                  refine ⟨37443772472215590117973603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49925029962954120157298137 37443772472215590117973603)
                  ·
                    refine ⟨56165658708323385176960405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37443772472215590117973603 56165658708323385176960405)
                    ·
                      refine ⟨2632765251952658680170019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56165658708323385176960405 2632765251952658680170019)
                      ·
                        rfl

theorem cell23_5127292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_5127292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127292 prefixEnd_5127292 := by exact prefixLift 5127292
  have htrace : WordTrace (prefixWord ++ tailWord_5127292) baseStart_5127292 baseEnd_5127292 := by
    simpa [prefixWord, tailWord_5127292, baseEnd_5127292] using wordTrace_append hprefix tailTrace_5127292
  have hstable : (prefixWord ++ tailWord_5127292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127292).length < 2 ^ (prefixWord ++ tailWord_5127292).sum := by decide
  have hdescent : baseEnd_5127292 < baseStart_5127292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127392 : List Nat := [2, 1, 1, 3, 1, 15]
def baseStart_5127392 : Nat := 118140960795 + 5127392 * 2 ^ 59
def prefixEnd_5127392 : Nat := 4983230072969 + 3 ^ 40 * 5127392 * 2
def baseEnd_5127392 : Nat := 10834636214066289254813

theorem tailTrace_5127392 : CollatzResearch.WordTrace tailWord_5127392 prefixEnd_5127392 10834636214066289254813 := by
  unfold tailWord_5127392
  simp only [CollatzResearch.WordTrace]
  refine ⟨93505674920170973840780215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124674233226894631787706953 93505674920170973840780215)
  ·
    refine ⟨140258512380256460761170323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93505674920170973840780215 140258512380256460761170323)
    ·
      refine ⟨210387768570384691141755485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140258512380256460761170323 210387768570384691141755485)
      ·
        refine ⟨78895413213894259178158307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210387768570384691141755485 78895413213894259178158307)
        ·
          refine ⟨118343119820841388767237461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78895413213894259178158307 118343119820841388767237461)
          ·
            refine ⟨10834636214066289254813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 118343119820841388767237461 10834636214066289254813)
            ·
              rfl

theorem cell23_5127392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 15].length) (baseStart_5127392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127392 prefixEnd_5127392 := by exact prefixLift 5127392
  have htrace : WordTrace (prefixWord ++ tailWord_5127392) baseStart_5127392 baseEnd_5127392 := by
    simpa [prefixWord, tailWord_5127392, baseEnd_5127392] using wordTrace_append hprefix tailTrace_5127392
  have hstable : (prefixWord ++ tailWord_5127392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127392).length < 2 ^ (prefixWord ++ tailWord_5127392).sum := by decide
  have hdescent : baseEnd_5127392 < baseStart_5127392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127396 : List Nat := [2, 3, 1, 1, 1, 2, 3, 4, 2, 4]
def baseStart_5127396 : Nat := 118140960795 + 5127396 * 2 ^ 59
def prefixEnd_5127396 : Nat := 4983230072969 + 3 ^ 40 * 5127396 * 2
def baseEnd_5127396 : Nat := 877606217980242091089847

theorem tailTrace_5127396 : CollatzResearch.WordTrace tailWord_5127396 prefixEnd_5127396 877606217980242091089847 := by
  unfold tailWord_5127396
  simp only [CollatzResearch.WordTrace]
  refine ⟨93505747866163728182353021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124674330488218304243137361 93505747866163728182353021)
  ·
    refine ⟨35064655449811398068382383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93505747866163728182353021 35064655449811398068382383)
    ·
      refine ⟨52596983174717097102573575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35064655449811398068382383 52596983174717097102573575)
      ·
        refine ⟨78895474762075645653860363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52596983174717097102573575 78895474762075645653860363)
        ·
          refine ⟨118343212143113468480790545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78895474762075645653860363 118343212143113468480790545)
          ·
            refine ⟨88757409107335101360592909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118343212143113468480790545 88757409107335101360592909)
            ·
              refine ⟨33284028415250663010222341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88757409107335101360592909 33284028415250663010222341)
              ·
                refine ⟨6240755327859499314416689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33284028415250663010222341 6240755327859499314416689)
                ·
                  refine ⟨4680566495894624485812517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6240755327859499314416689 4680566495894624485812517)
                  ·
                    refine ⟨877606217980242091089847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4680566495894624485812517 877606217980242091089847)
                    ·
                      rfl

theorem cell23_5127396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_5127396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127396 prefixEnd_5127396 := by exact prefixLift 5127396
  have htrace : WordTrace (prefixWord ++ tailWord_5127396) baseStart_5127396 baseEnd_5127396 := by
    simpa [prefixWord, tailWord_5127396, baseEnd_5127396] using wordTrace_append hprefix tailTrace_5127396
  have hstable : (prefixWord ++ tailWord_5127396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127396).length < 2 ^ (prefixWord ++ tailWord_5127396).sum := by decide
  have hdescent : baseEnd_5127396 < baseStart_5127396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127406 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_5127406 : Nat := 118140960795 + 5127406 * 2 ^ 59
def prefixEnd_5127406 : Nat := 4983230072969 + 3 ^ 40 * 5127406 * 2
def baseEnd_5127406 : Nat := 2632823788747271234144495

theorem tailTrace_5127406 : CollatzResearch.WordTrace tailWord_5127406 prefixEnd_5127406 2632823788747271234144495 := by
  unfold tailWord_5127406
  simp only [CollatzResearch.WordTrace]
  refine ⟨23376482557786403509071259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124674573641527485381713381 23376482557786403509071259)
  ·
    refine ⟨35064723836679605263606889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23376482557786403509071259 35064723836679605263606889)
    ·
      refine ⟨26298542877509703947705167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35064723836679605263606889 26298542877509703947705167)
      ·
        refine ⟨39447814316264555921557751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26298542877509703947705167 39447814316264555921557751)
        ·
          refine ⟨59171721474396833882336627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39447814316264555921557751 59171721474396833882336627)
          ·
            refine ⟨88757582211595250823504941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59171721474396833882336627 88757582211595250823504941)
            ·
              refine ⟨33284093329348219058814353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88757582211595250823504941 33284093329348219058814353)
              ·
                refine ⟨24963069997011164294110765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33284093329348219058814353 24963069997011164294110765)
                ·
                  refine ⟨9361151248879186610291537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24963069997011164294110765 9361151248879186610291537)
                  ·
                    refine ⟨7020863436659389957718653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9361151248879186610291537 7020863436659389957718653)
                    ·
                      refine ⟨2632823788747271234144495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7020863436659389957718653 2632823788747271234144495)
                      ·
                        rfl

theorem cell23_5127406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_5127406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127406 prefixEnd_5127406 := by exact prefixLift 5127406
  have htrace : WordTrace (prefixWord ++ tailWord_5127406) baseStart_5127406 baseEnd_5127406 := by
    simpa [prefixWord, tailWord_5127406, baseEnd_5127406] using wordTrace_append hprefix tailTrace_5127406
  have hstable : (prefixWord ++ tailWord_5127406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127406).length < 2 ^ (prefixWord ++ tailWord_5127406).sum := by decide
  have hdescent : baseEnd_5127406 < baseStart_5127406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127420 : List Nat := [2, 2, 2, 1, 5, 1, 1, 2, 3, 2, 2]
def baseStart_5127420 : Nat := 118140960795 + 5127420 * 2 ^ 59
def prefixEnd_5127420 : Nat := 4983230072969 + 3 ^ 40 * 5127420 * 2
def baseEnd_5127420 : Nat := 2632830977476434179369431

theorem tailTrace_5127420 : CollatzResearch.WordTrace tailWord_5127420 prefixEnd_5127420 2632830977476434179369431 := by
  unfold tailWord_5127420
  simp only [CollatzResearch.WordTrace]
  refine ⟨93506185542120254231789857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124674914056160338975719809 93506185542120254231789857)
  ·
    refine ⟨70129639156590190673842393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93506185542120254231789857 70129639156590190673842393)
    ·
      refine ⟨52597229367442643005381795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70129639156590190673842393 52597229367442643005381795)
      ·
        refine ⟨78895844051163964508072693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52597229367442643005381795 78895844051163964508072693)
        ·
          refine ⟨7396485379796621672631815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78895844051163964508072693 7396485379796621672631815)
          ·
            refine ⟨11094728069694932508947723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7396485379796621672631815 11094728069694932508947723)
            ·
              refine ⟨16642092104542398763421585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11094728069694932508947723 16642092104542398763421585)
              ·
                refine ⟨12481569078406799072566189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16642092104542398763421585 12481569078406799072566189)
                ·
                  refine ⟨4680588404402549652212321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12481569078406799072566189 4680588404402549652212321)
                  ·
                    refine ⟨3510441303301912239159241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4680588404402549652212321 3510441303301912239159241)
                    ·
                      refine ⟨2632830977476434179369431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3510441303301912239159241 2632830977476434179369431)
                      ·
                        rfl

theorem cell23_5127420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_5127420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127420 prefixEnd_5127420 := by exact prefixLift 5127420
  have htrace : WordTrace (prefixWord ++ tailWord_5127420) baseStart_5127420 baseEnd_5127420 := by
    simpa [prefixWord, tailWord_5127420, baseEnd_5127420] using wordTrace_append hprefix tailTrace_5127420
  have hstable : (prefixWord ++ tailWord_5127420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127420).length < 2 ^ (prefixWord ++ tailWord_5127420).sum := by decide
  have hdescent : baseEnd_5127420 < baseStart_5127420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127436 : List Nat := [2, 2, 1, 2, 2, 3, 2, 2, 1, 3, 3]
def baseStart_5127436 : Nat := 118140960795 + 5127436 * 2 ^ 59
def prefixEnd_5127436 : Nat := 4983230072969 + 3 ^ 40 * 5127436 * 2
def baseEnd_5127436 : Nat := 2632839193166906116769357

theorem tailTrace_5127436 : CollatzResearch.WordTrace tailWord_5127436 prefixEnd_5127436 2632839193166906116769357 := by
  unfold tailWord_5127436
  simp only [CollatzResearch.WordTrace]
  refine ⟨93506477326091271598081081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124675303101455028797441441 93506477326091271598081081)
  ·
    refine ⟨70129857994568453698560811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93506477326091271598081081 70129857994568453698560811)
    ·
      refine ⟨105194786991852680547841217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70129857994568453698560811 105194786991852680547841217)
      ·
        refine ⟨78896090243889510410880913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105194786991852680547841217 78896090243889510410880913)
        ·
          refine ⟨59172067682917132808160685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78896090243889510410880913 59172067682917132808160685)
          ·
            refine ⟨22189525381093924803060257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59172067682917132808160685 22189525381093924803060257)
            ·
              refine ⟨16642144035820443602295193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22189525381093924803060257 16642144035820443602295193)
              ·
                refine ⟨12481608026865332701721395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16642144035820443602295193 12481608026865332701721395)
                ·
                  refine ⟨18722412040297999052582093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12481608026865332701721395 18722412040297999052582093)
                  ·
                    refine ⟨7020904515111749644718285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18722412040297999052582093 7020904515111749644718285)
                    ·
                      refine ⟨2632839193166906116769357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7020904515111749644718285 2632839193166906116769357)
                      ·
                        rfl

theorem cell23_5127436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_5127436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127436 prefixEnd_5127436 := by exact prefixLift 5127436
  have htrace : WordTrace (prefixWord ++ tailWord_5127436) baseStart_5127436 baseEnd_5127436 := by
    simpa [prefixWord, tailWord_5127436, baseEnd_5127436] using wordTrace_append hprefix tailTrace_5127436
  have hstable : (prefixWord ++ tailWord_5127436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127436).length < 2 ^ (prefixWord ++ tailWord_5127436).sum := by decide
  have hdescent : baseEnd_5127436 < baseStart_5127436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127454 : List Nat := [4, 3, 2, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_5127454 : Nat := 118140960795 + 5127454 * 2 ^ 59
def prefixEnd_5127454 : Nat := 4983230072969 + 3 ^ 40 * 5127454 * 2
def baseEnd_5127454 : Nat := 2632848435818687046344275

theorem tailTrace_5127454 : CollatzResearch.WordTrace tailWord_5127454 prefixEnd_5127454 2632848435818687046344275 := by
  unfold tailWord_5127454
  simp only [CollatzResearch.WordTrace]
  refine ⟨23376701395764666533789677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124675740777411554846878277 23376701395764666533789677)
  ·
    refine ⟨8766263023411749950171129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23376701395764666533789677 8766263023411749950171129)
    ·
      refine ⟨6574697267558812462628347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8766263023411749950171129 6574697267558812462628347)
      ·
        refine ⟨9862045901338218693942521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6574697267558812462628347 9862045901338218693942521)
        ·
          refine ⟨7396534426003664020456891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9862045901338218693942521 7396534426003664020456891)
          ·
            refine ⟨11094801639005496030685337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7396534426003664020456891 11094801639005496030685337)
            ·
              refine ⟨8321101229254122023014003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11094801639005496030685337 8321101229254122023014003)
              ·
                refine ⟨12481651843881183034521005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8321101229254122023014003 12481651843881183034521005)
                ·
                  refine ⟨4680619441455443637945377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12481651843881183034521005 4680619441455443637945377)
                  ·
                    refine ⟨3510464581091582728459033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4680619441455443637945377 3510464581091582728459033)
                    ·
                      refine ⟨2632848435818687046344275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3510464581091582728459033 2632848435818687046344275)
                      ·
                        rfl

theorem cell23_5127454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_5127454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127454 prefixEnd_5127454 := by exact prefixLift 5127454
  have htrace : WordTrace (prefixWord ++ tailWord_5127454) baseStart_5127454 baseEnd_5127454 := by
    simpa [prefixWord, tailWord_5127454, baseEnd_5127454] using wordTrace_append hprefix tailTrace_5127454
  have hstable : (prefixWord ++ tailWord_5127454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127454).length < 2 ^ (prefixWord ++ tailWord_5127454).sum := by decide
  have hdescent : baseEnd_5127454 < baseStart_5127454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127527 : List Nat := [1, 1, 5, 1, 4, 1, 1, 3, 2, 2, 2]
def baseStart_5127527 : Nat := 118140960795 + 5127527 * 2 ^ 59
def prefixEnd_5127527 : Nat := 4983230072969 + 3 ^ 40 * 5127527 * 2
def baseEnd_5127527 : Nat := 2632885919906465260731439

theorem tailTrace_5127527 : CollatzResearch.WordTrace tailWord_5127527 prefixEnd_5127527 2632885919906465260731439 := by
  unfold tailWord_5127527
  simp only [CollatzResearch.WordTrace]
  refine ⟨187016273694852865737724835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124677515796568577158483223 187016273694852865737724835)
  ·
    refine ⟨280524410542279298606587253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187016273694852865737724835 280524410542279298606587253)
    ·
      refine ⟨26299163488338684244367555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 280524410542279298606587253 26299163488338684244367555)
      ·
        refine ⟨39448745232508026366551333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26299163488338684244367555 39448745232508026366551333)
        ·
          refine ⟨7396639731095254943728375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39448745232508026366551333 7396639731095254943728375)
          ·
            refine ⟨11094959596642882415592563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7396639731095254943728375 11094959596642882415592563)
            ·
              refine ⟨16642439394964323623388845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11094959596642882415592563 16642439394964323623388845)
              ·
                refine ⟨6240914773111621358770817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16642439394964323623388845 6240914773111621358770817)
                ·
                  refine ⟨4680686079833716019078113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6240914773111621358770817 4680686079833716019078113)
                  ·
                    refine ⟨3510514559875287014308585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4680686079833716019078113 3510514559875287014308585)
                    ·
                      refine ⟨2632885919906465260731439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3510514559875287014308585 2632885919906465260731439)
                      ·
                        rfl

theorem cell23_5127527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_5127527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127527 prefixEnd_5127527 := by exact prefixLift 5127527
  have htrace : WordTrace (prefixWord ++ tailWord_5127527) baseStart_5127527 baseEnd_5127527 := by
    simpa [prefixWord, tailWord_5127527, baseEnd_5127527] using wordTrace_append hprefix tailTrace_5127527
  have hstable : (prefixWord ++ tailWord_5127527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127527).length < 2 ^ (prefixWord ++ tailWord_5127527).sum := by decide
  have hdescent : baseEnd_5127527 < baseStart_5127527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127529 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 1, 7]
def baseStart_5127529 : Nat := 118140960795 + 5127529 * 2 ^ 59
def prefixEnd_5127529 : Nat := 4983230072969 + 3 ^ 40 * 5127529 * 2
def baseEnd_5127529 : Nat := 877628982289258084302143

theorem tailTrace_5127529 : CollatzResearch.WordTrace tailWord_5127529 prefixEnd_5127529 877628982289258084302143 := by
  unfold tailWord_5127529
  simp only [CollatzResearch.WordTrace]
  refine ⟨187016346640845620079297641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124677564427230413386198427 187016346640845620079297641)
  ·
    refine ⟨140262259980634215059473231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187016346640845620079297641 140262259980634215059473231)
    ·
      refine ⟨210393389970951322589209847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140262259980634215059473231 210393389970951322589209847)
      ·
        refine ⟨315590084956426983883814771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210393389970951322589209847 315590084956426983883814771)
        ·
          refine ⟨473385127434640475825722157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315590084956426983883814771 473385127434640475825722157)
          ·
            refine ⟨177519422787990178434645809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 473385127434640475825722157 177519422787990178434645809)
            ·
              refine ⟨133139567090992633825984357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177519422787990178434645809 133139567090992633825984357)
              ·
                refine ⟨24963668829561118842372067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133139567090992633825984357 24963668829561118842372067)
                ·
                  refine ⟨37445503244341678263558101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24963668829561118842372067 37445503244341678263558101)
                  ·
                    refine ⟨877628982289258084302143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37445503244341678263558101 877628982289258084302143)
                    ·
                      rfl

theorem cell23_5127529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 7].length) (baseStart_5127529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127529 prefixEnd_5127529 := by exact prefixLift 5127529
  have htrace : WordTrace (prefixWord ++ tailWord_5127529) baseStart_5127529 baseEnd_5127529 := by
    simpa [prefixWord, tailWord_5127529, baseEnd_5127529] using wordTrace_append hprefix tailTrace_5127529
  have hstable : (prefixWord ++ tailWord_5127529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127529).length < 2 ^ (prefixWord ++ tailWord_5127529).sum := by decide
  have hdescent : baseEnd_5127529 < baseStart_5127529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127539 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 5]
def baseStart_5127539 : Nat := 118140960795 + 5127539 * 2 ^ 59
def prefixEnd_5127539 : Nat := 4983230072969 + 3 ^ 40 * 5127539 * 2
def baseEnd_5127539 : Nat := 2632892081674319213781383

theorem tailTrace_5127539 : CollatzResearch.WordTrace tailWord_5127539 prefixEnd_5127539 2632892081674319213781383 := by
  unfold tailWord_5127539
  simp only [CollatzResearch.WordTrace]
  refine ⟨187016711370809391787161671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124677807580539594524774447 187016711370809391787161671)
  ·
    refine ⟨280525067056214087680742507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187016711370809391787161671 280525067056214087680742507)
    ·
      refine ⟨420787600584321131521113761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280525067056214087680742507 420787600584321131521113761)
      ·
        refine ⟨315590700438240848640835321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420787600584321131521113761 315590700438240848640835321)
        ·
          refine ⟨236693025328680636480626491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315590700438240848640835321 236693025328680636480626491)
          ·
            refine ⟨355039537993020954720939737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236693025328680636480626491 355039537993020954720939737)
            ·
              refine ⟨266279653494765716040704803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355039537993020954720939737 266279653494765716040704803)
              ·
                refine ⟨399419480242148574061057205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266279653494765716040704803 399419480242148574061057205)
                ·
                  refine ⟨37445576272701428818224113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 399419480242148574061057205 37445576272701428818224113)
                  ·
                    refine ⟨28084182204526071613668085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37445576272701428818224113 28084182204526071613668085)
                    ·
                      refine ⟨2632892081674319213781383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28084182204526071613668085 2632892081674319213781383)
                      ·
                        rfl

theorem cell23_5127539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_5127539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127539 prefixEnd_5127539 := by exact prefixLift 5127539
  have htrace : WordTrace (prefixWord ++ tailWord_5127539) baseStart_5127539 baseEnd_5127539 := by
    simpa [prefixWord, tailWord_5127539, baseEnd_5127539] using wordTrace_append hprefix tailTrace_5127539
  have hstable : (prefixWord ++ tailWord_5127539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127539).length < 2 ^ (prefixWord ++ tailWord_5127539).sum := by decide
  have hdescent : baseEnd_5127539 < baseStart_5127539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127556 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_5127556 : Nat := 118140960795 + 5127556 * 2 ^ 59
def prefixEnd_5127556 : Nat := 4983230072969 + 3 ^ 40 * 5127556 * 2
def baseEnd_5127556 : Nat := 2632900810845445647268805

theorem tailTrace_5127556 : CollatzResearch.WordTrace tailWord_5127556 prefixEnd_5127556 2632900810845445647268805 := by
  unfold tailWord_5127556
  simp only [CollatzResearch.WordTrace]
  refine ⟨93508665705873901845265261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124678220941165202460353681 93508665705873901845265261)
  ·
    refine ⟨35065749639702713191974473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93508665705873901845265261 35065749639702713191974473)
    ·
      refine ⟨26299312229777034893980855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35065749639702713191974473 26299312229777034893980855)
      ·
        refine ⟨39448968344665552340971283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26299312229777034893980855 39448968344665552340971283)
        ·
          refine ⟨59173452516998328511456925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39448968344665552340971283 59173452516998328511456925)
          ·
            refine ⟨22190044693874373191796347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59173452516998328511456925 22190044693874373191796347)
            ·
              refine ⟨33285067040811559787694521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22190044693874373191796347 33285067040811559787694521)
              ·
                refine ⟨24963800280608669840770891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33285067040811559787694521 24963800280608669840770891)
                ·
                  refine ⟨37445700420913004761156337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24963800280608669840770891 37445700420913004761156337)
                  ·
                    refine ⟨28084275315684753570867253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37445700420913004761156337 28084275315684753570867253)
                    ·
                      refine ⟨2632900810845445647268805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28084275315684753570867253 2632900810845445647268805)
                      ·
                        rfl

theorem cell23_5127556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_5127556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127556 prefixEnd_5127556 := by exact prefixLift 5127556
  have htrace : WordTrace (prefixWord ++ tailWord_5127556) baseStart_5127556 baseEnd_5127556 := by
    simpa [prefixWord, tailWord_5127556, baseEnd_5127556] using wordTrace_append hprefix tailTrace_5127556
  have hstable : (prefixWord ++ tailWord_5127556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127556).length < 2 ^ (prefixWord ++ tailWord_5127556).sum := by decide
  have hdescent : baseEnd_5127556 < baseStart_5127556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127579 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 6]
def baseStart_5127579 : Nat := 118140960795 + 5127579 * 2 ^ 59
def prefixEnd_5127579 : Nat := 4983230072969 + 3 ^ 40 * 5127579 * 2
def baseEnd_5127579 : Nat := 2632912620900499057281199

theorem tailTrace_5127579 : CollatzResearch.WordTrace tailWord_5127579 prefixEnd_5127579 2632912620900499057281199 := by
  unfold tailWord_5127579
  simp only [CollatzResearch.WordTrace]
  refine ⟨187018170290664478618617791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124678780193776319079078527 187018170290664478618617791)
  ·
    refine ⟨280527255435996717927926687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187018170290664478618617791 280527255435996717927926687)
    ·
      refine ⟨420790883153995076891890031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280527255435996717927926687 420790883153995076891890031)
      ·
        refine ⟨631186324730992615337835047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420790883153995076891890031 631186324730992615337835047)
        ·
          refine ⟨946779487096488923006752571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 631186324730992615337835047 946779487096488923006752571)
          ·
            refine ⟨1420169230644733384510128857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 946779487096488923006752571 1420169230644733384510128857)
            ·
              refine ⟨1065126922983550038382596643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1420169230644733384510128857 1065126922983550038382596643)
              ·
                refine ⟨1597690384475325057573894965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1065126922983550038382596643 1597690384475325057573894965)
                ·
                  refine ⟨149783473544561724147552653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1597690384475325057573894965 149783473544561724147552653)
                  ·
                    refine ⟨56168802579210646555332245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 149783473544561724147552653 56168802579210646555332245)
                    ·
                      refine ⟨2632912620900499057281199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56168802579210646555332245 2632912620900499057281199)
                      ·
                        rfl

theorem cell23_5127579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 6].length) (baseStart_5127579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127579 prefixEnd_5127579 := by exact prefixLift 5127579
  have htrace : WordTrace (prefixWord ++ tailWord_5127579) baseStart_5127579 baseEnd_5127579 := by
    simpa [prefixWord, tailWord_5127579, baseEnd_5127579] using wordTrace_append hprefix tailTrace_5127579
  have hstable : (prefixWord ++ tailWord_5127579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127579).length < 2 ^ (prefixWord ++ tailWord_5127579).sum := by decide
  have hdescent : baseEnd_5127579 < baseStart_5127579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127583 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 1, 6, 2]
def baseStart_5127583 : Nat := 118140960795 + 5127583 * 2 ^ 59
def prefixEnd_5127583 : Nat := 4983230072969 + 3 ^ 40 * 5127583 * 2
def baseEnd_5127583 : Nat := 2632914674823117041631181

theorem tailTrace_5127583 : CollatzResearch.WordTrace tailWord_5127583 prefixEnd_5127583 2632914674823117041631181 := by
  unfold tailWord_5127583
  simp only [CollatzResearch.WordTrace]
  refine ⟨187018316182649987301763403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124678877455099991534508935 187018316182649987301763403)
  ·
    refine ⟨280527474273974980952645105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187018316182649987301763403 280527474273974980952645105)
    ·
      refine ⟨210395605705481235714483829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280527474273974980952645105 210395605705481235714483829)
      ·
        refine ⟨19724588034888865848232859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 210395605705481235714483829 19724588034888865848232859)
        ·
          refine ⟨29586882052333298772349289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19724588034888865848232859 29586882052333298772349289)
          ·
            refine ⟨22190161539249974079261967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29586882052333298772349289 22190161539249974079261967)
            ·
              refine ⟨33285242308874961118892951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22190161539249974079261967 33285242308874961118892951)
              ·
                refine ⟨49927863463312441678339427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33285242308874961118892951 49927863463312441678339427)
                ·
                  refine ⟨74891795194968662517509141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49927863463312441678339427 74891795194968662517509141)
                  ·
                    refine ⟨3510552899764156055508241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74891795194968662517509141 3510552899764156055508241)
                    ·
                      refine ⟨2632914674823117041631181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3510552899764156055508241 2632914674823117041631181)
                      ·
                        rfl

theorem cell23_5127583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_5127583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127583 prefixEnd_5127583 := by exact prefixLift 5127583
  have htrace : WordTrace (prefixWord ++ tailWord_5127583) baseStart_5127583 baseEnd_5127583 := by
    simpa [prefixWord, tailWord_5127583, baseEnd_5127583] using wordTrace_append hprefix tailTrace_5127583
  have hstable : (prefixWord ++ tailWord_5127583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127583).length < 2 ^ (prefixWord ++ tailWord_5127583).sum := by decide
  have hdescent : baseEnd_5127583 < baseStart_5127583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127626 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_5127626 : Nat := 118140960795 + 5127626 * 2 ^ 59
def prefixEnd_5127626 : Nat := 4983230072969 + 3 ^ 40 * 5127626 * 2
def baseEnd_5127626 : Nat := 2632936754491260373393483

theorem tailTrace_5127626 : CollatzResearch.WordTrace tailWord_5127626 prefixEnd_5127626 2632936754491260373393483 := by
  unfold tailWord_5127626
  simp only [CollatzResearch.WordTrace]
  refine ⟨46754971130373551411394683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124679923014329470430385821 46754971130373551411394683)
  ·
    refine ⟨70132456695560327117092025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46754971130373551411394683 70132456695560327117092025)
    ·
      refine ⟨52599342521670245337819019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70132456695560327117092025 52599342521670245337819019)
      ·
        refine ⟨78899013782505368006728529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52599342521670245337819019 78899013782505368006728529)
        ·
          refine ⟨59174260336879026005046397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78899013782505368006728529 59174260336879026005046397)
          ·
            refine ⟨22190347626329634751892399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59174260336879026005046397 22190347626329634751892399)
            ·
              refine ⟨33285521439494452127838599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22190347626329634751892399 33285521439494452127838599)
              ·
                refine ⟨49928282159241678191757899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33285521439494452127838599 49928282159241678191757899)
                ·
                  refine ⟨74892423238862517287636849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49928282159241678191757899 74892423238862517287636849)
                  ·
                    refine ⟨56169317429146887965727637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74892423238862517287636849 56169317429146887965727637)
                    ·
                      refine ⟨2632936754491260373393483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56169317429146887965727637 2632936754491260373393483)
                      ·
                        rfl

theorem cell23_5127626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_5127626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127626 prefixEnd_5127626 := by exact prefixLift 5127626
  have htrace : WordTrace (prefixWord ++ tailWord_5127626) baseStart_5127626 baseEnd_5127626 := by
    simpa [prefixWord, tailWord_5127626, baseEnd_5127626] using wordTrace_append hprefix tailTrace_5127626
  have hstable : (prefixWord ++ tailWord_5127626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127626).length < 2 ^ (prefixWord ++ tailWord_5127626).sum := by decide
  have hdescent : baseEnd_5127626 < baseStart_5127626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127661 : List Nat := [1, 5, 1, 3, 3, 1, 1, 3, 1, 4]
def baseStart_5127661 : Nat := 118140960795 + 5127661 * 2 ^ 59
def prefixEnd_5127661 : Nat := 4983230072969 + 3 ^ 40 * 5127661 * 2
def baseEnd_5127661 : Nat := 877651575438055912151941

theorem tailTrace_5127661 : CollatzResearch.WordTrace tailWord_5127661 prefixEnd_5127661 877651575438055912151941 := by
  unfold tailWord_5127661
  simp only [CollatzResearch.WordTrace]
  refine ⟨187021161076367406623102837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124680774050911604415401891 187021161076367406623102837)
  ·
    refine ⟨17533233850909444370915891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 187021161076367406623102837 17533233850909444370915891)
    ·
      refine ⟨26299850776364166556373837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17533233850909444370915891 26299850776364166556373837)
      ·
        refine ⟨9862444041136562458640189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26299850776364166556373837 9862444041136562458640189)
        ·
          refine ⟨3698416515426210921990071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9862444041136562458640189 3698416515426210921990071)
          ·
            refine ⟨5547624773139316382985107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3698416515426210921990071 5547624773139316382985107)
            ·
              refine ⟨8321437159708974574477661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5547624773139316382985107 8321437159708974574477661)
              ·
                refine ⟨3120538934890865465429123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8321437159708974574477661 3120538934890865465429123)
                ·
                  refine ⟨4680808402336298198143685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3120538934890865465429123 4680808402336298198143685)
                  ·
                    refine ⟨877651575438055912151941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4680808402336298198143685 877651575438055912151941)
                    ·
                      rfl

theorem cell23_5127661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_5127661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127661 prefixEnd_5127661 := by exact prefixLift 5127661
  have htrace : WordTrace (prefixWord ++ tailWord_5127661) baseStart_5127661 baseEnd_5127661 := by
    simpa [prefixWord, tailWord_5127661, baseEnd_5127661] using wordTrace_append hprefix tailTrace_5127661
  have hstable : (prefixWord ++ tailWord_5127661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127661).length < 2 ^ (prefixWord ++ tailWord_5127661).sum := by decide
  have hdescent : baseEnd_5127661 < baseStart_5127661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127670 : List Nat := [5, 1, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_5127670 : Nat := 118140960795 + 5127670 * 2 ^ 59
def prefixEnd_5127670 : Nat := 4983230072969 + 3 ^ 40 * 5127670 * 2
def baseEnd_5127670 : Nat := 877653115880019400414427

theorem tailTrace_5127670 : CollatzResearch.WordTrace tailWord_5127670 prefixEnd_5127670 877653115880019400414427 := by
  unfold tailWord_5127670
  simp only [CollatzResearch.WordTrace]
  refine ⟨11688843083333425072511279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124680992888889867440120309 11688843083333425072511279)
  ·
    refine ⟨17533264625000137608766919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11688843083333425072511279 17533264625000137608766919)
    ·
      refine ⟨26299896937500206413150379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17533264625000137608766919 26299896937500206413150379)
      ·
        refine ⟨39449845406250309619725569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26299896937500206413150379 39449845406250309619725569)
        ·
          refine ⟨29587384054687732214794177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39449845406250309619725569 29587384054687732214794177)
          ·
            refine ⟨22190538041015799161095633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29587384054687732214794177 22190538041015799161095633)
            ·
              refine ⟨16642903530761849370821725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22190538041015799161095633 16642903530761849370821725)
              ·
                refine ⟨6241088824035693514058147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16642903530761849370821725 6241088824035693514058147)
                ·
                  refine ⟨9361633236053540271087221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6241088824035693514058147 9361633236053540271087221)
                  ·
                    refine ⟨877653115880019400414427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9361633236053540271087221 877653115880019400414427)
                    ·
                      rfl

theorem cell23_5127670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_5127670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127670 prefixEnd_5127670 := by exact prefixLift 5127670
  have htrace : WordTrace (prefixWord ++ tailWord_5127670) baseStart_5127670 baseEnd_5127670 := by
    simpa [prefixWord, tailWord_5127670, baseEnd_5127670] using wordTrace_append hprefix tailTrace_5127670
  have hstable : (prefixWord ++ tailWord_5127670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127670).length < 2 ^ (prefixWord ++ tailWord_5127670).sum := by decide
  have hdescent : baseEnd_5127670 < baseStart_5127670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127684 : List Nat := [2, 3, 2, 3, 2, 2, 1, 1, 3, 1, 3]
def baseStart_5127684 : Nat := 118140960795 + 5127684 * 2 ^ 59
def prefixEnd_5127684 : Nat := 4983230072969 + 3 ^ 40 * 5127684 * 2
def baseEnd_5127684 : Nat := 2632966536369221146468217

theorem tailTrace_5127684 : CollatzResearch.WordTrace tailWord_5127684 prefixEnd_5127684 2632966536369221146468217 := by
  unfold tailWord_5127684
  simp only [CollatzResearch.WordTrace]
  refine ⟨93510999977642040775595053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124681333303522721034126737 93510999977642040775595053)
  ·
    refine ⟨35066624991615765290848145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93510999977642040775595053 35066624991615765290848145)
    ·
      refine ⟨26299968743711823968136109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35066624991615765290848145 26299968743711823968136109)
      ·
        refine ⟨9862488278891933988051041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26299968743711823968136109 9862488278891933988051041)
        ·
          refine ⟨7396866209168950491038281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9862488278891933988051041 7396866209168950491038281)
          ·
            refine ⟨5547649656876712868278711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7396866209168950491038281 5547649656876712868278711)
            ·
              refine ⟨8321474485315069302418067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5547649656876712868278711 8321474485315069302418067)
              ·
                refine ⟨12482211727972603953627101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8321474485315069302418067 12482211727972603953627101)
                ·
                  refine ⟨4680829397989726482610163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12482211727972603953627101 4680829397989726482610163)
                  ·
                    refine ⟨7021244096984589723915245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4680829397989726482610163 7021244096984589723915245)
                    ·
                      refine ⟨2632966536369221146468217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7021244096984589723915245 2632966536369221146468217)
                      ·
                        rfl

theorem cell23_5127684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_5127684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127684 prefixEnd_5127684 := by exact prefixLift 5127684
  have htrace : WordTrace (prefixWord ++ tailWord_5127684) baseStart_5127684 baseEnd_5127684 := by
    simpa [prefixWord, tailWord_5127684, baseEnd_5127684] using wordTrace_append hprefix tailTrace_5127684
  have hstable : (prefixWord ++ tailWord_5127684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127684).length < 2 ^ (prefixWord ++ tailWord_5127684).sum := by decide
  have hdescent : baseEnd_5127684 < baseStart_5127684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127734 : List Nat := [5, 1, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_5127734 : Nat := 118140960795 + 5127734 * 2 ^ 59
def prefixEnd_5127734 : Nat := 4983230072969 + 3 ^ 40 * 5127734 * 2
def baseEnd_5127734 : Nat := 877664070133981983614329

theorem tailTrace_5127734 : CollatzResearch.WordTrace tailWord_5127734 prefixEnd_5127734 877664070133981983614329 := by
  unfold tailWord_5127734
  simp only [CollatzResearch.WordTrace]
  refine ⟨11688988975318933755656891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124682549070068626727006837 11688988975318933755656891)
  ·
    refine ⟨17533483462978400633485337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11688988975318933755656891 17533483462978400633485337)
    ·
      refine ⟨13150112597233800475114003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17533483462978400633485337 13150112597233800475114003)
      ·
        refine ⟨19725168895850700712671005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13150112597233800475114003 19725168895850700712671005)
        ·
          refine ⟨7396938335944012767251627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19725168895850700712671005 7396938335944012767251627)
          ·
            refine ⟨11095407503916019150877441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7396938335944012767251627 11095407503916019150877441)
            ·
              refine ⟨8321555627937014363158081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11095407503916019150877441 8321555627937014363158081)
              ·
                refine ⟨6241166720952760772368561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8321555627937014363158081 6241166720952760772368561)
                ·
                  refine ⟨4680875040714570579276421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6241166720952760772368561 4680875040714570579276421)
                  ·
                    refine ⟨877664070133981983614329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4680875040714570579276421 877664070133981983614329)
                    ·
                      rfl

theorem cell23_5127734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_5127734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127734 prefixEnd_5127734 := by exact prefixLift 5127734
  have htrace : WordTrace (prefixWord ++ tailWord_5127734) baseStart_5127734 baseEnd_5127734 := by
    simpa [prefixWord, tailWord_5127734, baseEnd_5127734] using wordTrace_append hprefix tailTrace_5127734
  have hstable : (prefixWord ++ tailWord_5127734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127734).length < 2 ^ (prefixWord ++ tailWord_5127734).sum := by decide
  have hdescent : baseEnd_5127734 < baseStart_5127734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127741 : List Nat := [1, 4, 1, 3, 3, 1, 1, 4, 1, 2, 2]
def baseStart_5127741 : Nat := 118140960795 + 5127741 * 2 ^ 59
def prefixEnd_5127741 : Nat := 4983230072969 + 3 ^ 40 * 5127741 * 2
def baseEnd_5127741 : Nat := 2632995804766527423455455

theorem tailTrace_5127741 : CollatzResearch.WordTrace tailWord_5127741 prefixEnd_5127741 2632995804766527423455455 := by
  unfold tailWord_5127741
  simp only [CollatzResearch.WordTrace]
  refine ⟨187024078916077580286015077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124682719277385053524010051 187024078916077580286015077)
  ·
    refine ⟨35067014796764546303627827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187024078916077580286015077 35067014796764546303627827)
    ·
      refine ⟨52600522195146819455441741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35067014796764546303627827 52600522195146819455441741)
      ·
        refine ⟨19725195823180057295790653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52600522195146819455441741 19725195823180057295790653)
        ·
          refine ⟨7396948433692521485921495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19725195823180057295790653 7396948433692521485921495)
          ·
            refine ⟨11095422650538782228882243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7396948433692521485921495 11095422650538782228882243)
            ·
              refine ⟨16643133975808173343323365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11095422650538782228882243 16643133975808173343323365)
              ·
                refine ⟨3120587620464032501873131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16643133975808173343323365 3120587620464032501873131)
                ·
                  refine ⟨4680881430696048752809697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3120587620464032501873131 4680881430696048752809697)
                  ·
                    refine ⟨3510661073022036564607273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4680881430696048752809697 3510661073022036564607273)
                    ·
                      refine ⟨2632995804766527423455455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3510661073022036564607273 2632995804766527423455455)
                      ·
                        rfl

theorem cell23_5127741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_5127741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127741 prefixEnd_5127741 := by exact prefixLift 5127741
  have htrace : WordTrace (prefixWord ++ tailWord_5127741) baseStart_5127741 baseEnd_5127741 := by
    simpa [prefixWord, tailWord_5127741, baseEnd_5127741] using wordTrace_append hprefix tailTrace_5127741
  have hstable : (prefixWord ++ tailWord_5127741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127741).length < 2 ^ (prefixWord ++ tailWord_5127741).sum := by decide
  have hdescent : baseEnd_5127741 < baseStart_5127741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127783 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_5127783 : Nat := 118140960795 + 5127783 * 2 ^ 59
def prefixEnd_5127783 : Nat := 4983230072969 + 3 ^ 40 * 5127783 * 2
def baseEnd_5127783 : Nat := 2633017370954016259130261

theorem tailTrace_5127783 : CollatzResearch.WordTrace tailWord_5127783 prefixEnd_5127783 2633017370954016259130261 := by
  unfold tailWord_5127783
  simp only [CollatzResearch.WordTrace]
  refine ⟨187025610781925421459044003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124683740521283614306029335 187025610781925421459044003)
  ·
    refine ⟨280538416172888132188566005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187025610781925421459044003 280538416172888132188566005)
    ·
      refine ⟨26300476516208262392678063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 280538416172888132188566005 26300476516208262392678063)
      ·
        refine ⟨39450714774312393589017095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26300476516208262392678063 39450714774312393589017095)
        ·
          refine ⟨59176072161468590383525643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39450714774312393589017095 59176072161468590383525643)
          ·
            refine ⟨88764108242202885575288465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59176072161468590383525643 88764108242202885575288465)
            ·
              refine ⟨66573081181652164181466349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88764108242202885575288465 66573081181652164181466349)
              ·
                refine ⟨24964905443119561568049881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66573081181652164181466349 24964905443119561568049881)
                ·
                  refine ⟨18723679082339671176037411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24964905443119561568049881 18723679082339671176037411)
                  ·
                    refine ⟨28085518623509506764056117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18723679082339671176037411 28085518623509506764056117)
                    ·
                      refine ⟨2633017370954016259130261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28085518623509506764056117 2633017370954016259130261)
                      ·
                        rfl

theorem cell23_5127783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_5127783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127783 prefixEnd_5127783 := by exact prefixLift 5127783
  have htrace : WordTrace (prefixWord ++ tailWord_5127783) baseStart_5127783 baseEnd_5127783 := by
    simpa [prefixWord, tailWord_5127783, baseEnd_5127783] using wordTrace_append hprefix tailTrace_5127783
  have hstable : (prefixWord ++ tailWord_5127783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127783).length < 2 ^ (prefixWord ++ tailWord_5127783).sum := by decide
  have hdescent : baseEnd_5127783 < baseStart_5127783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127784 : List Nat := [2, 1, 4, 3, 1, 2, 1, 3, 1, 3, 2]
def baseStart_5127784 : Nat := 118140960795 + 5127784 * 2 ^ 59
def prefixEnd_5127784 : Nat := 4983230072969 + 3 ^ 40 * 5127784 * 2
def baseEnd_5127784 : Nat := 2633017884434670755217757

theorem tailTrace_5127784 : CollatzResearch.WordTrace tailWord_5127784 prefixEnd_5127784 2633017884434670755217757 := by
  unfold tailWord_5127784
  simp only [CollatzResearch.WordTrace]
  refine ⟨93512823627460899314915203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124683764836614532419886937 93512823627460899314915203)
  ·
    refine ⟨140269235441191348972372805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93512823627460899314915203 140269235441191348972372805)
    ·
      refine ⟨26300481645223377932319901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140269235441191348972372805 26300481645223377932319901)
      ·
        refine ⟨9862680616958766724619963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26300481645223377932319901 9862680616958766724619963)
        ·
          refine ⟨14794020925438150086929945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9862680616958766724619963 14794020925438150086929945)
          ·
            refine ⟨11095515694078612565197459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14794020925438150086929945 11095515694078612565197459)
            ·
              refine ⟨16643273541117918847796189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11095515694078612565197459 16643273541117918847796189)
              ·
                refine ⟨6241227577919219567923571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16643273541117918847796189 6241227577919219567923571)
                ·
                  refine ⟨9361841366878829351885357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6241227577919219567923571 9361841366878829351885357)
                  ·
                    refine ⟨3510690512579561006957009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9361841366878829351885357 3510690512579561006957009)
                    ·
                      refine ⟨2633017884434670755217757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3510690512579561006957009 2633017884434670755217757)
                      ·
                        rfl

theorem cell23_5127784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_5127784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127784 prefixEnd_5127784 := by exact prefixLift 5127784
  have htrace : WordTrace (prefixWord ++ tailWord_5127784) baseStart_5127784 baseEnd_5127784 := by
    simpa [prefixWord, tailWord_5127784, baseEnd_5127784] using wordTrace_append hprefix tailTrace_5127784
  have hstable : (prefixWord ++ tailWord_5127784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127784).length < 2 ^ (prefixWord ++ tailWord_5127784).sum := by decide
  have hdescent : baseEnd_5127784 < baseStart_5127784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127803 : List Nat := [1, 1, 1, 1, 1, 4, 6, 1, 7]
def baseStart_5127803 : Nat := 118140960795 + 5127803 * 2 ^ 59
def prefixEnd_5127803 : Nat := 4983230072969 + 3 ^ 40 * 5127803 * 2
def baseEnd_5127803 : Nat := 292558626729678464542241

theorem tailTrace_5127803 : CollatzResearch.WordTrace tailWord_5127803 prefixEnd_5127803 292558626729678464542241 := by
  unfold tailWord_5127803
  simp only [CollatzResearch.WordTrace]
  refine ⟨187026340241852964874772063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124684226827901976583181375 187026340241852964874772063)
  ·
    refine ⟨280539510362779447312158095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187026340241852964874772063 280539510362779447312158095)
    ·
      refine ⟨420809265544169170968237143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280539510362779447312158095 420809265544169170968237143)
      ·
        refine ⟨631213898316253756452355715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420809265544169170968237143 631213898316253756452355715)
        ·
          refine ⟨946820847474380634678533573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 631213898316253756452355715 946820847474380634678533573)
          ·
            refine ⟨177528908901446369002225045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 946820847474380634678533573 177528908901446369002225045)
            ·
              refine ⟨8321667604755298546979299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 177528908901446369002225045 8321667604755298546979299)
              ·
                refine ⟨12482501407132947820468949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8321667604755298546979299 12482501407132947820468949)
                ·
                  refine ⟨292558626729678464542241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12482501407132947820468949 292558626729678464542241)
                  ·
                    rfl

theorem cell23_5127803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 7].length) (baseStart_5127803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127803 prefixEnd_5127803 := by exact prefixLift 5127803
  have htrace : WordTrace (prefixWord ++ tailWord_5127803) baseStart_5127803 baseEnd_5127803 := by
    simpa [prefixWord, tailWord_5127803, baseEnd_5127803] using wordTrace_append hprefix tailTrace_5127803
  have hstable : (prefixWord ++ tailWord_5127803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127803).length < 2 ^ (prefixWord ++ tailWord_5127803).sum := by decide
  have hdescent : baseEnd_5127803 < baseStart_5127803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127843 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 5]
def baseStart_5127843 : Nat := 118140960795 + 5127843 * 2 ^ 59
def prefixEnd_5127843 : Nat := 4983230072969 + 3 ^ 40 * 5127843 * 2
def baseEnd_5127843 : Nat := 2633048179793286024379985

theorem tailTrace_5127843 : CollatzResearch.WordTrace tailWord_5127843 prefixEnd_5127843 2633048179793286024379985 := by
  unfold tailWord_5127843
  simp only [CollatzResearch.WordTrace]
  refine ⟨187027799161708051706228183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124685199441138701137485455 187027799161708051706228183)
  ·
    refine ⟨280541698742562077559342275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187027799161708051706228183 280541698742562077559342275)
    ·
      refine ⟨420812548113843116339013413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280541698742562077559342275 420812548113843116339013413)
      ·
        refine ⟨78902352771345584313565015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 420812548113843116339013413 78902352771345584313565015)
        ·
          refine ⟨118353529157018376470347523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78902352771345584313565015 118353529157018376470347523)
          ·
            refine ⟨177530293735527564705521285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118353529157018376470347523 177530293735527564705521285)
            ·
              refine ⟨33286930075411418382285241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177530293735527564705521285 33286930075411418382285241)
              ·
                refine ⟨24965197556558563786713931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33286930075411418382285241 24965197556558563786713931)
                ·
                  refine ⟨37447796334837845680070897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24965197556558563786713931 37447796334837845680070897)
                  ·
                    refine ⟨28085847251128384260053173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37447796334837845680070897 28085847251128384260053173)
                    ·
                      refine ⟨2633048179793286024379985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28085847251128384260053173 2633048179793286024379985)
                      ·
                        rfl

theorem cell23_5127843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_5127843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127843 prefixEnd_5127843 := by exact prefixLift 5127843
  have htrace : WordTrace (prefixWord ++ tailWord_5127843) baseStart_5127843 baseEnd_5127843 := by
    simpa [prefixWord, tailWord_5127843, baseEnd_5127843] using wordTrace_append hprefix tailTrace_5127843
  have hstable : (prefixWord ++ tailWord_5127843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127843).length < 2 ^ (prefixWord ++ tailWord_5127843).sum := by decide
  have hdescent : baseEnd_5127843 < baseStart_5127843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127854 : List Nat := [4, 1, 4, 1, 2, 2, 1, 1, 7]
def baseStart_5127854 : Nat := 118140960795 + 5127854 * 2 ^ 59
def prefixEnd_5127854 : Nat := 4983230072969 + 3 ^ 40 * 5127854 * 2
def baseEnd_5127854 : Nat := 292561536453387275704715

theorem tailTrace_5127854 : CollatzResearch.WordTrace tailWord_5127854 prefixEnd_5127854 292561536453387275704715 := by
  unfold tailWord_5127854
  simp only [CollatzResearch.WordTrace]
  refine ⟨23378525045583525073109827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124685466909778800389919077 23378525045583525073109827)
  ·
    refine ⟨35067787568375287609664741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23378525045583525073109827 35067787568375287609664741)
    ·
      refine ⟨6575210169070366426812139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35067787568375287609664741 6575210169070366426812139)
      ·
        refine ⟨9862815253605549640218209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6575210169070366426812139 9862815253605549640218209)
        ·
          refine ⟨7397111440204162230163657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9862815253605549640218209 7397111440204162230163657)
          ·
            refine ⟨5547833580153121672622743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7397111440204162230163657 5547833580153121672622743)
            ·
              refine ⟨8321750370229682508934115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5547833580153121672622743 8321750370229682508934115)
              ·
                refine ⟨12482625555344523763401173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8321750370229682508934115 12482625555344523763401173)
                ·
                  refine ⟨292561536453387275704715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12482625555344523763401173 292561536453387275704715)
                  ·
                    rfl

theorem cell23_5127854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_5127854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127854 prefixEnd_5127854 := by exact prefixLift 5127854
  have htrace : WordTrace (prefixWord ++ tailWord_5127854) baseStart_5127854 baseEnd_5127854 := by
    simpa [prefixWord, tailWord_5127854, baseEnd_5127854] using wordTrace_append hprefix tailTrace_5127854
  have hstable : (prefixWord ++ tailWord_5127854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127854).length < 2 ^ (prefixWord ++ tailWord_5127854).sum := by decide
  have hdescent : baseEnd_5127854 < baseStart_5127854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127880 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 5, 4]
def baseStart_5127880 : Nat := 118140960795 + 5127880 * 2 ^ 59
def prefixEnd_5127880 : Nat := 4983230072969 + 3 ^ 40 * 5127880 * 2
def baseEnd_5127880 : Nat := 877689059525834126539105

theorem tailTrace_5127880 : CollatzResearch.WordTrace tailWord_5127880 prefixEnd_5127880 877689059525834126539105 := by
  unfold tailWord_5127880
  simp only [CollatzResearch.WordTrace]
  refine ⟨93514574331287003512662547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124686099108382671350216729 93514574331287003512662547)
  ·
    refine ⟨140271861496930505268993821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93514574331287003512662547 140271861496930505268993821)
    ·
      refine ⟨52601948061348939475872683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140271861496930505268993821 52601948061348939475872683)
      ·
        refine ⟨78902922092023409213809025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52601948061348939475872683 78902922092023409213809025)
        ·
          refine ⟨59177191569017556910356769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78902922092023409213809025 59177191569017556910356769)
          ·
            refine ⟨44382893676763167682767577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59177191569017556910356769 44382893676763167682767577)
            ·
              refine ⟨33287170257572375762075683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44382893676763167682767577 33287170257572375762075683)
              ·
                refine ⟨49930755386358563643113525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33287170257572375762075683 49930755386358563643113525)
                ·
                  refine ⟨4681008317471115341541893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49930755386358563643113525 4681008317471115341541893)
                  ·
                    refine ⟨877689059525834126539105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4681008317471115341541893 877689059525834126539105)
                    ·
                      rfl

theorem cell23_5127880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_5127880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127880 prefixEnd_5127880 := by exact prefixLift 5127880
  have htrace : WordTrace (prefixWord ++ tailWord_5127880) baseStart_5127880 baseEnd_5127880 := by
    simpa [prefixWord, tailWord_5127880, baseEnd_5127880] using wordTrace_append hprefix tailTrace_5127880
  have hstable : (prefixWord ++ tailWord_5127880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127880).length < 2 ^ (prefixWord ++ tailWord_5127880).sum := by decide
  have hdescent : baseEnd_5127880 < baseStart_5127880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127883 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 4]
def baseStart_5127883 : Nat := 118140960795 + 5127883 * 2 ^ 59
def prefixEnd_5127883 : Nat := 4983230072969 + 3 ^ 40 * 5127883 * 2
def baseEnd_5127883 : Nat := 2633068719019465867879801

theorem tailTrace_5127883 : CollatzResearch.WordTrace tailWord_5127883 prefixEnd_5127883 2633068719019465867879801 := by
  unfold tailWord_5127883
  simp only [CollatzResearch.WordTrace]
  refine ⟨187029258081563138537684303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124686172054375425691789535 187029258081563138537684303)
  ·
    refine ⟨280543887122344707806526455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187029258081563138537684303 280543887122344707806526455)
    ·
      refine ⟨420815830683517061709789683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280543887122344707806526455 420815830683517061709789683)
      ·
        refine ⟨631223746025275592564684525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420815830683517061709789683 631223746025275592564684525)
        ·
          refine ⟨236708904759478347211756697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 631223746025275592564684525 236708904759478347211756697)
          ·
            refine ⟨177531678569608760408817523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236708904759478347211756697 177531678569608760408817523)
            ·
              refine ⟨266297517854413140613226285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177531678569608760408817523 266297517854413140613226285)
              ·
                refine ⟨99861569195404927729959857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266297517854413140613226285 99861569195404927729959857)
                ·
                  refine ⟨74896176896553695797469893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99861569195404927729959857 74896176896553695797469893)
                  ·
                    refine ⟨14043033168103817962025605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74896176896553695797469893 14043033168103817962025605)
                    ·
                      refine ⟨2633068719019465867879801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14043033168103817962025605 2633068719019465867879801)
                      ·
                        rfl

theorem cell23_5127883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 4].length) (baseStart_5127883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127883 prefixEnd_5127883 := by exact prefixLift 5127883
  have htrace : WordTrace (prefixWord ++ tailWord_5127883) baseStart_5127883 baseEnd_5127883 := by
    simpa [prefixWord, tailWord_5127883, baseEnd_5127883] using wordTrace_append hprefix tailTrace_5127883
  have hstable : (prefixWord ++ tailWord_5127883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127883).length < 2 ^ (prefixWord ++ tailWord_5127883).sum := by decide
  have hdescent : baseEnd_5127883 < baseStart_5127883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127913 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 1, 2, 6]
def baseStart_5127913 : Nat := 118140960795 + 5127913 * 2 ^ 59
def prefixEnd_5127913 : Nat := 4983230072969 + 3 ^ 40 * 5127913 * 2
def baseEnd_5127913 : Nat := 2633084123439100750504663

theorem tailTrace_5127913 : CollatzResearch.WordTrace tailWord_5127913 prefixEnd_5127913 2633084123439100750504663 := by
  unfold tailWord_5127913
  simp only [CollatzResearch.WordTrace]
  refine ⟨187030352271454453661276393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124686901514302969107517595 187030352271454453661276393)
  ·
    refine ⟨140272764203590840245957295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187030352271454453661276393 140272764203590840245957295)
    ·
      refine ⟨210409146305386260368935943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140272764203590840245957295 210409146305386260368935943)
      ·
        refine ⟨315613719458079390553403915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210409146305386260368935943 315613719458079390553403915)
        ·
          refine ⟨473420579187119085830105873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315613719458079390553403915 473420579187119085830105873)
          ·
            refine ⟨355065434390339314372579405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473420579187119085830105873 355065434390339314372579405)
            ·
              refine ⟨133149537896377242889717277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 355065434390339314372579405 133149537896377242889717277)
              ·
                refine ⟨49931076711141466083643979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133149537896377242889717277 49931076711141466083643979)
                ·
                  refine ⟨74896615066712199125465969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49931076711141466083643979 74896615066712199125465969)
                  ·
                    refine ⟨56172461300034149344099477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74896615066712199125465969 56172461300034149344099477)
                    ·
                      refine ⟨2633084123439100750504663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56172461300034149344099477 2633084123439100750504663)
                      ·
                        rfl

theorem cell23_5127913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_5127913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127913 prefixEnd_5127913 := by exact prefixLift 5127913
  have htrace : WordTrace (prefixWord ++ tailWord_5127913) baseStart_5127913 baseEnd_5127913 := by
    simpa [prefixWord, tailWord_5127913, baseEnd_5127913] using wordTrace_append hprefix tailTrace_5127913
  have hstable : (prefixWord ++ tailWord_5127913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127913).length < 2 ^ (prefixWord ++ tailWord_5127913).sum := by decide
  have hdescent : baseEnd_5127913 < baseStart_5127913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127937 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 5, 1, 3]
def baseStart_5127937 : Nat := 118140960795 + 5127937 * 2 ^ 59
def prefixEnd_5127937 : Nat := 4983230072969 + 3 ^ 40 * 5127937 * 2
def baseEnd_5127937 : Nat := 2633096446974808656604553

theorem tailTrace_5127937 : CollatzResearch.WordTrace tailWord_5127937 prefixEnd_5127937 2633096446974808656604553 := by
  unfold tailWord_5127937
  simp only [CollatzResearch.WordTrace]
  refine ⟨187031227623367505760150065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124687485082245003840100043 187031227623367505760150065)
  ·
    refine ⟨140273420717525629320112549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187031227623367505760150065 140273420717525629320112549)
    ·
      refine ⟨26301266384536055497521103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140273420717525629320112549 26301266384536055497521103)
      ·
        refine ⟨39451899576804083246281655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26301266384536055497521103 39451899576804083246281655)
        ·
          refine ⟨59177849365206124869422483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39451899576804083246281655 59177849365206124869422483)
          ·
            refine ⟨88766774047809187304133725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59177849365206124869422483 88766774047809187304133725)
            ·
              refine ⟨33287540267928445239050147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88766774047809187304133725 33287540267928445239050147)
              ·
                refine ⟨49931310401892667858575221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33287540267928445239050147 49931310401892667858575221)
                ·
                  refine ⟨4681060350177437611741427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49931310401892667858575221 4681060350177437611741427)
                  ·
                    refine ⟨7021590525266156417612141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4681060350177437611741427 7021590525266156417612141)
                    ·
                      refine ⟨2633096446974808656604553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7021590525266156417612141 2633096446974808656604553)
                      ·
                        rfl

theorem cell23_5127937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_5127937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127937 prefixEnd_5127937 := by exact prefixLift 5127937
  have htrace : WordTrace (prefixWord ++ tailWord_5127937) baseStart_5127937 baseEnd_5127937 := by
    simpa [prefixWord, tailWord_5127937, baseEnd_5127937] using wordTrace_append hprefix tailTrace_5127937
  have hstable : (prefixWord ++ tailWord_5127937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127937).length < 2 ^ (prefixWord ++ tailWord_5127937).sum := by decide
  have hdescent : baseEnd_5127937 < baseStart_5127937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127957 : List Nat := [1, 3, 2, 1, 2, 4, 1, 3, 1, 5]
def baseStart_5127957 : Nat := 118140960795 + 5127957 * 2 ^ 59
def prefixEnd_5127957 : Nat := 4983230072969 + 3 ^ 40 * 5127957 * 2
def baseEnd_5127957 : Nat := 877702238862632859451487

theorem tailTrace_5127957 : CollatzResearch.WordTrace tailWord_5127957 prefixEnd_5127957 877702238862632859451487 := by
  unfold tailWord_5127957
  simp only [CollatzResearch.WordTrace]
  refine ⟨187031957083295049175878125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124687971388863366117252083 187031957083295049175878125)
  ·
    refine ⟨70136983906235643440954297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187031957083295049175878125 70136983906235643440954297)
    ·
      refine ⟨52602737929676732580715723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70136983906235643440954297 52602737929676732580715723)
      ·
        refine ⟨78904106894515098871073585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52602737929676732580715723 78904106894515098871073585)
        ·
          refine ⟨59178080170886324153305189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78904106894515098871073585 59178080170886324153305189)
          ·
            refine ⟨11095890032041185778744723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59178080170886324153305189 11095890032041185778744723)
            ·
              refine ⟨16643835048061778668117085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11095890032041185778744723 16643835048061778668117085)
              ·
                refine ⟨6241438143023167000543907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16643835048061778668117085 6241438143023167000543907)
                ·
                  refine ⟨9362157214534750500815861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6241438143023167000543907 9362157214534750500815861)
                  ·
                    refine ⟨877702238862632859451487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9362157214534750500815861 877702238862632859451487)
                    ·
                      rfl

theorem cell23_5127957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_5127957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127957 prefixEnd_5127957 := by exact prefixLift 5127957
  have htrace : WordTrace (prefixWord ++ tailWord_5127957) baseStart_5127957 baseEnd_5127957 := by
    simpa [prefixWord, tailWord_5127957, baseEnd_5127957] using wordTrace_append hprefix tailTrace_5127957
  have hstable : (prefixWord ++ tailWord_5127957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127957).length < 2 ^ (prefixWord ++ tailWord_5127957).sum := by decide
  have hdescent : baseEnd_5127957 < baseStart_5127957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127980 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 5]
def baseStart_5127980 : Nat := 118140960795 + 5127980 * 2 ^ 59
def prefixEnd_5127980 : Nat := 4983230072969 + 3 ^ 40 * 5127980 * 2
def baseEnd_5127980 : Nat := 2633118526642951988366855

theorem tailTrace_5127980 : CollatzResearch.WordTrace tailWord_5127980 prefixEnd_5127980 2633118526642951988366855 := by
  unfold tailWord_5127980
  simp only [CollatzResearch.WordTrace]
  refine ⟨93516397981105862051982697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124688530641474482735976929 93516397981105862051982697)
  ·
    refine ⟨70137298485829396538987023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93516397981105862051982697 70137298485829396538987023)
    ·
      refine ⟨105205947728744094808480535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70137298485829396538987023 105205947728744094808480535)
      ·
        refine ⟨157808921593116142212720803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105205947728744094808480535 157808921593116142212720803)
        ·
          refine ⟨236713382389674213319081205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157808921593116142212720803 236713382389674213319081205)
          ·
            refine ⟨22191879599031957498663863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 236713382389674213319081205 22191879599031957498663863)
            ·
              refine ⟨33287819398547936247995795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22191879599031957498663863 33287819398547936247995795)
              ·
                refine ⟨49931729097821904371993693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33287819398547936247995795 49931729097821904371993693)
                ·
                  refine ⟨18724398411683214139497635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49931729097821904371993693 18724398411683214139497635)
                  ·
                    refine ⟨28086597617524821209246453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18724398411683214139497635 28086597617524821209246453)
                    ·
                      refine ⟨2633118526642951988366855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28086597617524821209246453 2633118526642951988366855)
                      ·
                        rfl

theorem cell23_5127980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_5127980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127980 prefixEnd_5127980 := by exact prefixLift 5127980
  have htrace : WordTrace (prefixWord ++ tailWord_5127980) baseStart_5127980 baseEnd_5127980 := by
    simpa [prefixWord, tailWord_5127980, baseEnd_5127980] using wordTrace_append hprefix tailTrace_5127980
  have hstable : (prefixWord ++ tailWord_5127980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127980).length < 2 ^ (prefixWord ++ tailWord_5127980).sum := by decide
  have hdescent : baseEnd_5127980 < baseStart_5127980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127994 : List Nat := [3, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4]
def baseStart_5127994 : Nat := 118140960795 + 5127994 * 2 ^ 59
def prefixEnd_5127994 : Nat := 4983230072969 + 3 ^ 40 * 5127994 * 2
def baseEnd_5127994 : Nat := 2633125715372114933591791

theorem tailTrace_5127994 : CollatzResearch.WordTrace tailWord_5127994 prefixEnd_5127994 2633125715372114933591791 := by
  unfold tailWord_5127994
  simp only [CollatzResearch.WordTrace]
  refine ⟨46758326646040251123743759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124688871056107336329983357 46758326646040251123743759)
  ·
    refine ⟨70137489969060376685615639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46758326646040251123743759 70137489969060376685615639)
    ·
      refine ⟨105206234953590565028423459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70137489969060376685615639 105206234953590565028423459)
      ·
        refine ⟨157809352430385847542635189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105206234953590565028423459 157809352430385847542635189)
        ·
          refine ⟨14794626790348673207122049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157809352430385847542635189 14794626790348673207122049)
          ·
            refine ⟨11095970092761504905341537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14794626790348673207122049 11095970092761504905341537)
            ·
              refine ⟨8321977569571128679006153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11095970092761504905341537 8321977569571128679006153)
              ·
                refine ⟨6241483177178346509254615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8321977569571128679006153 6241483177178346509254615)
                ·
                  refine ⟨9362224765767519763881923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6241483177178346509254615 9362224765767519763881923)
                  ·
                    refine ⟨14043337148651279645822885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9362224765767519763881923 14043337148651279645822885)
                    ·
                      refine ⟨2633125715372114933591791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14043337148651279645822885 2633125715372114933591791)
                      ·
                        rfl

theorem cell23_5127994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4].length) (baseStart_5127994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5127994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5127994 prefixEnd_5127994 := by exact prefixLift 5127994
  have htrace : WordTrace (prefixWord ++ tailWord_5127994) baseStart_5127994 baseEnd_5127994 := by
    simpa [prefixWord, tailWord_5127994, baseEnd_5127994] using wordTrace_append hprefix tailTrace_5127994
  have hstable : (prefixWord ++ tailWord_5127994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127994).length < 2 ^ (prefixWord ++ tailWord_5127994).sum := by decide
  have hdescent : baseEnd_5127994 < baseStart_5127994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128037 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 2, 7, 2]
def baseStart_5128037 : Nat := 118140960795 + 5128037 * 2 ^ 59
def prefixEnd_5128037 : Nat := 4983230072969 + 3 ^ 40 * 5128037 * 2
def baseEnd_5128037 : Nat := 2633147795040258265354093

theorem tailTrace_5128037 : CollatzResearch.WordTrace tailWord_5128037 prefixEnd_5128037 2633147795040258265354093 := by
  unfold tailWord_5128037
  simp only [CollatzResearch.WordTrace]
  refine ⟨187034874923005222838790365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124689916615336815225860243 187034874923005222838790365)
  ·
    refine ⟨70138078096126958564546387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187034874923005222838790365 70138078096126958564546387)
    ·
      refine ⟨105207117144190437846819581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70138078096126958564546387 105207117144190437846819581)
      ·
        refine ⟨39452668929071414192557343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105207117144190437846819581 39452668929071414192557343)
        ·
          refine ⟨59179003393607121288836015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39452668929071414192557343 59179003393607121288836015)
          ·
            refine ⟨88768505090410681933254023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59179003393607121288836015 88768505090410681933254023)
            ·
              refine ⟨133152757635616022899881035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88768505090410681933254023 133152757635616022899881035)
              ·
                refine ⟨199729136453424034349821553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133152757635616022899881035 199729136453424034349821553)
                ·
                  refine ⟨149796852340068025762366165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199729136453424034349821553 149796852340068025762366165)
                  ·
                    refine ⟨3510863726720344353805457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 149796852340068025762366165 3510863726720344353805457)
                    ·
                      refine ⟨2633147795040258265354093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3510863726720344353805457 2633147795040258265354093)
                      ·
                        rfl

theorem cell23_5128037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_5128037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128037 prefixEnd_5128037 := by exact prefixLift 5128037
  have htrace : WordTrace (prefixWord ++ tailWord_5128037) baseStart_5128037 baseEnd_5128037 := by
    simpa [prefixWord, tailWord_5128037, baseEnd_5128037] using wordTrace_append hprefix tailTrace_5128037
  have hstable : (prefixWord ++ tailWord_5128037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128037).length < 2 ^ (prefixWord ++ tailWord_5128037).sum := by decide
  have hdescent : baseEnd_5128037 < baseStart_5128037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128050 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_5128050 : Nat := 118140960795 + 5128050 * 2 ^ 59
def prefixEnd_5128050 : Nat := 4983230072969 + 3 ^ 40 * 5128050 * 2
def baseEnd_5128050 : Nat := 2633154470288766714491533

theorem tailTrace_5128050 : CollatzResearch.WordTrace tailWord_5128050 prefixEnd_5128050 2633154470288766714491533 := by
  unfold tailWord_5128050
  simp only [CollatzResearch.WordTrace]
  refine ⟨46758837267989531514753401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124690232714638750706009069 46758837267989531514753401)
  ·
    refine ⟨35069127950992148636065051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46758837267989531514753401 35069127950992148636065051)
    ·
      refine ⟨52603691926488222954097577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35069127950992148636065051 52603691926488222954097577)
      ·
        refine ⟨39452768944866167215573183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52603691926488222954097577 39452768944866167215573183)
        ·
          refine ⟨59179153417299250823359775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39452768944866167215573183 59179153417299250823359775)
          ·
            refine ⟨88768730125948876235039663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59179153417299250823359775 88768730125948876235039663)
            ·
              refine ⟨133153095188923314352559495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88768730125948876235039663 133153095188923314352559495)
              ·
                refine ⟨199729642783384971528839243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133153095188923314352559495 199729642783384971528839243)
                ·
                  refine ⟨299594464175077457293258865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 199729642783384971528839243 299594464175077457293258865)
                  ·
                    refine ⟨224695848131308092969944149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 299594464175077457293258865 224695848131308092969944149)
                    ·
                      refine ⟨2633154470288766714491533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 224695848131308092969944149 2633154470288766714491533)
                      ·
                        rfl

theorem cell23_5128050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_5128050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128050 prefixEnd_5128050 := by exact prefixLift 5128050
  have htrace : WordTrace (prefixWord ++ tailWord_5128050) baseStart_5128050 baseEnd_5128050 := by
    simpa [prefixWord, tailWord_5128050, baseEnd_5128050] using wordTrace_append hprefix tailTrace_5128050
  have hstable : (prefixWord ++ tailWord_5128050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128050).length < 2 ^ (prefixWord ++ tailWord_5128050).sum := by decide
  have hdescent : baseEnd_5128050 < baseStart_5128050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128060 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 6, 6]
def baseStart_5128060 : Nat := 118140960795 + 5128060 * 2 ^ 59
def prefixEnd_5128060 : Nat := 4983230072969 + 3 ^ 40 * 5128060 * 2
def baseEnd_5128060 : Nat := 877719868365103891788829

theorem tailTrace_5128060 : CollatzResearch.WordTrace tailWord_5128060 prefixEnd_5128060 877719868365103891788829 := by
  unfold tailWord_5128060
  simp only [CollatzResearch.WordTrace]
  refine ⟨93517856900960948883438817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124690475867947931844585089 93517856900960948883438817)
  ·
    refine ⟨70138392675720711662579113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93517856900960948883438817 70138392675720711662579113)
    ·
      refine ⟨52603794506790533746934335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70138392675720711662579113 52603794506790533746934335)
      ·
        refine ⟨78905691760185800620401503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52603794506790533746934335 78905691760185800620401503)
        ·
          refine ⟨118358537640278700930602255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78905691760185800620401503 118358537640278700930602255)
          ·
            refine ⟨177537806460418051395903383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118358537640278700930602255 177537806460418051395903383)
            ·
              refine ⟨266306709690627077093855075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177537806460418051395903383 266306709690627077093855075)
              ·
                refine ⟨399460064535940615640782613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266306709690627077093855075 399460064535940615640782613)
                ·
                  refine ⟨18724690525122216358161685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 399460064535940615640782613 18724690525122216358161685)
                  ·
                    refine ⟨877719868365103891788829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18724690525122216358161685 877719868365103891788829)
                    ·
                      rfl

theorem cell23_5128060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_5128060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128060 prefixEnd_5128060 := by exact prefixLift 5128060
  have htrace : WordTrace (prefixWord ++ tailWord_5128060) baseStart_5128060 baseEnd_5128060 := by
    simpa [prefixWord, tailWord_5128060, baseEnd_5128060] using wordTrace_append hprefix tailTrace_5128060
  have hstable : (prefixWord ++ tailWord_5128060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128060).length < 2 ^ (prefixWord ++ tailWord_5128060).sum := by decide
  have hdescent : baseEnd_5128060 < baseStart_5128060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128087 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 3]
def baseStart_5128087 : Nat := 118140960795 + 5128087 * 2 ^ 59
def prefixEnd_5128087 : Nat := 4983230072969 + 3 ^ 40 * 5128087 * 2
def baseEnd_5128087 : Nat := 2633173469072983069728863

theorem tailTrace_5128087 : CollatzResearch.WordTrace tailWord_5128087 prefixEnd_5128087 2633173469072983069728863 := by
  unfold tailWord_5128087
  simp only [CollatzResearch.WordTrace]
  refine ⟨187036698572824081378110515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124691132381882720918740343 187036698572824081378110515)
  ·
    refine ⟨280555047859236122067165773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187036698572824081378110515 280555047859236122067165773)
    ·
      refine ⟨105208142947213545775187165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280555047859236122067165773 105208142947213545775187165)
      ·
        refine ⟨39453053605205079665695187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105208142947213545775187165 39453053605205079665695187)
        ·
          refine ⟨59179580407807619498542781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39453053605205079665695187 59179580407807619498542781)
          ·
            refine ⟨22192342652927857311953543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59179580407807619498542781 22192342652927857311953543)
            ·
              refine ⟨33288513979391785967930315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22192342652927857311953543 33288513979391785967930315)
              ·
                refine ⟨49932770969087678951895473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33288513979391785967930315 49932770969087678951895473)
                ·
                  refine ⟨37449578226815759213921605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49932770969087678951895473 37449578226815759213921605)
                  ·
                    refine ⟨7021795917527954852610301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37449578226815759213921605 7021795917527954852610301)
                    ·
                      refine ⟨2633173469072983069728863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7021795917527954852610301 2633173469072983069728863)
                      ·
                        rfl

theorem cell23_5128087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_5128087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128087 prefixEnd_5128087 := by exact prefixLift 5128087
  have htrace : WordTrace (prefixWord ++ tailWord_5128087) baseStart_5128087 baseEnd_5128087 := by
    simpa [prefixWord, tailWord_5128087, baseEnd_5128087] using wordTrace_append hprefix tailTrace_5128087
  have hstable : (prefixWord ++ tailWord_5128087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128087).length < 2 ^ (prefixWord ++ tailWord_5128087).sum := by decide
  have hdescent : baseEnd_5128087 < baseStart_5128087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128174 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_5128174 : Nat := 118140960795 + 5128174 * 2 ^ 59
def prefixEnd_5128174 : Nat := 4983230072969 + 3 ^ 40 * 5128174 * 2
def baseEnd_5128174 : Nat := 2633218141889924229340963

theorem tailTrace_5128174 : CollatzResearch.WordTrace tailWord_5128174 prefixEnd_5128174 2633218141889924229340963 := by
  unfold tailWord_5128174
  simp only [CollatzResearch.WordTrace]
  refine ⟨23379983965438611904565947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124693247815672596824351717 23379983965438611904565947)
  ·
    refine ⟨35069975948157917856848921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23379983965438611904565947 35069975948157917856848921)
    ·
      refine ⟨26302481961118438392636691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35069975948157917856848921 26302481961118438392636691)
      ·
        refine ⟨39453722941677657588955037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26302481961118438392636691 39453722941677657588955037)
        ·
          refine ⟨14795146103129121595858139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39453722941677657588955037 14795146103129121595858139)
          ·
            refine ⟨22192719154693682393787209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14795146103129121595858139 22192719154693682393787209)
            ·
              refine ⟨16644539366020261795340407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22192719154693682393787209 16644539366020261795340407)
              ·
                refine ⟨24966809049030392693010611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16644539366020261795340407 24966809049030392693010611)
                ·
                  refine ⟨37450213573545589039515917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24966809049030392693010611 37450213573545589039515917)
                  ·
                    refine ⟨14043830090079595889818469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37450213573545589039515917 14043830090079595889818469)
                    ·
                      refine ⟨2633218141889924229340963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14043830090079595889818469 2633218141889924229340963)
                      ·
                        rfl

theorem cell23_5128174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_5128174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128174 prefixEnd_5128174 := by exact prefixLift 5128174
  have htrace : WordTrace (prefixWord ++ tailWord_5128174) baseStart_5128174 baseEnd_5128174 := by
    simpa [prefixWord, tailWord_5128174, baseEnd_5128174] using wordTrace_append hprefix tailTrace_5128174
  have hstable : (prefixWord ++ tailWord_5128174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128174).length < 2 ^ (prefixWord ++ tailWord_5128174).sum := by decide
  have hdescent : baseEnd_5128174 < baseStart_5128174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128197 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 8]
def baseStart_5128197 : Nat := 118140960795 + 5128197 * 2 ^ 59
def prefixEnd_5128197 : Nat := 4983230072969 + 3 ^ 40 * 5128197 * 2
def baseEnd_5128197 : Nat := 292581105771664182150373

theorem tailTrace_5128197 : CollatzResearch.WordTrace tailWord_5128197 prefixEnd_5128197 292581105771664182150373 := by
  unfold tailWord_5128197
  simp only [CollatzResearch.WordTrace]
  refine ⟨187040710602425570164614845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124693807068283713443076563 187040710602425570164614845)
  ·
    refine ⟨70140266475909588811730567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187040710602425570164614845 70140266475909588811730567)
    ·
      refine ⟨105210399713864383217595851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70140266475909588811730567 105210399713864383217595851)
      ·
        refine ⟨157815599570796574826393777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105210399713864383217595851 157815599570796574826393777)
        ·
          refine ⟨118361699678097431119795333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157815599570796574826393777 118361699678097431119795333)
          ·
            refine ⟨22192818689643268334961625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118361699678097431119795333 22192818689643268334961625)
            ·
              refine ⟨16644614017232451251221219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22192818689643268334961625 16644614017232451251221219)
              ·
                refine ⟨24966921025848676876831829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16644614017232451251221219 24966921025848676876831829)
                ·
                  refine ⟨292581105771664182150373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24966921025848676876831829 292581105771664182150373)
                  ·
                    rfl

theorem cell23_5128197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 8].length) (baseStart_5128197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128197 prefixEnd_5128197 := by exact prefixLift 5128197
  have htrace : WordTrace (prefixWord ++ tailWord_5128197) baseStart_5128197 baseEnd_5128197 := by
    simpa [prefixWord, tailWord_5128197, baseEnd_5128197] using wordTrace_append hprefix tailTrace_5128197
  have hstable : (prefixWord ++ tailWord_5128197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128197).length < 2 ^ (prefixWord ++ tailWord_5128197).sum := by decide
  have hdescent : baseEnd_5128197 < baseStart_5128197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128228 : List Nat := [2, 3, 1, 4, 2, 1, 2, 1, 2, 2, 3]
def baseStart_5128228 : Nat := 118140960795 + 5128228 * 2 ^ 59
def prefixEnd_5128228 : Nat := 4983230072969 + 3 ^ 40 * 5128228 * 2
def baseEnd_5128228 : Nat := 2633245869845267018065715

theorem tailTrace_5128228 : CollatzResearch.WordTrace tailWord_5128228 prefixEnd_5128228 2633245869845267018065715 := by
  unfold tailWord_5128228
  simp only [CollatzResearch.WordTrace]
  refine ⟨93520920632656631229496669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124694560843542174972662225 93520920632656631229496669)
  ·
    refine ⟨35070345237246236711061251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93520920632656631229496669 35070345237246236711061251)
    ·
      refine ⟨52605517855869355066591877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35070345237246236711061251 52605517855869355066591877)
      ·
        refine ⟨9863534597975504074985977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52605517855869355066591877 9863534597975504074985977)
        ·
          refine ⟨7397650948481628056239483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9863534597975504074985977 7397650948481628056239483)
          ·
            refine ⟨11096476422722442084359225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7397650948481628056239483 11096476422722442084359225)
            ·
              refine ⟨8322357317041831563269419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11096476422722442084359225 8322357317041831563269419)
              ·
                refine ⟨12483535975562747344904129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8322357317041831563269419 12483535975562747344904129)
                ·
                  refine ⟨9362651981672060508678097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12483535975562747344904129 9362651981672060508678097)
                  ·
                    refine ⟨7021988986254045381508573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9362651981672060508678097 7021988986254045381508573)
                    ·
                      refine ⟨2633245869845267018065715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7021988986254045381508573 2633245869845267018065715)
                      ·
                        rfl

theorem cell23_5128228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_5128228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128228 prefixEnd_5128228 := by exact prefixLift 5128228
  have htrace : WordTrace (prefixWord ++ tailWord_5128228) baseStart_5128228 baseEnd_5128228 := by
    simpa [prefixWord, tailWord_5128228, baseEnd_5128228] using wordTrace_append hprefix tailTrace_5128228
  have hstable : (prefixWord ++ tailWord_5128228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128228).length < 2 ^ (prefixWord ++ tailWord_5128228).sum := by decide
  have hdescent : baseEnd_5128228 < baseStart_5128228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128278 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_5128278 : Nat := 118140960795 + 5128278 * 2 ^ 59
def prefixEnd_5128278 : Nat := 4983230072969 + 3 ^ 40 * 5128278 * 2
def baseEnd_5128278 : Nat := 877757181292663940813495

theorem tailTrace_5128278 : CollatzResearch.WordTrace tailWord_5128278 prefixEnd_5128278 877757181292663940813495 := by
  unfold tailWord_5128278
  simp only [CollatzResearch.WordTrace]
  refine ⟨11690229057195757562394593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124695776610088080665542325 11690229057195757562394593)
  ·
    refine ⟨8767671792896818171795945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11690229057195757562394593 8767671792896818171795945)
    ·
      refine ⟨6575753844672613628846959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8767671792896818171795945 6575753844672613628846959)
      ·
        refine ⟨9863630767008920443270439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6575753844672613628846959 9863630767008920443270439)
        ·
          refine ⟨14795446150513380664905659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9863630767008920443270439 14795446150513380664905659)
          ·
            refine ⟨22193169225770070997358489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14795446150513380664905659 22193169225770070997358489)
            ·
              refine ⟨16644876919327553248018867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22193169225770070997358489 16644876919327553248018867)
              ·
                refine ⟨24967315378991329872028301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16644876919327553248018867 24967315378991329872028301)
                ·
                  refine ⟨9362743267121748702010613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24967315378991329872028301 9362743267121748702010613)
                  ·
                    refine ⟨877757181292663940813495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9362743267121748702010613 877757181292663940813495)
                    ·
                      rfl

theorem cell23_5128278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_5128278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128278 prefixEnd_5128278 := by exact prefixLift 5128278
  have htrace : WordTrace (prefixWord ++ tailWord_5128278) baseStart_5128278 baseEnd_5128278 := by
    simpa [prefixWord, tailWord_5128278, baseEnd_5128278] using wordTrace_append hprefix tailTrace_5128278
  have hstable : (prefixWord ++ tailWord_5128278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128278).length < 2 ^ (prefixWord ++ tailWord_5128278).sum := by decide
  have hdescent : baseEnd_5128278 < baseStart_5128278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128285 : List Nat := [1, 4, 4, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_5128285 : Nat := 118140960795 + 5128285 * 2 ^ 59
def prefixEnd_5128285 : Nat := 4983230072969 + 3 ^ 40 * 5128285 * 2
def baseEnd_5128285 : Nat := 2633275138242573295052953

theorem tailTrace_5128285 : CollatzResearch.WordTrace tailWord_5128285 prefixEnd_5128285 2633275138242573295052953 := by
  unfold tailWord_5128285
  simp only [CollatzResearch.WordTrace]
  refine ⟨187043920226106761193818309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124695946817404507462545539 187043920226106761193818309)
  ·
    refine ⟨35070735042395017723840933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187043920226106761193818309 35070735042395017723840933)
    ·
      refine ⟨6575762820449065823220175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35070735042395017723840933 6575762820449065823220175)
      ·
        refine ⟨9863644230673598734830263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6575762820449065823220175 9863644230673598734830263)
        ·
          refine ⟨14795466346010398102245395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9863644230673598734830263 14795466346010398102245395)
          ·
            refine ⟨22193199519015597153368093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14795466346010398102245395 22193199519015597153368093)
            ·
              refine ⟨8322449819630848932513035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22193199519015597153368093 8322449819630848932513035)
              ·
                refine ⟨12483674729446273398769553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8322449819630848932513035 12483674729446273398769553)
                ·
                  refine ⟨9362756047084705049077165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12483674729446273398769553 9362756047084705049077165)
                  ·
                    refine ⟨3511033517656764393403937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9362756047084705049077165 3511033517656764393403937)
                    ·
                      refine ⟨2633275138242573295052953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3511033517656764393403937 2633275138242573295052953)
                      ·
                        rfl

theorem cell23_5128285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_5128285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128285 prefixEnd_5128285 := by exact prefixLift 5128285
  have htrace : WordTrace (prefixWord ++ tailWord_5128285) baseStart_5128285 baseEnd_5128285 := by
    simpa [prefixWord, tailWord_5128285, baseEnd_5128285] using wordTrace_append hprefix tailTrace_5128285
  have hstable : (prefixWord ++ tailWord_5128285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128285).length < 2 ^ (prefixWord ++ tailWord_5128285).sum := by decide
  have hdescent : baseEnd_5128285 < baseStart_5128285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128298 : List Nat := [3, 1, 3, 2, 3, 1, 1, 3, 1, 1, 4]
def baseStart_5128298 : Nat := 118140960795 + 5128298 * 2 ^ 59
def prefixEnd_5128298 : Nat := 4983230072969 + 3 ^ 40 * 5128298 * 2
def baseEnd_5128298 : Nat := 2633281813491081744190393

theorem tailTrace_5128298 : CollatzResearch.WordTrace tailWord_5128298 prefixEnd_5128298 2633281813491081744190393 := by
  unfold tailWord_5128298
  simp only [CollatzResearch.WordTrace]
  refine ⟨46761098593764916103510387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124696262916706442942694365 46761098593764916103510387)
  ·
    refine ⟨70141647890647374155265581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46761098593764916103510387 70141647890647374155265581)
    ·
      refine ⟨26303117958992765308224593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70141647890647374155265581 26303117958992765308224593)
      ·
        refine ⟨19727338469244573981168445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26303117958992765308224593 19727338469244573981168445)
        ·
          refine ⟨7397751925966715242938167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19727338469244573981168445 7397751925966715242938167)
          ·
            refine ⟨11096627888950072864407251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7397751925966715242938167 11096627888950072864407251)
            ·
              refine ⟨16644941833425109296610877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11096627888950072864407251 16644941833425109296610877)
              ·
                refine ⟨6241853187534415986229079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16644941833425109296610877 6241853187534415986229079)
                ·
                  refine ⟨9362779781301623979343619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6241853187534415986229079 9362779781301623979343619)
                  ·
                    refine ⟨14044169671952435969015429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9362779781301623979343619 14044169671952435969015429)
                    ·
                      refine ⟨2633281813491081744190393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14044169671952435969015429 2633281813491081744190393)
                      ·
                        rfl

theorem cell23_5128298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_5128298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128298 prefixEnd_5128298 := by exact prefixLift 5128298
  have htrace : WordTrace (prefixWord ++ tailWord_5128298) baseStart_5128298 baseEnd_5128298 := by
    simpa [prefixWord, tailWord_5128298, baseEnd_5128298] using wordTrace_append hprefix tailTrace_5128298
  have hstable : (prefixWord ++ tailWord_5128298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128298).length < 2 ^ (prefixWord ++ tailWord_5128298).sum := by decide
  have hdescent : baseEnd_5128298 < baseStart_5128298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128328 : List Nat := [2, 1, 3, 4, 1, 3, 1, 1, 1, 2, 4]
def baseStart_5128328 : Nat := 118140960795 + 5128328 * 2 ^ 59
def prefixEnd_5128328 : Nat := 4983230072969 + 3 ^ 40 * 5128328 * 2
def baseEnd_5128328 : Nat := 2633297217910716626815255

theorem tailTrace_5128328 : CollatzResearch.WordTrace tailWord_5128328 prefixEnd_5128328 2633297217910716626815255 := by
  unfold tailWord_5128328
  simp only [CollatzResearch.WordTrace]
  refine ⟨93522744282475489768816819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124696992376633986358422425 93522744282475489768816819)
  ·
    refine ⟨140284116423713234653225229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93522744282475489768816819 140284116423713234653225229)
    ·
      refine ⟨52606543658892462994959461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140284116423713234653225229 52606543658892462994959461)
      ·
        refine ⟨9863726936042336811554899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52606543658892462994959461 9863726936042336811554899)
        ·
          refine ⟨14795590404063505217332349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9863726936042336811554899 14795590404063505217332349)
          ·
            refine ⟨5548346401523814456499631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14795590404063505217332349 5548346401523814456499631)
            ·
              refine ⟨8322519602285721684749447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5548346401523814456499631 8322519602285721684749447)
              ·
                refine ⟨12483779403428582527124171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8322519602285721684749447 12483779403428582527124171)
                ·
                  refine ⟨18725669105142873790686257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12483779403428582527124171 18725669105142873790686257)
                  ·
                    refine ⟨14044251828857155343014693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18725669105142873790686257 14044251828857155343014693)
                    ·
                      refine ⟨2633297217910716626815255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14044251828857155343014693 2633297217910716626815255)
                      ·
                        rfl

theorem cell23_5128328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_5128328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128328 prefixEnd_5128328 := by exact prefixLift 5128328
  have htrace : WordTrace (prefixWord ++ tailWord_5128328) baseStart_5128328 baseEnd_5128328 := by
    simpa [prefixWord, tailWord_5128328, baseEnd_5128328] using wordTrace_append hprefix tailTrace_5128328
  have hstable : (prefixWord ++ tailWord_5128328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128328).length < 2 ^ (prefixWord ++ tailWord_5128328).sum := by decide
  have hdescent : baseEnd_5128328 < baseStart_5128328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128366 : List Nat := [4, 1, 4, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_5128366 : Nat := 118140960795 + 5128366 * 2 ^ 59
def prefixEnd_5128366 : Nat := 4983230072969 + 3 ^ 40 * 5128366 * 2
def baseEnd_5128366 : Nat := 2633316730175587478140081

theorem tailTrace_5128366 : CollatzResearch.WordTrace tailWord_5128366 prefixEnd_5128366 2633316730175587478140081 := by
  unfold tailWord_5128366
  simp only [CollatzResearch.WordTrace]
  refine ⟨23380859317351664003439619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124697916359208874685011301 23380859317351664003439619)
  ·
    refine ⟨35071288976027496005159429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23380859317351664003439619 35071288976027496005159429)
    ·
      refine ⟨6575866683005155500967393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35071288976027496005159429 6575866683005155500967393)
      ·
        refine ⟨4931900012253866625725545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6575866683005155500967393 4931900012253866625725545)
        ·
          refine ⟨3698925009190399969294159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4931900012253866625725545 3698925009190399969294159)
          ·
            refine ⟨5548387513785599953941239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3698925009190399969294159 5548387513785599953941239)
            ·
              refine ⟨8322581270678399930911859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5548387513785599953941239 8322581270678399930911859)
              ·
                refine ⟨12483871906017599896367789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8322581270678399930911859 12483871906017599896367789)
                ·
                  refine ⟨4681451964756599961137921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12483871906017599896367789 4681451964756599961137921)
                  ·
                    refine ⟨3511088973567449970853441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4681451964756599961137921 3511088973567449970853441)
                    ·
                      refine ⟨2633316730175587478140081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3511088973567449970853441 2633316730175587478140081)
                      ·
                        rfl

theorem cell23_5128366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_5128366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128366 prefixEnd_5128366 := by exact prefixLift 5128366
  have htrace : WordTrace (prefixWord ++ tailWord_5128366) baseStart_5128366 baseEnd_5128366 := by
    simpa [prefixWord, tailWord_5128366, baseEnd_5128366] using wordTrace_append hprefix tailTrace_5128366
  have hstable : (prefixWord ++ tailWord_5128366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128366).length < 2 ^ (prefixWord ++ tailWord_5128366).sum := by decide
  have hdescent : baseEnd_5128366 < baseStart_5128366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128394 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 9]
def baseStart_5128394 : Nat := 118140960795 + 5128394 * 2 ^ 59
def prefixEnd_5128394 : Nat := 4983230072969 + 3 ^ 40 * 5128394 * 2
def baseEnd_5128394 : Nat := 292592345292657040954439

theorem tailTrace_5128394 : CollatzResearch.WordTrace tailWord_5128394 prefixEnd_5128394 292592345292657040954439 := by
  unfold tailWord_5128394
  simp only [CollatzResearch.WordTrace]
  refine ⟨46761973945677968202384059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124698597188474581873024157 46761973945677968202384059)
  ·
    refine ⟨70142960918516952303576089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46761973945677968202384059 70142960918516952303576089)
    ·
      refine ⟨52607220688887714227682067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70142960918516952303576089 52607220688887714227682067)
      ·
        refine ⟨78910831033331571341523101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52607220688887714227682067 78910831033331571341523101)
        ·
          refine ⟨29591561637499339253071163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78910831033331571341523101 29591561637499339253071163)
          ·
            refine ⟨44387342456249008879606745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29591561637499339253071163 44387342456249008879606745)
            ·
              refine ⟨33290506842186756659705059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44387342456249008879606745 33290506842186756659705059)
              ·
                refine ⟨49935760263280134989557589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33290506842186756659705059 49935760263280134989557589)
                ·
                  refine ⟨292592345292657040954439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49935760263280134989557589 292592345292657040954439)
                  ·
                    rfl

theorem cell23_5128394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 9].length) (baseStart_5128394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128394 prefixEnd_5128394 := by exact prefixLift 5128394
  have htrace : WordTrace (prefixWord ++ tailWord_5128394) baseStart_5128394 baseEnd_5128394 := by
    simpa [prefixWord, tailWord_5128394, baseEnd_5128394] using wordTrace_append hprefix tailTrace_5128394
  have hstable : (prefixWord ++ tailWord_5128394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128394).length < 2 ^ (prefixWord ++ tailWord_5128394).sum := by decide
  have hdescent : baseEnd_5128394 < baseStart_5128394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128405 : List Nat := [1, 3, 2, 4, 2, 1, 1, 2, 1, 4, 2]
def baseStart_5128405 : Nat := 118140960795 + 5128405 * 2 ^ 59
def prefixEnd_5128405 : Nat := 4983230072969 + 3 ^ 40 * 5128405 * 2
def baseEnd_5128405 : Nat := 2633336755921112825552401

theorem tailTrace_5128405 : CollatzResearch.WordTrace tailWord_5128405 prefixEnd_5128405 2633336755921112825552401 := by
  unfold tailWord_5128405
  simp only [CollatzResearch.WordTrace]
  refine ⟨187048296985672021688186669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124698864657114681125457779 187048296985672021688186669)
  ·
    refine ⟨70143111369627008133070001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187048296985672021688186669 70143111369627008133070001)
    ·
      refine ⟨52607333527220256099802501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70143111369627008133070001 52607333527220256099802501)
      ·
        refine ⟨9863875036353798018712969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52607333527220256099802501 9863875036353798018712969)
        ·
          refine ⟨7397906277265348514034727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9863875036353798018712969 7397906277265348514034727)
          ·
            refine ⟨11096859415898022771052091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7397906277265348514034727 11096859415898022771052091)
            ·
              refine ⟨16645289123847034156578137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11096859415898022771052091 16645289123847034156578137)
              ·
                refine ⟨12483966842885275617433603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16645289123847034156578137 12483966842885275617433603)
                ·
                  refine ⟨18725950264327913426150405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12483966842885275617433603 18725950264327913426150405)
                  ·
                    refine ⟨3511115674561483767403201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18725950264327913426150405 3511115674561483767403201)
                    ·
                      refine ⟨2633336755921112825552401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3511115674561483767403201 2633336755921112825552401)
                      ·
                        rfl

theorem cell23_5128405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_5128405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128405 prefixEnd_5128405 := by exact prefixLift 5128405
  have htrace : WordTrace (prefixWord ++ tailWord_5128405) baseStart_5128405 baseEnd_5128405 := by
    simpa [prefixWord, tailWord_5128405, baseEnd_5128405] using wordTrace_append hprefix tailTrace_5128405
  have hstable : (prefixWord ++ tailWord_5128405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128405).length < 2 ^ (prefixWord ++ tailWord_5128405).sum := by decide
  have hdescent : baseEnd_5128405 < baseStart_5128405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128511 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 3]
def baseStart_5128511 : Nat := 118140960795 + 5128511 * 2 ^ 59
def prefixEnd_5128511 : Nat := 4983230072969 + 3 ^ 40 * 5128511 * 2
def baseEnd_5128511 : Nat := 2633391184870489410826913

theorem tailTrace_5128511 : CollatzResearch.WordTrace tailWord_5128511 prefixEnd_5128511 2633391184870489410826913 := by
  unfold tailWord_5128511
  simp only [CollatzResearch.WordTrace]
  refine ⟨187052163123288001791545387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124701442082192001194363591 187052163123288001791545387)
  ·
    refine ⟨280578244684932002687318081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187052163123288001791545387 280578244684932002687318081)
    ·
      refine ⟨210433683513699002015488561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280578244684932002687318081 210433683513699002015488561)
      ·
        refine ⟨157825262635274251511616421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210433683513699002015488561 157825262635274251511616421)
        ·
          refine ⟨29592236744113922158428079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157825262635274251511616421 29592236744113922158428079)
          ·
            refine ⟨44388355116170883237642119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29592236744113922158428079 44388355116170883237642119)
            ·
              refine ⟨66582532674256324856463179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44388355116170883237642119 66582532674256324856463179)
              ·
                refine ⟨99873799011384487284694769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66582532674256324856463179 99873799011384487284694769)
                ·
                  refine ⟨74905349258538365463521077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99873799011384487284694769 74905349258538365463521077)
                  ·
                    refine ⟨7022376492987971762205101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74905349258538365463521077 7022376492987971762205101)
                    ·
                      refine ⟨2633391184870489410826913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7022376492987971762205101 2633391184870489410826913)
                      ·
                        rfl

theorem cell23_5128511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_5128511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128511 prefixEnd_5128511 := by exact prefixLift 5128511
  have htrace : WordTrace (prefixWord ++ tailWord_5128511) baseStart_5128511 baseEnd_5128511 := by
    simpa [prefixWord, tailWord_5128511, baseEnd_5128511] using wordTrace_append hprefix tailTrace_5128511
  have hstable : (prefixWord ++ tailWord_5128511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128511).length < 2 ^ (prefixWord ++ tailWord_5128511).sum := by decide
  have hdescent : baseEnd_5128511 < baseStart_5128511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128561 : List Nat := [1, 2, 2, 2, 1, 2, 1, 5, 1, 6]
def baseStart_5128561 : Nat := 118140960795 + 5128561 * 2 ^ 59
def prefixEnd_5128561 : Nat := 4983230072969 + 3 ^ 40 * 5128561 * 2
def baseEnd_5128561 : Nat := 877805619634404738400561

theorem tailTrace_5128561 : CollatzResearch.WordTrace tailWord_5128561 prefixEnd_5128561 877805619634404738400561 := by
  unfold tailWord_5128561
  simp only [CollatzResearch.WordTrace]
  refine ⟨187053986773106860330865537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124702657848737906887243691 187053986773106860330865537)
  ·
    refine ⟨140290490079830145248149153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187053986773106860330865537 140290490079830145248149153)
    ·
      refine ⟨105217867559872608936111865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140290490079830145248149153 105217867559872608936111865)
      ·
        refine ⟨78913400669904456702083899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105217867559872608936111865 78913400669904456702083899)
        ·
          refine ⟨118370101004856685053125849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78913400669904456702083899 118370101004856685053125849)
          ·
            refine ⟨88777575753642513789844387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118370101004856685053125849 88777575753642513789844387)
            ·
              refine ⟨133166363630463770684766581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88777575753642513789844387 133166363630463770684766581)
              ·
                refine ⟨12484346590355978501696867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133166363630463770684766581 12484346590355978501696867)
                ·
                  refine ⟨18726519885533967752545301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12484346590355978501696867 18726519885533967752545301)
                  ·
                    refine ⟨877805619634404738400561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18726519885533967752545301 877805619634404738400561)
                    ·
                      rfl

theorem cell23_5128561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_5128561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128561 prefixEnd_5128561 := by exact prefixLift 5128561
  have htrace : WordTrace (prefixWord ++ tailWord_5128561) baseStart_5128561 baseEnd_5128561 := by
    simpa [prefixWord, tailWord_5128561, baseEnd_5128561] using wordTrace_append hprefix tailTrace_5128561
  have hstable : (prefixWord ++ tailWord_5128561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128561).length < 2 ^ (prefixWord ++ tailWord_5128561).sum := by decide
  have hdescent : baseEnd_5128561 < baseStart_5128561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128565 : List Nat := [1, 3, 4, 1, 2, 1, 3, 2, 1, 5]
def baseStart_5128565 : Nat := 118140960795 + 5128565 * 2 ^ 59
def prefixEnd_5128565 : Nat := 4983230072969 + 3 ^ 40 * 5128565 * 2
def baseEnd_5128565 : Nat := 877806304275277399850555

theorem tailTrace_5128565 : CollatzResearch.WordTrace tailWord_5128565 prefixEnd_5128565 877806304275277399850555 := by
  unfold tailWord_5128565
  simp only [CollatzResearch.WordTrace]
  refine ⟨187054132665092369014011149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124702755110061579342674099 187054132665092369014011149)
  ·
    refine ⟨70145299749409638380254181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187054132665092369014011149 70145299749409638380254181)
    ·
      refine ⟨13152243703014307196297659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70145299749409638380254181 13152243703014307196297659)
      ·
        refine ⟨19728365554521460794446489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13152243703014307196297659 19728365554521460794446489)
        ·
          refine ⟨14796274165891095595834867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19728365554521460794446489 14796274165891095595834867)
          ·
            refine ⟨22194411248836643393752301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14796274165891095595834867 22194411248836643393752301)
            ·
              refine ⟨8322904218313741272657113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22194411248836643393752301 8322904218313741272657113)
              ·
                refine ⟨6242178163735305954492835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8322904218313741272657113 6242178163735305954492835)
                ·
                  refine ⟨9363267245602958931739253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6242178163735305954492835 9363267245602958931739253)
                  ·
                    refine ⟨877806304275277399850555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9363267245602958931739253 877806304275277399850555)
                    ·
                      rfl

theorem cell23_5128565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_5128565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128565 prefixEnd_5128565 := by exact prefixLift 5128565
  have htrace : WordTrace (prefixWord ++ tailWord_5128565) baseStart_5128565 baseEnd_5128565 := by
    simpa [prefixWord, tailWord_5128565, baseEnd_5128565] using wordTrace_append hprefix tailTrace_5128565
  have hstable : (prefixWord ++ tailWord_5128565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128565).length < 2 ^ (prefixWord ++ tailWord_5128565).sum := by decide
  have hdescent : baseEnd_5128565 < baseStart_5128565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128588 : List Nat := [2, 2, 1, 2, 1, 4, 3, 1, 1, 1, 5]
def baseStart_5128588 : Nat := 118140960795 + 5128588 * 2 ^ 59
def prefixEnd_5128588 : Nat := 4983230072969 + 3 ^ 40 * 5128588 * 2
def baseEnd_5128588 : Nat := 2633430722880885609564059

theorem tailTrace_5128588 : CollatzResearch.WordTrace tailWord_5128588 prefixEnd_5128588 2633430722880885609564059 := by
  unfold tailWord_5128588
  simp only [CollatzResearch.WordTrace]
  refine ⟨93527485772004521971049209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124703314362672695961398945 93527485772004521971049209)
  ·
    refine ⟨70145614329003391478286907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93527485772004521971049209 70145614329003391478286907)
    ·
      refine ⟨105218421493505087217430361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70145614329003391478286907 105218421493505087217430361)
      ·
        refine ⟨78913816120128815413072771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105218421493505087217430361 78913816120128815413072771)
        ·
          refine ⟨118370724180193223119609157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78913816120128815413072771 118370724180193223119609157)
          ·
            refine ⟨22194510783786229334926717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118370724180193223119609157 22194510783786229334926717)
            ·
              refine ⟨8322941543919836000597519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22194510783786229334926717 8322941543919836000597519)
              ·
                refine ⟨12484412315879754000896279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8322941543919836000597519 12484412315879754000896279)
                ·
                  refine ⟨18726618473819631001344419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12484412315879754000896279 18726618473819631001344419)
                  ·
                    refine ⟨28089927710729446502016629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18726618473819631001344419 28089927710729446502016629)
                    ·
                      refine ⟨2633430722880885609564059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28089927710729446502016629 2633430722880885609564059)
                      ·
                        rfl

theorem cell23_5128588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_5128588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128588 prefixEnd_5128588 := by exact prefixLift 5128588
  have htrace : WordTrace (prefixWord ++ tailWord_5128588) baseStart_5128588 baseEnd_5128588 := by
    simpa [prefixWord, tailWord_5128588, baseEnd_5128588] using wordTrace_append hprefix tailTrace_5128588
  have hstable : (prefixWord ++ tailWord_5128588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128588).length < 2 ^ (prefixWord ++ tailWord_5128588).sum := by decide
  have hdescent : baseEnd_5128588 < baseStart_5128588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128608 : List Nat := [2, 1, 1, 4, 1, 5, 1, 8]
def baseStart_5128608 : Nat := 118140960795 + 5128608 * 2 ^ 59
def prefixEnd_5128608 : Nat := 4983230072969 + 3 ^ 40 * 5128608 * 2
def baseEnd_5128608 : Nat := 97534851573850945604221

theorem tailTrace_5128608 : CollatzResearch.WordTrace tailWord_5128608 prefixEnd_5128608 97534851573850945604221 := by
  unfold tailWord_5128608
  simp only [CollatzResearch.WordTrace]
  refine ⟨93527850501968293678913239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124703800669291058238550985 93527850501968293678913239)
  ·
    refine ⟨140291775752952440518369859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93527850501968293678913239 140291775752952440518369859)
    ·
      refine ⟨210437663629428660777554789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140291775752952440518369859 210437663629428660777554789)
      ·
        refine ⟨39457061930517873895791523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210437663629428660777554789 39457061930517873895791523)
        ·
          refine ⟨59185592895776810843687285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39457061930517873895791523 59185592895776810843687285)
          ·
            refine ⟨5548649333979076016595683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59185592895776810843687285 5548649333979076016595683)
            ·
              refine ⟨8322974000968614024893525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5548649333979076016595683 8322974000968614024893525)
              ·
                refine ⟨97534851573850945604221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8322974000968614024893525 97534851573850945604221)
                ·
                  rfl

theorem cell23_5128608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 8].length) (baseStart_5128608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128608 prefixEnd_5128608 := by exact prefixLift 5128608
  have htrace : WordTrace (prefixWord ++ tailWord_5128608) baseStart_5128608 baseEnd_5128608 := by
    simpa [prefixWord, tailWord_5128608, baseEnd_5128608] using wordTrace_append hprefix tailTrace_5128608
  have hstable : (prefixWord ++ tailWord_5128608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128608).length < 2 ^ (prefixWord ++ tailWord_5128608).sum := by decide
  have hdescent : baseEnd_5128608 < baseStart_5128608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128615 : List Nat := [1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_5128615 : Nat := 118140960795 + 5128615 * 2 ^ 59
def prefixEnd_5128615 : Nat := 4983230072969 + 3 ^ 40 * 5128615 * 2
def baseEnd_5128615 : Nat := 2633444586858557003926435

theorem tailTrace_5128615 : CollatzResearch.WordTrace tailWord_5128615 prefixEnd_5128615 2633444586858557003926435 := by
  unfold tailWord_5128615
  simp only [CollatzResearch.WordTrace]
  refine ⟨187055956314911227553331299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124703970876607485035554199 187055956314911227553331299)
  ·
    refine ⟨280583934472366841329996949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187055956314911227553331299 280583934472366841329996949)
    ·
      refine ⟨13152371928392195687343607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 280583934472366841329996949 13152371928392195687343607)
      ·
        refine ⟨19728557892588293531015411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13152371928392195687343607 19728557892588293531015411)
        ·
          refine ⟨29592836838882440296523117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19728557892588293531015411 29592836838882440296523117)
          ·
            refine ⟨11097313814580915111196169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29592836838882440296523117 11097313814580915111196169)
            ·
              refine ⟨8322985360935686333397127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11097313814580915111196169 8322985360935686333397127)
              ·
                refine ⟨12484478041403529500095691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8322985360935686333397127 12484478041403529500095691)
                ·
                  refine ⟨18726717062105294250143537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12484478041403529500095691 18726717062105294250143537)
                  ·
                    refine ⟨14045037796578970687607653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18726717062105294250143537 14045037796578970687607653)
                    ·
                      refine ⟨2633444586858557003926435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14045037796578970687607653 2633444586858557003926435)
                      ·
                        rfl

theorem cell23_5128615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_5128615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128615 prefixEnd_5128615 := by exact prefixLift 5128615
  have htrace : WordTrace (prefixWord ++ tailWord_5128615) baseStart_5128615 baseEnd_5128615 := by
    simpa [prefixWord, tailWord_5128615, baseEnd_5128615] using wordTrace_append hprefix tailTrace_5128615
  have hstable : (prefixWord ++ tailWord_5128615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128615).length < 2 ^ (prefixWord ++ tailWord_5128615).sum := by decide
  have hdescent : baseEnd_5128615 < baseStart_5128615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128636 : List Nat := [2, 2, 2, 4, 1, 2, 2, 3, 1, 2, 2]
def baseStart_5128636 : Nat := 118140960795 + 5128636 * 2 ^ 59
def prefixEnd_5128636 : Nat := 4983230072969 + 3 ^ 40 * 5128636 * 2
def baseEnd_5128636 : Nat := 2633455369952301421763839

theorem tailTrace_5128636 : CollatzResearch.WordTrace tailWord_5128636 prefixEnd_5128636 2633455369952301421763839 := by
  unfold tailWord_5128636
  simp only [CollatzResearch.WordTrace]
  refine ⟨93528361123917574069922881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124704481498556765426563841 93528361123917574069922881)
  ·
    refine ⟨70146270842938180552442161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93528361123917574069922881 70146270842938180552442161)
    ·
      refine ⟨52609703132203635414331621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70146270842938180552442161 52609703132203635414331621)
      ·
        refine ⟨9864319337288181640187179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52609703132203635414331621 9864319337288181640187179)
        ·
          refine ⟨14796479005932272460280769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9864319337288181640187179 14796479005932272460280769)
          ·
            refine ⟨11097359254449204345210577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14796479005932272460280769 11097359254449204345210577)
            ·
              refine ⟨8323019440836903258907933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11097359254449204345210577 8323019440836903258907933)
              ·
                refine ⟨3121132290313838722090475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8323019440836903258907933 3121132290313838722090475)
                ·
                  refine ⟨4681698435470758083135713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3121132290313838722090475 4681698435470758083135713)
                  ·
                    refine ⟨3511273826603068562351785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4681698435470758083135713 3511273826603068562351785)
                    ·
                      refine ⟨2633455369952301421763839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3511273826603068562351785 2633455369952301421763839)
                      ·
                        rfl

theorem cell23_5128636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_5128636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128636 prefixEnd_5128636 := by exact prefixLift 5128636
  have htrace : WordTrace (prefixWord ++ tailWord_5128636) baseStart_5128636 baseEnd_5128636 := by
    simpa [prefixWord, tailWord_5128636, baseEnd_5128636] using wordTrace_append hprefix tailTrace_5128636
  have hstable : (prefixWord ++ tailWord_5128636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128636).length < 2 ^ (prefixWord ++ tailWord_5128636).sum := by decide
  have hdescent : baseEnd_5128636 < baseStart_5128636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128652 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 4, 1, 3]
def baseStart_5128652 : Nat := 118140960795 + 5128652 * 2 ^ 59
def prefixEnd_5128652 : Nat := 4983230072969 + 3 ^ 40 * 5128652 * 2
def baseEnd_5128652 : Nat := 2633463585642773359163765

theorem tailTrace_5128652 : CollatzResearch.WordTrace tailWord_5128652 prefixEnd_5128652 2633463585642773359163765 := by
  unfold tailWord_5128652
  simp only [CollatzResearch.WordTrace]
  refine ⟨93528652907888591436214105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124704870543851455248285473 93528652907888591436214105)
  ·
    refine ⟨70146489680916443577160579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93528652907888591436214105 70146489680916443577160579)
    ·
      refine ⟨105219734521374665365740869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70146489680916443577160579 105219734521374665365740869)
      ·
        refine ⟨19728700222757749756076413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105219734521374665365740869 19728700222757749756076413)
        ·
          refine ⟨7398262583534156158528655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19728700222757749756076413 7398262583534156158528655)
          ·
            refine ⟨11097393875301234237792983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7398262583534156158528655 11097393875301234237792983)
            ·
              refine ⟨16646090812951851356689475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11097393875301234237792983 16646090812951851356689475)
              ·
                refine ⟨24969136219427777035034213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16646090812951851356689475 24969136219427777035034213)
                ·
                  refine ⟨4681713041142708194068915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24969136219427777035034213 4681713041142708194068915)
                  ·
                    refine ⟨7022569561714062291103373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4681713041142708194068915 7022569561714062291103373)
                    ·
                      refine ⟨2633463585642773359163765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7022569561714062291103373 2633463585642773359163765)
                      ·
                        rfl

theorem cell23_5128652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_5128652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128652 prefixEnd_5128652 := by exact prefixLift 5128652
  have htrace : WordTrace (prefixWord ++ tailWord_5128652) baseStart_5128652 baseEnd_5128652 := by
    simpa [prefixWord, tailWord_5128652, baseEnd_5128652] using wordTrace_append hprefix tailTrace_5128652
  have hstable : (prefixWord ++ tailWord_5128652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128652).length < 2 ^ (prefixWord ++ tailWord_5128652).sum := by decide
  have hdescent : baseEnd_5128652 < baseStart_5128652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128669 : List Nat := [1, 4, 3, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_5128669 : Nat := 118140960795 + 5128669 * 2 ^ 59
def prefixEnd_5128669 : Nat := 4983230072969 + 3 ^ 40 * 5128669 * 2
def baseEnd_5128669 : Nat := 2633472314813899792651187

theorem tailTrace_5128669 : CollatzResearch.WordTrace tailWord_5128669 prefixEnd_5128669 2633472314813899792651187 := by
  unfold tailWord_5128669
  simp only [CollatzResearch.WordTrace]
  refine ⟨187057925856715594775797061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124705283904477063183864707 187057925856715594775797061)
  ·
    refine ⟨35073361098134174020461949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187057925856715594775797061 35073361098134174020461949)
    ·
      refine ⟨13152510411800315257673231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35073361098134174020461949 13152510411800315257673231)
      ·
        refine ⟨19728765617700472886509847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13152510411800315257673231 19728765617700472886509847)
        ·
          refine ⟨29593148426550709329764771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19728765617700472886509847 29593148426550709329764771)
          ·
            refine ⟨44389722639826063994647157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29593148426550709329764771 44389722639826063994647157)
            ·
              refine ⟨4161536497483693499498171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44389722639826063994647157 4161536497483693499498171)
              ·
                refine ⟨6242304746225540249247257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4161536497483693499498171 6242304746225540249247257)
                ·
                  refine ⟨4681728559669155186935443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6242304746225540249247257 4681728559669155186935443)
                  ·
                    refine ⟨7022592839503732780403165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4681728559669155186935443 7022592839503732780403165)
                    ·
                      refine ⟨2633472314813899792651187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7022592839503732780403165 2633472314813899792651187)
                      ·
                        rfl

theorem cell23_5128669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_5128669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128669 prefixEnd_5128669 := by exact prefixLift 5128669
  have htrace : WordTrace (prefixWord ++ tailWord_5128669) baseStart_5128669 baseEnd_5128669 := by
    simpa [prefixWord, tailWord_5128669, baseEnd_5128669] using wordTrace_append hprefix tailTrace_5128669
  have hstable : (prefixWord ++ tailWord_5128669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128669).length < 2 ^ (prefixWord ++ tailWord_5128669).sum := by decide
  have hdescent : baseEnd_5128669 < baseStart_5128669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128681 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 9]
def baseStart_5128681 : Nat := 118140960795 + 5128681 * 2 ^ 59
def prefixEnd_5128681 : Nat := 4983230072969 + 3 ^ 40 * 5128681 * 2
def baseEnd_5128681 : Nat := 292608719620194860633459

theorem tailTrace_5128681 : CollatzResearch.WordTrace tailWord_5128681 prefixEnd_5128681 292608719620194860633459 := by
  unfold tailWord_5128681
  simp only [CollatzResearch.WordTrace]
  refine ⟨187058363532672120825233897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124705575688448080550155931 187058363532672120825233897)
  ·
    refine ⟨140293772649504090618925423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187058363532672120825233897 140293772649504090618925423)
    ·
      refine ⟨210440658974256135928388135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140293772649504090618925423 210440658974256135928388135)
      ·
        refine ⟨315660988461384203892582203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210440658974256135928388135 315660988461384203892582203)
        ·
          refine ⟨473491482692076305838873305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315660988461384203892582203 473491482692076305838873305)
          ·
            refine ⟨355118612019057229379154979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473491482692076305838873305 355118612019057229379154979)
            ·
              refine ⟨532677918028585844068732469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355118612019057229379154979 532677918028585844068732469)
              ·
                refine ⟨49938554815179922881443669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 532677918028585844068732469 49938554815179922881443669)
                ·
                  refine ⟨292608719620194860633459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49938554815179922881443669 292608719620194860633459)
                  ·
                    rfl

theorem cell23_5128681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 9].length) (baseStart_5128681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128681 prefixEnd_5128681 := by exact prefixLift 5128681
  have htrace : WordTrace (prefixWord ++ tailWord_5128681) baseStart_5128681 baseEnd_5128681 := by
    simpa [prefixWord, tailWord_5128681, baseEnd_5128681] using wordTrace_append hprefix tailTrace_5128681
  have hstable : (prefixWord ++ tailWord_5128681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128681).length < 2 ^ (prefixWord ++ tailWord_5128681).sum := by decide
  have hdescent : baseEnd_5128681 < baseStart_5128681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128715 : List Nat := [1, 1, 1, 1, 7, 3, 1, 1, 7]
def baseStart_5128715 : Nat := 118140960795 + 5128715 * 2 ^ 59
def prefixEnd_5128715 : Nat := 4983230072969 + 3 ^ 40 * 5128715 * 2
def baseEnd_5128715 : Nat := 292610659436000734741775

theorem tailTrace_5128715 : CollatzResearch.WordTrace tailWord_5128715 prefixEnd_5128715 292610659436000734741775 := by
  unfold tailWord_5128715
  simp only [CollatzResearch.WordTrace]
  refine ⟨187059603614548944631971599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124706402409699296421314399 187059603614548944631971599)
  ·
    refine ⟨280589405421823416947957399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187059603614548944631971599 280589405421823416947957399)
    ·
      refine ⟨420884108132735125421936099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280589405421823416947957399 420884108132735125421936099)
      ·
        refine ⟨631326162199102688132904149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420884108132735125421936099 631326162199102688132904149)
        ·
          refine ⟨14796706926541469253114941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 631326162199102688132904149 14796706926541469253114941)
          ·
            refine ⟨5548765097453050969918103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14796706926541469253114941 5548765097453050969918103)
            ·
              refine ⟨8323147646179576454877155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5548765097453050969918103 8323147646179576454877155)
              ·
                refine ⟨12484721469269364682315733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8323147646179576454877155 12484721469269364682315733)
                ·
                  refine ⟨292610659436000734741775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12484721469269364682315733 292610659436000734741775)
                  ·
                    rfl

theorem cell23_5128715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 7].length) (baseStart_5128715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128715 prefixEnd_5128715 := by exact prefixLift 5128715
  have htrace : WordTrace (prefixWord ++ tailWord_5128715) baseStart_5128715 baseEnd_5128715 := by
    simpa [prefixWord, tailWord_5128715, baseEnd_5128715] using wordTrace_append hprefix tailTrace_5128715
  have hstable : (prefixWord ++ tailWord_5128715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128715).length < 2 ^ (prefixWord ++ tailWord_5128715).sum := by decide
  have hdescent : baseEnd_5128715 < baseStart_5128715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128738 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_5128738 : Nat := 118140960795 + 5128738 * 2 ^ 59
def prefixEnd_5128738 : Nat := 4983230072969 + 3 ^ 40 * 5128738 * 2
def baseEnd_5128738 : Nat := 2633507744979060022688369

theorem tailTrace_5128738 : CollatzResearch.WordTrace tailWord_5128738 prefixEnd_5128738 2633507744979060022688369 := by
  unfold tailWord_5128738
  simp only [CollatzResearch.WordTrace]
  refine ⟨46765110623366404890014717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124706961662310413040039245 46765110623366404890014717)
  ·
    refine ⟨17536916483762401833755519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46765110623366404890014717 17536916483762401833755519)
    ·
      refine ⟨26305374725643602750633279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17536916483762401833755519 26305374725643602750633279)
      ·
        refine ⟨39458062088465404125949919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26305374725643602750633279 39458062088465404125949919)
        ·
          refine ⟨59187093132698106188924879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39458062088465404125949919 59187093132698106188924879)
          ·
            refine ⟨88780639699047159283387319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59187093132698106188924879 88780639699047159283387319)
            ·
              refine ⟨133170959548570738925080979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88780639699047159283387319 133170959548570738925080979)
              ·
                refine ⟨199756439322856108387621469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133170959548570738925080979 199756439322856108387621469)
                ·
                  refine ⟨74908664746071040645358051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199756439322856108387621469 74908664746071040645358051)
                  ·
                    refine ⟨112362997119106560968037077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74908664746071040645358051 112362997119106560968037077)
                    ·
                      refine ⟨2633507744979060022688369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112362997119106560968037077 2633507744979060022688369)
                      ·
                        rfl

theorem cell23_5128738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_5128738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128738 prefixEnd_5128738 := by exact prefixLift 5128738
  have htrace : WordTrace (prefixWord ++ tailWord_5128738) baseStart_5128738 baseEnd_5128738 := by
    simpa [prefixWord, tailWord_5128738, baseEnd_5128738] using wordTrace_append hprefix tailTrace_5128738
  have hstable : (prefixWord ++ tailWord_5128738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128738).length < 2 ^ (prefixWord ++ tailWord_5128738).sum := by decide
  have hdescent : baseEnd_5128738 < baseStart_5128738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128748 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 4]
def baseStart_5128748 : Nat := 118140960795 + 5128748 * 2 ^ 59
def prefixEnd_5128748 : Nat := 4983230072969 + 3 ^ 40 * 5128748 * 2
def baseEnd_5128748 : Nat := 2633512879785604983563323

theorem tailTrace_5128748 : CollatzResearch.WordTrace tailWord_5128748 prefixEnd_5128748 2633512879785604983563323 := by
  unfold tailWord_5128748
  simp only [CollatzResearch.WordTrace]
  refine ⟨93530403611714695633961449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124707204815619594178615265 93530403611714695633961449)
  ·
    refine ⟨70147802708786021725471087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93530403611714695633961449 70147802708786021725471087)
    ·
      refine ⟨105221704063179032588206631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70147802708786021725471087 105221704063179032588206631)
      ·
        refine ⟨157832556094768548882309947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105221704063179032588206631 157832556094768548882309947)
        ·
          refine ⟨236748834142152823323464921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157832556094768548882309947 236748834142152823323464921)
          ·
            refine ⟨177561625606614617492598691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236748834142152823323464921 177561625606614617492598691)
            ·
              refine ⟨266342438409921926238898037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177561625606614617492598691 266342438409921926238898037)
              ·
                refine ⟨24969603600930180584896691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 266342438409921926238898037 24969603600930180584896691)
                ·
                  refine ⟨37454405401395270877345037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24969603600930180584896691 37454405401395270877345037)
                  ·
                    refine ⟨14045402025523226579004389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37454405401395270877345037 14045402025523226579004389)
                    ·
                      refine ⟨2633512879785604983563323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14045402025523226579004389 2633512879785604983563323)
                      ·
                        rfl

theorem cell23_5128748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_5128748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128748 prefixEnd_5128748 := by exact prefixLift 5128748
  have htrace : WordTrace (prefixWord ++ tailWord_5128748) baseStart_5128748 baseEnd_5128748 := by
    simpa [prefixWord, tailWord_5128748, baseEnd_5128748] using wordTrace_append hprefix tailTrace_5128748
  have hstable : (prefixWord ++ tailWord_5128748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128748).length < 2 ^ (prefixWord ++ tailWord_5128748).sum := by decide
  have hdescent : baseEnd_5128748 < baseStart_5128748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128822 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 8]
def baseStart_5128822 : Nat := 118140960795 + 5128822 * 2 ^ 59
def prefixEnd_5128822 : Nat := 4983230072969 + 3 ^ 40 * 5128822 * 2
def baseEnd_5128822 : Nat := 292616764150448632670887

theorem tailTrace_5128822 : CollatzResearch.WordTrace tailWord_5128822 prefixEnd_5128822 292616764150448632670887 := by
  unfold tailWord_5128822
  simp only [CollatzResearch.WordTrace]
  refine ⟨11691469139072581369132295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124709004150107534604077813 11691469139072581369132295)
  ·
    refine ⟨17537203708608872053698443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11691469139072581369132295 17537203708608872053698443)
    ·
      refine ⟨26305805562913308080547665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17537203708608872053698443 26305805562913308080547665)
      ·
        refine ⟨19729354172184981060410749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26305805562913308080547665 19729354172184981060410749)
        ·
          refine ⟨7398507814569367897654031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19729354172184981060410749 7398507814569367897654031)
          ·
            refine ⟨11097761721854051846481047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7398507814569367897654031 11097761721854051846481047)
            ·
              refine ⟨16646642582781077769721571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11097761721854051846481047 16646642582781077769721571)
              ·
                refine ⟨24969963874171616654582357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16646642582781077769721571 24969963874171616654582357)
                ·
                  refine ⟨292616764150448632670887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24969963874171616654582357 292616764150448632670887)
                  ·
                    rfl

theorem cell23_5128822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_5128822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128822 prefixEnd_5128822 := by exact prefixLift 5128822
  have htrace : WordTrace (prefixWord ++ tailWord_5128822) baseStart_5128822 baseEnd_5128822 := by
    simpa [prefixWord, tailWord_5128822, baseEnd_5128822] using wordTrace_append hprefix tailTrace_5128822
  have hstable : (prefixWord ++ tailWord_5128822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128822).length < 2 ^ (prefixWord ++ tailWord_5128822).sum := by decide
  have hdescent : baseEnd_5128822 < baseStart_5128822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128832 : List Nat := [2, 1, 1, 2, 1, 5, 1, 3, 3, 1, 3]
def baseStart_5128832 : Nat := 118140960795 + 5128832 * 2 ^ 59
def prefixEnd_5128832 : Nat := 4983230072969 + 3 ^ 40 * 5128832 * 2
def baseEnd_5128832 : Nat := 2633556012160582654912937

theorem tailTrace_5128832 : CollatzResearch.WordTrace tailWord_5128832 prefixEnd_5128832 2633556012160582654912937 := by
  unfold tailWord_5128832
  simp only [CollatzResearch.WordTrace]
  refine ⟨93531935477562536806990375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124709247303416715742653833 93531935477562536806990375)
  ·
    refine ⟨140297903216343805210485563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93531935477562536806990375 140297903216343805210485563)
    ·
      refine ⟨210446854824515707815728345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140297903216343805210485563 210446854824515707815728345)
      ·
        refine ⟨157835141118386780861796259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210446854824515707815728345 157835141118386780861796259)
        ·
          refine ⟨236752711677580171292694389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157835141118386780861796259 236752711677580171292694389)
          ·
            refine ⟨22195566719773141058690099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 236752711677580171292694389 22195566719773141058690099)
            ·
              refine ⟨33293350079659711588035149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22195566719773141058690099 33293350079659711588035149)
              ·
                refine ⟨12485006279872391845513181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33293350079659711588035149 12485006279872391845513181)
                ·
                  refine ⟨4681877354952146942067443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12485006279872391845513181 4681877354952146942067443)
                  ·
                    refine ⟨7022816032428220413101165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4681877354952146942067443 7022816032428220413101165)
                    ·
                      refine ⟨2633556012160582654912937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7022816032428220413101165 2633556012160582654912937)
                      ·
                        rfl

theorem cell23_5128832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 3, 1, 3].length) (baseStart_5128832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128832 prefixEnd_5128832 := by exact prefixLift 5128832
  have htrace : WordTrace (prefixWord ++ tailWord_5128832) baseStart_5128832 baseEnd_5128832 := by
    simpa [prefixWord, tailWord_5128832, baseEnd_5128832] using wordTrace_append hprefix tailTrace_5128832
  have hstable : (prefixWord ++ tailWord_5128832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128832).length < 2 ^ (prefixWord ++ tailWord_5128832).sum := by decide
  have hdescent : baseEnd_5128832 < baseStart_5128832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128882 : List Nat := [3, 2, 1, 1, 1, 2, 1, 6, 2, 4]
def baseStart_5128882 : Nat := 118140960795 + 5128882 * 2 ^ 59
def prefixEnd_5128882 : Nat := 4983230072969 + 3 ^ 40 * 5128882 * 2
def baseEnd_5128882 : Nat := 877860562064435819762569

theorem tailTrace_5128882 : CollatzResearch.WordTrace tailWord_5128882 prefixEnd_5128882 877860562064435819762569 := by
  unfold tailWord_5128882
  simp only [CollatzResearch.WordTrace]
  refine ⟨46766423651235983038325225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124710463069962621435533933 46766423651235983038325225)
  ·
    refine ⟨35074817738426987278743919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46766423651235983038325225 35074817738426987278743919)
    ·
      refine ⟨52612226607640480918115879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35074817738426987278743919 52612226607640480918115879)
      ·
        refine ⟨78918339911460721377173819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52612226607640480918115879 78918339911460721377173819)
        ·
          refine ⟨118377509867191082065760729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78918339911460721377173819 118377509867191082065760729)
          ·
            refine ⟨88783132400393311549320547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118377509867191082065760729 88783132400393311549320547)
            ·
              refine ⟨133174698600589967323980821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88783132400393311549320547 133174698600589967323980821)
              ·
                refine ⟨6242563996902654718311601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 133174698600589967323980821 6242563996902654718311601)
                ·
                  refine ⟨4681922997676991038733701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6242563996902654718311601 4681922997676991038733701)
                  ·
                    refine ⟨877860562064435819762569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4681922997676991038733701 877860562064435819762569)
                    ·
                      rfl

theorem cell23_5128882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_5128882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128882 prefixEnd_5128882 := by exact prefixLift 5128882
  have htrace : WordTrace (prefixWord ++ tailWord_5128882) baseStart_5128882 baseEnd_5128882 := by
    simpa [prefixWord, tailWord_5128882, baseEnd_5128882] using wordTrace_append hprefix tailTrace_5128882
  have hstable : (prefixWord ++ tailWord_5128882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128882).length < 2 ^ (prefixWord ++ tailWord_5128882).sum := by decide
  have hdescent : baseEnd_5128882 < baseStart_5128882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128892 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 3, 2, 3]
def baseStart_5128892 : Nat := 118140960795 + 5128892 * 2 ^ 59
def prefixEnd_5128892 : Nat := 4983230072969 + 3 ^ 40 * 5128892 * 2
def baseEnd_5128892 : Nat := 2633586820999852420162661

theorem tailTrace_5128892 : CollatzResearch.WordTrace tailWord_5128892 prefixEnd_5128892 2633586820999852420162661 := by
  unfold tailWord_5128892
  simp only [CollatzResearch.WordTrace]
  refine ⟨93533029667453851930582465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124710706223271802574109953 93533029667453851930582465)
  ·
    refine ⟨70149772250590388947936849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93533029667453851930582465 70149772250590388947936849)
    ·
      refine ⟨52612329187942791710952637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70149772250590388947936849 52612329187942791710952637)
      ·
        refine ⟨19729623445478546891607239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52612329187942791710952637 19729623445478546891607239)
        ·
          refine ⟨29594435168217820337410859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19729623445478546891607239 29594435168217820337410859)
          ·
            refine ⟨44391652752326730506116289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29594435168217820337410859 44391652752326730506116289)
            ·
              refine ⟨33293739564245047879587217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44391652752326730506116289 33293739564245047879587217)
              ·
                refine ⟨24970304673183785909690413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33293739564245047879587217 24970304673183785909690413)
                ·
                  refine ⟨9363864252443919716133905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24970304673183785909690413 9363864252443919716133905)
                  ·
                    refine ⟨7022898189332939787100429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9363864252443919716133905 7022898189332939787100429)
                    ·
                      refine ⟨2633586820999852420162661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7022898189332939787100429 2633586820999852420162661)
                      ·
                        rfl

theorem cell23_5128892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_5128892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128892 prefixEnd_5128892 := by exact prefixLift 5128892
  have htrace : WordTrace (prefixWord ++ tailWord_5128892) baseStart_5128892 baseEnd_5128892 := by
    simpa [prefixWord, tailWord_5128892, baseEnd_5128892] using wordTrace_append hprefix tailTrace_5128892
  have hstable : (prefixWord ++ tailWord_5128892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128892).length < 2 ^ (prefixWord ++ tailWord_5128892).sum := by decide
  have hdescent : baseEnd_5128892 < baseStart_5128892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128895 : List Nat := [1, 1, 2, 2, 2, 5, 2, 8]
def baseStart_5128895 : Nat := 118140960795 + 5128895 * 2 ^ 59
def prefixEnd_5128895 : Nat := 4983230072969 + 3 ^ 40 * 5128895 * 2
def baseEnd_5128895 : Nat := 97540309683030218830561

theorem tailTrace_5128895 : CollatzResearch.WordTrace tailWord_5128895 prefixEnd_5128895 97540309683030218830561 := by
  unfold tailWord_5128895
  simp only [CollatzResearch.WordTrace]
  refine ⟨187066168753896835373524139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124710779169264556915682759 187066168753896835373524139)
  ·
    refine ⟨280599253130845253060286209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187066168753896835373524139 280599253130845253060286209)
    ·
      refine ⟨210449439848133939795214657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280599253130845253060286209 210449439848133939795214657)
      ·
        refine ⟨157837079886100454846410993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210449439848133939795214657 157837079886100454846410993)
        ·
          refine ⟨118377809914575341134808245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157837079886100454846410993 118377809914575341134808245)
          ·
            refine ⟨11097919679491438231388273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118377809914575341134808245 11097919679491438231388273)
            ·
              refine ⟨8323439759618578673541205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11097919679491438231388273 8323439759618578673541205)
              ·
                refine ⟨97540309683030218830561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8323439759618578673541205 97540309683030218830561)
                ·
                  rfl

theorem cell23_5128895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 8].length) (baseStart_5128895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128895 prefixEnd_5128895 := by exact prefixLift 5128895
  have htrace : WordTrace (prefixWord ++ tailWord_5128895) baseStart_5128895 baseEnd_5128895 := by
    simpa [prefixWord, tailWord_5128895, baseEnd_5128895] using wordTrace_append hprefix tailTrace_5128895
  have hstable : (prefixWord ++ tailWord_5128895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128895).length < 2 ^ (prefixWord ++ tailWord_5128895).sum := by decide
  have hdescent : baseEnd_5128895 < baseStart_5128895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128905 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 7, 3, 3]
def baseStart_5128905 : Nat := 118140960795 + 5128905 * 2 ^ 59
def prefixEnd_5128905 : Nat := 4983230072969 + 3 ^ 40 * 5128905 * 2
def baseEnd_5128905 : Nat := 2633593496248360869300101

theorem tailTrace_5128905 : CollatzResearch.WordTrace tailWord_5128905 prefixEnd_5128905 2633593496248360869300101 := by
  unfold tailWord_5128905
  simp only [CollatzResearch.WordTrace]
  refine ⟨187066533483860607081388169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124711022322573738054258779 187066533483860607081388169)
  ·
    refine ⟨140299900112895455311041127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187066533483860607081388169 140299900112895455311041127)
    ·
      refine ⟨210449850169343182966561691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140299900112895455311041127 210449850169343182966561691)
      ·
        refine ⟨315674775254014774449842537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210449850169343182966561691 315674775254014774449842537)
        ·
          refine ⟨236756081440511080837381903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315674775254014774449842537 236756081440511080837381903)
          ·
            refine ⟨355134122160766621256072855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236756081440511080837381903 355134122160766621256072855)
            ·
              refine ⟨532701183241149931884109283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355134122160766621256072855 532701183241149931884109283)
              ·
                refine ⟨799051774861724897826163925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532701183241149931884109283 799051774861724897826163925)
                ·
                  refine ⟨18727775973321677292800717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 799051774861724897826163925 18727775973321677292800717)
                  ·
                    refine ⟨7022915989995628984800269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18727775973321677292800717 7022915989995628984800269)
                    ·
                      refine ⟨2633593496248360869300101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7022915989995628984800269 2633593496248360869300101)
                      ·
                        rfl

theorem cell23_5128905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 3, 3].length) (baseStart_5128905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128905 prefixEnd_5128905 := by exact prefixLift 5128905
  have htrace : WordTrace (prefixWord ++ tailWord_5128905) baseStart_5128905 baseEnd_5128905 := by
    simpa [prefixWord, tailWord_5128905, baseEnd_5128905] using wordTrace_append hprefix tailTrace_5128905
  have hstable : (prefixWord ++ tailWord_5128905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128905).length < 2 ^ (prefixWord ++ tailWord_5128905).sum := by decide
  have hdescent : baseEnd_5128905 < baseStart_5128905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128922 : List Nat := [3, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3]
def baseStart_5128922 : Nat := 118140960795 + 5128922 * 2 ^ 59
def prefixEnd_5128922 : Nat := 4983230072969 + 3 ^ 40 * 5128922 * 2
def baseEnd_5128922 : Nat := 2633602225419487302787523

theorem tailTrace_5128922 : CollatzResearch.WordTrace tailWord_5128922 prefixEnd_5128922 2633602225419487302787523 := by
  unfold tailWord_5128922
  simp only [CollatzResearch.WordTrace]
  refine ⟨46766788381199754746189255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124711435683199345989838013 46766788381199754746189255)
  ·
    refine ⟨70150182571799632119283883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46766788381199754746189255 70150182571799632119283883)
    ·
      refine ⟨105225273857699448178925825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70150182571799632119283883 105225273857699448178925825)
      ·
        refine ⟨78918955393274586134194369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105225273857699448178925825 78918955393274586134194369)
        ·
          refine ⟨59189216544955939600645777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78918955393274586134194369 59189216544955939600645777)
          ·
            refine ⟨44391912408716954700484333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59189216544955939600645777 44391912408716954700484333)
            ·
              refine ⟨16646967153268858012681625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44391912408716954700484333 16646967153268858012681625)
              ·
                refine ⟨12485225364951643509511219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16646967153268858012681625 12485225364951643509511219)
                ·
                  refine ⟨18727838047427465264266829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12485225364951643509511219 18727838047427465264266829)
                  ·
                    refine ⟨7022939267785299474100061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18727838047427465264266829 7022939267785299474100061)
                    ·
                      refine ⟨2633602225419487302787523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7022939267785299474100061 2633602225419487302787523)
                      ·
                        rfl

theorem cell23_5128922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_5128922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128922 prefixEnd_5128922 := by exact prefixLift 5128922
  have htrace : WordTrace (prefixWord ++ tailWord_5128922) baseStart_5128922 baseEnd_5128922 := by
    simpa [prefixWord, tailWord_5128922, baseEnd_5128922] using wordTrace_append hprefix tailTrace_5128922
  have hstable : (prefixWord ++ tailWord_5128922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128922).length < 2 ^ (prefixWord ++ tailWord_5128922).sum := by decide
  have hdescent : baseEnd_5128922 < baseStart_5128922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128945 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 1, 5, 4]
def baseStart_5128945 : Nat := 118140960795 + 5128945 * 2 ^ 59
def prefixEnd_5128945 : Nat := 4983230072969 + 3 ^ 40 * 5128945 * 2
def baseEnd_5128945 : Nat := 2633614035474540712799917

theorem tailTrace_5128945 : CollatzResearch.WordTrace tailWord_5128945 prefixEnd_5128945 2633614035474540712799917 := by
  unfold tailWord_5128945
  simp only [CollatzResearch.WordTrace]
  refine ⟨187067992403715693912844289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124711994935810462608562859 187067992403715693912844289)
  ·
    refine ⟨140300994302786770434633217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187067992403715693912844289 140300994302786770434633217)
    ·
      refine ⟨105225745727090077825974913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140300994302786770434633217 105225745727090077825974913)
      ·
        refine ⟨78919309295317558369481185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105225745727090077825974913 78919309295317558369481185)
        ·
          refine ⟨59189481971488168777110889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78919309295317558369481185 59189481971488168777110889)
          ·
            refine ⟨44392111478616126582833167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59189481971488168777110889 44392111478616126582833167)
            ·
              refine ⟨66588167217924189874249751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44392111478616126582833167 66588167217924189874249751)
              ·
                refine ⟨99882250826886284811374627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66588167217924189874249751 99882250826886284811374627)
                ·
                  refine ⟨149823376240329427217061941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99882250826886284811374627 149823376240329427217061941)
                  ·
                    refine ⟨14045941522530883801599557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 149823376240329427217061941 14045941522530883801599557)
                    ·
                      refine ⟨2633614035474540712799917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14045941522530883801599557 2633614035474540712799917)
                      ·
                        rfl

theorem cell23_5128945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_5128945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128945 prefixEnd_5128945 := by exact prefixLift 5128945
  have htrace : WordTrace (prefixWord ++ tailWord_5128945) baseStart_5128945 baseEnd_5128945 := by
    simpa [prefixWord, tailWord_5128945, baseEnd_5128945] using wordTrace_append hprefix tailTrace_5128945
  have hstable : (prefixWord ++ tailWord_5128945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128945).length < 2 ^ (prefixWord ++ tailWord_5128945).sum := by decide
  have hdescent : baseEnd_5128945 < baseStart_5128945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128965 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 4, 1, 5]
def baseStart_5128965 : Nat := 118140960795 + 5128965 * 2 ^ 59
def prefixEnd_5128965 : Nat := 4983230072969 + 3 ^ 40 * 5128965 * 2
def baseEnd_5128965 : Nat := 2633624305087630634549825

theorem tailTrace_5128965 : CollatzResearch.WordTrace tailWord_5128965 prefixEnd_5128965 2633624305087630634549825 := by
  unfold tailWord_5128965
  simp only [CollatzResearch.WordTrace]
  refine ⟨187068721863643237328572349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124712481242428824885714899 187068721863643237328572349)
  ·
    refine ⟨70150770698866213998214631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187068721863643237328572349 70150770698866213998214631)
    ·
      refine ⟨105226156048299320997321947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70150770698866213998214631 105226156048299320997321947)
      ·
        refine ⟨157839234072448981495982921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105226156048299320997321947 157839234072448981495982921)
        ·
          refine ⟨118379425554336736121987191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157839234072448981495982921 118379425554336736121987191)
          ·
            refine ⟨177569138331505104182980787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118379425554336736121987191 177569138331505104182980787)
            ·
              refine ⟨266353707497257656274471181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177569138331505104182980787 266353707497257656274471181)
              ·
                refine ⟨99882640311471621102926693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266353707497257656274471181 99882640311471621102926693)
                ·
                  refine ⟨18727995058400928956798755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99882640311471621102926693 18727995058400928956798755)
                  ·
                    refine ⟨28091992587601393435198133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18727995058400928956798755 28091992587601393435198133)
                    ·
                      refine ⟨2633624305087630634549825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28091992587601393435198133 2633624305087630634549825)
                      ·
                        rfl

theorem cell23_5128965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_5128965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128965 prefixEnd_5128965 := by exact prefixLift 5128965
  have htrace : WordTrace (prefixWord ++ tailWord_5128965) baseStart_5128965 baseEnd_5128965 := by
    simpa [prefixWord, tailWord_5128965, baseEnd_5128965] using wordTrace_append hprefix tailTrace_5128965
  have hstable : (prefixWord ++ tailWord_5128965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128965).length < 2 ^ (prefixWord ++ tailWord_5128965).sum := by decide
  have hdescent : baseEnd_5128965 < baseStart_5128965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128975 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 4]
def baseStart_5128975 : Nat := 118140960795 + 5128975 * 2 ^ 59
def prefixEnd_5128975 : Nat := 4983230072969 + 3 ^ 40 * 5128975 * 2
def baseEnd_5128975 : Nat := 2633629439894175595424779

theorem tailTrace_5128975 : CollatzResearch.WordTrace tailWord_5128975 prefixEnd_5128975 2633629439894175595424779 := by
  unfold tailWord_5128975
  simp only [CollatzResearch.WordTrace]
  refine ⟨187069086593607009036436379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124712724395738006024290919 187069086593607009036436379)
  ·
    refine ⟨280603629890410513554654569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187069086593607009036436379 280603629890410513554654569)
    ·
      refine ⟨210452722417807885165990927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280603629890410513554654569 210452722417807885165990927)
      ·
        refine ⟨315679083626711827748986391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210452722417807885165990927 315679083626711827748986391)
        ·
          refine ⟨473518625440067741623479587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315679083626711827748986391 473518625440067741623479587)
          ·
            refine ⟨710277938160101612435219381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473518625440067741623479587 710277938160101612435219381)
            ·
              refine ⟨66588556702509526165801817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 710277938160101612435219381 66588556702509526165801817)
              ·
                refine ⟨49941417526882144624351363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66588556702509526165801817 49941417526882144624351363)
                ·
                  refine ⟨74912126290323216936527045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49941417526882144624351363 74912126290323216936527045)
                  ·
                    refine ⟨14046023679435603175598821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74912126290323216936527045 14046023679435603175598821)
                    ·
                      refine ⟨2633629439894175595424779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14046023679435603175598821 2633629439894175595424779)
                      ·
                        rfl

theorem cell23_5128975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 4].length) (baseStart_5128975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128975 prefixEnd_5128975 := by exact prefixLift 5128975
  have htrace : WordTrace (prefixWord ++ tailWord_5128975) baseStart_5128975 baseEnd_5128975 := by
    simpa [prefixWord, tailWord_5128975, baseEnd_5128975] using wordTrace_append hprefix tailTrace_5128975
  have hstable : (prefixWord ++ tailWord_5128975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128975).length < 2 ^ (prefixWord ++ tailWord_5128975).sum := by decide
  have hdescent : baseEnd_5128975 < baseStart_5128975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128979 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 4, 2, 2]
def baseStart_5128979 : Nat := 118140960795 + 5128979 * 2 ^ 59
def prefixEnd_5128979 : Nat := 4983230072969 + 3 ^ 40 * 5128979 * 2
def baseEnd_5128979 : Nat := 2633631493816793579774761

theorem tailTrace_5128979 : CollatzResearch.WordTrace tailWord_5128979 prefixEnd_5128979 2633631493816793579774761 := by
  unfold tailWord_5128979
  simp only [CollatzResearch.WordTrace]
  refine ⟨187069232485592517719581991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124712821657061678479721327 187069232485592517719581991)
  ·
    refine ⟨280603848728388776579372987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187069232485592517719581991 280603848728388776579372987)
    ·
      refine ⟨420905773092583164869059481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280603848728388776579372987 420905773092583164869059481)
      ·
        refine ⟨315679329819437373651794611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420905773092583164869059481 315679329819437373651794611)
        ·
          refine ⟨473518994729156060477691917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315679329819437373651794611 473518994729156060477691917)
          ·
            refine ⟨177569623023433522679134469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 473518994729156060477691917 177569623023433522679134469)
            ·
              refine ⟨33294304316893785502337713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177569623023433522679134469 33294304316893785502337713)
              ·
                refine ⟨24970728237670339126753285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33294304316893785502337713 24970728237670339126753285)
                ·
                  refine ⟨4682011544563188586266241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24970728237670339126753285 4682011544563188586266241)
                  ·
                    refine ⟨3511508658422391439699681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4682011544563188586266241 3511508658422391439699681)
                    ·
                      refine ⟨2633631493816793579774761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3511508658422391439699681 2633631493816793579774761)
                      ·
                        rfl

theorem cell23_5128979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 2, 2].length) (baseStart_5128979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128979 prefixEnd_5128979 := by exact prefixLift 5128979
  have htrace : WordTrace (prefixWord ++ tailWord_5128979) baseStart_5128979 baseEnd_5128979 := by
    simpa [prefixWord, tailWord_5128979, baseEnd_5128979] using wordTrace_append hprefix tailTrace_5128979
  have hstable : (prefixWord ++ tailWord_5128979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128979).length < 2 ^ (prefixWord ++ tailWord_5128979).sum := by decide
  have hdescent : baseEnd_5128979 < baseStart_5128979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5128992 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 4]
def baseStart_5128992 : Nat := 118140960795 + 5128992 * 2 ^ 59
def prefixEnd_5128992 : Nat := 4983230072969 + 3 ^ 40 * 5128992 * 2
def baseEnd_5128992 : Nat := 2633638169065302028912201

theorem tailTrace_5128992 : CollatzResearch.WordTrace tailWord_5128992 prefixEnd_5128992 2633638169065302028912201 := by
  unfold tailWord_5128992
  simp only [CollatzResearch.WordTrace]
  refine ⟨93534853317272710469902615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124713137756363613959870153 93534853317272710469902615)
  ·
    refine ⟨140302279975909065704853923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93534853317272710469902615 140302279975909065704853923)
    ·
      refine ⟨210453419963863598557280885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140302279975909065704853923 210453419963863598557280885)
      ·
        refine ⟨19730008121612212364745083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 210453419963863598557280885 19730008121612212364745083)
        ·
          refine ⟨29595012182418318547117625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19730008121612212364745083 29595012182418318547117625)
          ·
            refine ⟨22196259136813738910338219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29595012182418318547117625 22196259136813738910338219)
            ·
              refine ⟨33294388705220608365507329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22196259136813738910338219 33294388705220608365507329)
              ·
                refine ⟨24970791528915456274130497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33294388705220608365507329 24970791528915456274130497)
                ·
                  refine ⟨18728093646686592205597873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24970791528915456274130497 18728093646686592205597873)
                  ·
                    refine ⟨14046070235014944154198405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18728093646686592205597873 14046070235014944154198405)
                    ·
                      refine ⟨2633638169065302028912201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14046070235014944154198405 2633638169065302028912201)
                      ·
                        rfl

theorem cell23_5128992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_5128992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5128992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5128992 prefixEnd_5128992 := by exact prefixLift 5128992
  have htrace : WordTrace (prefixWord ++ tailWord_5128992) baseStart_5128992 baseEnd_5128992 := by
    simpa [prefixWord, tailWord_5128992, baseEnd_5128992] using wordTrace_append hprefix tailTrace_5128992
  have hstable : (prefixWord ++ tailWord_5128992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5128992).length < 2 ^ (prefixWord ++ tailWord_5128992).sum := by decide
  have hdescent : baseEnd_5128992 < baseStart_5128992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5128992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129015 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 3, 7]
def baseStart_5129015 : Nat := 118140960795 + 5129015 * 2 ^ 59
def prefixEnd_5129015 : Nat := 4983230072969 + 3 ^ 40 * 5129015 * 2
def baseEnd_5129015 : Nat := 877883326373451812974865

theorem tailTrace_5129015 : CollatzResearch.WordTrace tailWord_5129015 prefixEnd_5129015 877883326373451812974865 := by
  unfold tailWord_5129015
  simp only [CollatzResearch.WordTrace]
  refine ⟨187070545513462095867892499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124713697008974730578594999 187070545513462095867892499)
  ·
    refine ⟨280605818270193143801838749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187070545513462095867892499 280605818270193143801838749)
    ·
      refine ⟨105227181851322428925689531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280605818270193143801838749 105227181851322428925689531)
      ·
        refine ⟨157840772776983643388534297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105227181851322428925689531 157840772776983643388534297)
        ·
          refine ⟨118380579582737732541400723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157840772776983643388534297 118380579582737732541400723)
          ·
            refine ⟨177570869374106598812101085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118380579582737732541400723 177570869374106598812101085)
            ·
              refine ⟨66589076015289974554537907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177570869374106598812101085 66589076015289974554537907)
              ·
                refine ⟨99883614022934961831806861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66589076015289974554537907 99883614022934961831806861)
                ·
                  refine ⟨37456355258600610686927573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99883614022934961831806861 37456355258600610686927573)
                  ·
                    refine ⟨877883326373451812974865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37456355258600610686927573 877883326373451812974865)
                    ·
                      rfl

theorem cell23_5129015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_5129015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129015 prefixEnd_5129015 := by exact prefixLift 5129015
  have htrace : WordTrace (prefixWord ++ tailWord_5129015) baseStart_5129015 baseEnd_5129015 := by
    simpa [prefixWord, tailWord_5129015, baseEnd_5129015] using wordTrace_append hprefix tailTrace_5129015
  have hstable : (prefixWord ++ tailWord_5129015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129015).length < 2 ^ (prefixWord ++ tailWord_5129015).sum := by decide
  have hdescent : baseEnd_5129015 < baseStart_5129015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129032 : List Nat := [2, 1, 3, 1, 1, 3, 2, 3, 2, 5]
def baseStart_5129032 : Nat := 118140960795 + 5129032 * 2 ^ 59
def prefixEnd_5129032 : Nat := 4983230072969 + 3 ^ 40 * 5129032 * 2
def baseEnd_5129032 : Nat := 877886236097160624137339

theorem tailTrace_5129032 : CollatzResearch.WordTrace tailWord_5129032 prefixEnd_5129032 877886236097160624137339 := by
  unfold tailWord_5129032
  simp only [CollatzResearch.WordTrace]
  refine ⟨93535582777200253885630675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124714110369600338514174233 93535582777200253885630675)
  ·
    refine ⟨140303374165800380828446013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93535582777200253885630675 140303374165800380828446013)
    ·
      refine ⟨52613765312175142810667255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140303374165800380828446013 52613765312175142810667255)
      ·
        refine ⟨78920647968262714216000883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52613765312175142810667255 78920647968262714216000883)
        ·
          refine ⟨118380971952394071324001325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78920647968262714216000883 118380971952394071324001325)
          ·
            refine ⟨44392864482147776746500497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118380971952394071324001325 44392864482147776746500497)
            ·
              refine ⟨33294648361610832559875373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44392864482147776746500497 33294648361610832559875373)
              ·
                refine ⟨12485493135604062209953265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33294648361610832559875373 12485493135604062209953265)
                ·
                  refine ⟨9364119851703046657464949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12485493135604062209953265 9364119851703046657464949)
                  ·
                    refine ⟨877886236097160624137339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9364119851703046657464949 877886236097160624137339)
                    ·
                      rfl

theorem cell23_5129032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_5129032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129032 prefixEnd_5129032 := by exact prefixLift 5129032
  have htrace : WordTrace (prefixWord ++ tailWord_5129032) baseStart_5129032 baseEnd_5129032 := by
    simpa [prefixWord, tailWord_5129032, baseEnd_5129032] using wordTrace_append hprefix tailTrace_5129032
  have hstable : (prefixWord ++ tailWord_5129032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129032).length < 2 ^ (prefixWord ++ tailWord_5129032).sum := by decide
  have hdescent : baseEnd_5129032 < baseStart_5129032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129036 : List Nat := [2, 2, 1, 3, 3, 3, 1, 3, 5]
def baseStart_5129036 : Nat := 118140960795 + 5129036 * 2 ^ 59
def prefixEnd_5129036 : Nat := 4983230072969 + 3 ^ 40 * 5129036 * 2
def baseEnd_5129036 : Nat := 292628973579344428529111

theorem tailTrace_5129036 : CollatzResearch.WordTrace tailWord_5129036 prefixEnd_5129036 292628973579344428529111 := by
  unfold tailWord_5129036
  simp only [CollatzResearch.WordTrace]
  refine ⟨93535655723193008227203481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124714207630924010969604641 93535655723193008227203481)
  ·
    refine ⟨70151741792394756170402611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93535655723193008227203481 70151741792394756170402611)
    ·
      refine ⟨105227612688592134255603917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70151741792394756170402611 105227612688592134255603917)
      ·
        refine ⟨39460354758222050345851469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105227612688592134255603917 39460354758222050345851469)
        ·
          refine ⟨14797633034333268879694301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39460354758222050345851469 14797633034333268879694301)
          ·
            refine ⟨5549112387874975829885363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14797633034333268879694301 5549112387874975829885363)
            ·
              refine ⟨8323668581812463744828045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5549112387874975829885363 8323668581812463744828045)
              ·
                refine ⟨3121375718179673904310517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8323668581812463744828045 3121375718179673904310517)
                ·
                  refine ⟨292628973579344428529111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3121375718179673904310517 292628973579344428529111)
                  ·
                    rfl

theorem cell23_5129036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 5].length) (baseStart_5129036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129036 prefixEnd_5129036 := by exact prefixLift 5129036
  have htrace : WordTrace (prefixWord ++ tailWord_5129036) baseStart_5129036 baseEnd_5129036 := by
    simpa [prefixWord, tailWord_5129036, baseEnd_5129036] using wordTrace_append hprefix tailTrace_5129036
  have hstable : (prefixWord ++ tailWord_5129036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129036).length < 2 ^ (prefixWord ++ tailWord_5129036).sum := by decide
  have hdescent : baseEnd_5129036 < baseStart_5129036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129042 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_5129042 : Nat := 118140960795 + 5129042 * 2 ^ 59
def prefixEnd_5129042 : Nat := 4983230072969 + 3 ^ 40 * 5129042 * 2
def baseEnd_5129042 : Nat := 2633663843098026833286971

theorem tailTrace_5129042 : CollatzResearch.WordTrace tailWord_5129042 prefixEnd_5129042 2633663843098026833286971 := by
  unfold tailWord_5129042
  simp only [CollatzResearch.WordTrace]
  refine ⟨46767882571091069869781345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124714353522909519652750253 46767882571091069869781345)
  ·
    refine ⟨35075911928318302402336009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46767882571091069869781345 35075911928318302402336009)
    ·
      refine ⟨26306933946238726801752007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35075911928318302402336009 26306933946238726801752007)
      ·
        refine ⟨39460400919358090202628011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26306933946238726801752007 39460400919358090202628011)
        ·
          refine ⟨59190601379037135303942017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39460400919358090202628011 59190601379037135303942017)
          ·
            refine ⟨44392951034277851477956513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59190601379037135303942017 44392951034277851477956513)
            ·
              refine ⟨33294713275708388608467385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44392951034277851477956513 33294713275708388608467385)
              ·
                refine ⟨24971034956781291456350539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33294713275708388608467385 24971034956781291456350539)
                ·
                  refine ⟨37456552435171937184525809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24971034956781291456350539 37456552435171937184525809)
                  ·
                    refine ⟨28092414326378952888394357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37456552435171937184525809 28092414326378952888394357)
                    ·
                      refine ⟨2633663843098026833286971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28092414326378952888394357 2633663843098026833286971)
                      ·
                        rfl

theorem cell23_5129042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_5129042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129042 prefixEnd_5129042 := by exact prefixLift 5129042
  have htrace : WordTrace (prefixWord ++ tailWord_5129042) baseStart_5129042 baseEnd_5129042 := by
    simpa [prefixWord, tailWord_5129042, baseEnd_5129042] using wordTrace_append hprefix tailTrace_5129042
  have hstable : (prefixWord ++ tailWord_5129042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129042).length < 2 ^ (prefixWord ++ tailWord_5129042).sum := by decide
  have hdescent : baseEnd_5129042 < baseStart_5129042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129069 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 1, 6, 2]
def baseStart_5129069 : Nat := 118140960795 + 5129069 * 2 ^ 59
def prefixEnd_5129069 : Nat := 4983230072969 + 3 ^ 40 * 5129069 * 2
def baseEnd_5129069 : Nat := 2633677707075698227649347

theorem tailTrace_5129069 : CollatzResearch.WordTrace tailWord_5129069 prefixEnd_5129069 2633677707075698227649347 := by
  unfold tailWord_5129069
  simp only [CollatzResearch.WordTrace]
  refine ⟨187072515055266463090358261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124715010036844308726905507 187072515055266463090358261)
  ·
    refine ⟨17538048286431230914721087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 187072515055266463090358261 17538048286431230914721087)
    ·
      refine ⟨26307072429646846372081631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17538048286431230914721087 26307072429646846372081631)
      ·
        refine ⟨39460608644470269558122447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26307072429646846372081631 39460608644470269558122447)
        ·
          refine ⟨59190912966705404337183671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39460608644470269558122447 59190912966705404337183671)
          ·
            refine ⟨88786369450058106505775507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59190912966705404337183671 88786369450058106505775507)
            ·
              refine ⟨133179554175087159758663261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88786369450058106505775507 133179554175087159758663261)
              ·
                refine ⟨49942332815657684909498723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133179554175087159758663261 49942332815657684909498723)
                ·
                  refine ⟨74913499223486527364248085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49942332815657684909498723 74913499223486527364248085)
                  ·
                    refine ⟨3511570276100930970199129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74913499223486527364248085 3511570276100930970199129)
                    ·
                      refine ⟨2633677707075698227649347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3511570276100930970199129 2633677707075698227649347)
                      ·
                        rfl

theorem cell23_5129069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_5129069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129069 prefixEnd_5129069 := by exact prefixLift 5129069
  have htrace : WordTrace (prefixWord ++ tailWord_5129069) baseStart_5129069 baseEnd_5129069 := by
    simpa [prefixWord, tailWord_5129069, baseEnd_5129069] using wordTrace_append hprefix tailTrace_5129069
  have hstable : (prefixWord ++ tailWord_5129069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129069).length < 2 ^ (prefixWord ++ tailWord_5129069).sum := by decide
  have hdescent : baseEnd_5129069 < baseStart_5129069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129072 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 3]
def baseStart_5129072 : Nat := 118140960795 + 5129072 * 2 ^ 59
def prefixEnd_5129072 : Nat := 4983230072969 + 3 ^ 40 * 5129072 * 2
def baseEnd_5129072 : Nat := 2633679247517661715911833

theorem tailTrace_5129072 : CollatzResearch.WordTrace tailWord_5129072 prefixEnd_5129072 2633679247517661715911833 := by
  unfold tailWord_5129072
  simp only [CollatzResearch.WordTrace]
  refine ⟨93536312237127797301358735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124715082982837063068478313 93536312237127797301358735)
  ·
    refine ⟨140304468355691695952038103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93536312237127797301358735 140304468355691695952038103)
    ·
      refine ⟨210456702533537543928057155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140304468355691695952038103 210456702533537543928057155)
      ·
        refine ⟨315685053800306315892085733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210456702533537543928057155 315685053800306315892085733)
        ·
          refine ⟨59190947587557434229766075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 315685053800306315892085733 59190947587557434229766075)
          ·
            refine ⟨88786421381336151344649113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59190947587557434229766075 88786421381336151344649113)
            ·
              refine ⟨66589816036002113508486835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88786421381336151344649113 66589816036002113508486835)
              ·
                refine ⟨99884724054003170262730253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66589816036002113508486835 99884724054003170262730253)
                ·
                  refine ⟨37456771520251188848523845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99884724054003170262730253 37456771520251188848523845)
                  ·
                    refine ⟨7023144660047097909098221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37456771520251188848523845 7023144660047097909098221)
                    ·
                      refine ⟨2633679247517661715911833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7023144660047097909098221 2633679247517661715911833)
                      ·
                        rfl

theorem cell23_5129072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 3].length) (baseStart_5129072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129072 prefixEnd_5129072 := by exact prefixLift 5129072
  have htrace : WordTrace (prefixWord ++ tailWord_5129072) baseStart_5129072 baseEnd_5129072 := by
    simpa [prefixWord, tailWord_5129072, baseEnd_5129072] using wordTrace_append hprefix tailTrace_5129072
  have hstable : (prefixWord ++ tailWord_5129072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129072).length < 2 ^ (prefixWord ++ tailWord_5129072).sum := by decide
  have hdescent : baseEnd_5129072 < baseStart_5129072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129109 : List Nat := [1, 3, 2, 1, 1, 5, 2, 2, 6]
def baseStart_5129109 : Nat := 118140960795 + 5129109 * 2 ^ 59
def prefixEnd_5129109 : Nat := 4983230072969 + 3 ^ 40 * 5129109 * 2
def baseEnd_5129109 : Nat := 292633138477986452349907

theorem tailTrace_5129109 : CollatzResearch.WordTrace tailWord_5129109 prefixEnd_5129109 292633138477986452349907 := by
  unfold tailWord_5129109
  simp only [CollatzResearch.WordTrace]
  refine ⟨187073973975121549921814381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124715982650081033281209587 187073973975121549921814381)
  ·
    refine ⟨70152740240670581220680393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187073973975121549921814381 70152740240670581220680393)
    ·
      refine ⟨52614555180502935915510295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70152740240670581220680393 52614555180502935915510295)
      ·
        refine ⟨78921832770754403873265443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52614555180502935915510295 78921832770754403873265443)
        ·
          refine ⟨118382749156131605809898165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78921832770754403873265443 118382749156131605809898165)
          ·
            refine ⟨11098382733387338044677953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118382749156131605809898165 11098382733387338044677953)
            ·
              refine ⟨8323787050040503533508465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11098382733387338044677953 8323787050040503533508465)
              ·
                refine ⟨6242840287530377650131349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8323787050040503533508465 6242840287530377650131349)
                ·
                  refine ⟨292633138477986452349907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6242840287530377650131349 292633138477986452349907)
                  ·
                    rfl

theorem cell23_5129109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 6].length) (baseStart_5129109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129109 prefixEnd_5129109 := by exact prefixLift 5129109
  have htrace : WordTrace (prefixWord ++ tailWord_5129109) baseStart_5129109 baseEnd_5129109 := by
    simpa [prefixWord, tailWord_5129109, baseEnd_5129109] using wordTrace_append hprefix tailTrace_5129109
  have hstable : (prefixWord ++ tailWord_5129109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129109).length < 2 ^ (prefixWord ++ tailWord_5129109).sum := by decide
  have hdescent : baseEnd_5129109 < baseStart_5129109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129129 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 1, 5, 2]
def baseStart_5129129 : Nat := 118140960795 + 5129129 * 2 ^ 59
def prefixEnd_5129129 : Nat := 4983230072969 + 3 ^ 40 * 5129129 * 2
def baseEnd_5129129 : Nat := 2633708515914967992899071

theorem tailTrace_5129129 : CollatzResearch.WordTrace tailWord_5129129 prefixEnd_5129129 2633708515914967992899071 := by
  unfold tailWord_5129129
  simp only [CollatzResearch.WordTrace]
  refine ⟨187074703435049093337542441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124716468956699395558361627 187074703435049093337542441)
  ·
    refine ⟨140306027576286820003156831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187074703435049093337542441 140306027576286820003156831)
    ·
      refine ⟨210459041364430230004735247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140306027576286820003156831 210459041364430230004735247)
      ·
        refine ⟨315688562046645345007102871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210459041364430230004735247 315688562046645345007102871)
        ·
          refine ⟨473532843069968017510654307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315688562046645345007102871 473532843069968017510654307)
          ·
            refine ⟨710299264604952026265981461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473532843069968017510654307 710299264604952026265981461)
            ·
              refine ⟨33295278028357126231217881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 710299264604952026265981461 33295278028357126231217881)
              ·
                refine ⟨24971458521267844673413411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33295278028357126231217881 24971458521267844673413411)
                ·
                  refine ⟨37457187781901767010120117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24971458521267844673413411 37457187781901767010120117)
                  ·
                    refine ⟨3511611354553290657198761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37457187781901767010120117 3511611354553290657198761)
                    ·
                      refine ⟨2633708515914967992899071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3511611354553290657198761 2633708515914967992899071)
                      ·
                        rfl

theorem cell23_5129129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 5, 2].length) (baseStart_5129129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129129 prefixEnd_5129129 := by exact prefixLift 5129129
  have htrace : WordTrace (prefixWord ++ tailWord_5129129) baseStart_5129129 baseEnd_5129129 := by
    simpa [prefixWord, tailWord_5129129, baseEnd_5129129] using wordTrace_append hprefix tailTrace_5129129
  have hstable : (prefixWord ++ tailWord_5129129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129129).length < 2 ^ (prefixWord ++ tailWord_5129129).sum := by decide
  have hdescent : baseEnd_5129129 < baseStart_5129129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129140 : List Nat := [2, 5, 2, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_5129140 : Nat := 118140960795 + 5129140 * 2 ^ 59
def prefixEnd_5129140 : Nat := 4983230072969 + 3 ^ 40 * 5129140 * 2
def baseEnd_5129140 : Nat := 2633714164202167449861521

theorem tailTrace_5129140 : CollatzResearch.WordTrace tailWord_5129140 prefixEnd_5129140 2633714164202167449861521 := by
  unfold tailWord_5129140
  simp only [CollatzResearch.WordTrace]
  refine ⟨93537552319004621108096437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124716736425339494810795249 93537552319004621108096437)
  ·
    refine ⟨8769145529906683228884041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93537552319004621108096437 8769145529906683228884041)
    ·
      refine ⟨6576859147430012421663031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8769145529906683228884041 6576859147430012421663031)
      ·
        refine ⟨9865288721145018632494547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6576859147430012421663031 9865288721145018632494547)
        ·
          refine ⟨14797933081717527948741821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9865288721145018632494547 14797933081717527948741821)
          ·
            refine ⟨5549224905644072980778183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14797933081717527948741821 5549224905644072980778183)
            ·
              refine ⟨8323837358466109471167275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5549224905644072980778183 8323837358466109471167275)
              ·
                refine ⟨12485756037699164206750913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8323837358466109471167275 12485756037699164206750913)
                ·
                  refine ⟨9364317028274373155063185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12485756037699164206750913 9364317028274373155063185)
                  ·
                    refine ⟨7023237771205779866297389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9364317028274373155063185 7023237771205779866297389)
                    ·
                      refine ⟨2633714164202167449861521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7023237771205779866297389 2633714164202167449861521)
                      ·
                        rfl

theorem cell23_5129140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_5129140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129140 prefixEnd_5129140 := by exact prefixLift 5129140
  have htrace : WordTrace (prefixWord ++ tailWord_5129140) baseStart_5129140 baseEnd_5129140 := by
    simpa [prefixWord, tailWord_5129140, baseEnd_5129140] using wordTrace_append hprefix tailTrace_5129140
  have hstable : (prefixWord ++ tailWord_5129140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129140).length < 2 ^ (prefixWord ++ tailWord_5129140).sum := by decide
  have hdescent : baseEnd_5129140 < baseStart_5129140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129169 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 4, 4]
def baseStart_5129169 : Nat := 118140960795 + 5129169 * 2 ^ 59
def prefixEnd_5129169 : Nat := 4983230072969 + 3 ^ 40 * 5129169 * 2
def baseEnd_5129169 : Nat := 877909685047049278799629

theorem tailTrace_5129169 : CollatzResearch.WordTrace tailWord_5129169 prefixEnd_5129169 877909685047049278799629 := by
  unfold tailWord_5129169
  simp only [CollatzResearch.WordTrace]
  refine ⟨187076162354904180168998561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124717441569936120112665707 187076162354904180168998561)
  ·
    refine ⟨140307121766178135126748921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187076162354904180168998561 140307121766178135126748921)
    ·
      refine ⟨105230341324633601345061691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140307121766178135126748921 105230341324633601345061691)
      ·
        refine ⟨157845511986950402017592537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105230341324633601345061691 157845511986950402017592537)
        ·
          refine ⟨118384133990212801513194403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157845511986950402017592537 118384133990212801513194403)
          ·
            refine ⟨177576200985319202269791605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118384133990212801513194403 177576200985319202269791605)
            ·
              refine ⟨16647768842373675212792963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 177576200985319202269791605 16647768842373675212792963)
              ·
                refine ⟨24971653263560512819189445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16647768842373675212792963 24971653263560512819189445)
                ·
                  refine ⟨4682184986917596153598021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24971653263560512819189445 4682184986917596153598021)
                  ·
                    refine ⟨877909685047049278799629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4682184986917596153598021 877909685047049278799629)
                    ·
                      rfl

theorem cell23_5129169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 4].length) (baseStart_5129169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129169 prefixEnd_5129169 := by exact prefixLift 5129169
  have htrace : WordTrace (prefixWord ++ tailWord_5129169) baseStart_5129169 baseEnd_5129169 := by
    simpa [prefixWord, tailWord_5129169, baseEnd_5129169] using wordTrace_append hprefix tailTrace_5129169
  have hstable : (prefixWord ++ tailWord_5129169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129169).length < 2 ^ (prefixWord ++ tailWord_5129169).sum := by decide
  have hdescent : baseEnd_5129169 < baseStart_5129169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129170 : List Nat := [3, 2, 2, 3, 1, 1, 2, 4, 1, 1, 3]
def baseStart_5129170 : Nat := 118140960795 + 5129170 * 2 ^ 59
def prefixEnd_5129170 : Nat := 4983230072969 + 3 ^ 40 * 5129170 * 2
def baseEnd_5129170 : Nat := 2633729568621802332486383

theorem tailTrace_5129170 : CollatzResearch.WordTrace tailWord_5129170 prefixEnd_5129170 2633729568621802332486383 := by
  unfold tailWord_5129170
  simp only [CollatzResearch.WordTrace]
  refine ⟨46769049706975139334946241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124717465885267038226523309 46769049706975139334946241)
  ·
    refine ⟨35076787280231354501209681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46769049706975139334946241 35076787280231354501209681)
    ·
      refine ⟨26307590460173515875907261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35076787280231354501209681 26307590460173515875907261)
      ·
        refine ⟨9865346422565068453465223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26307590460173515875907261 9865346422565068453465223)
        ·
          refine ⟨14798019633847602680197835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9865346422565068453465223 14798019633847602680197835)
          ·
            refine ⟨22197029450771404020296753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14798019633847602680197835 22197029450771404020296753)
            ·
              refine ⟨16647772088078553015222565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22197029450771404020296753 16647772088078553015222565)
              ·
                refine ⟨3121457266514728690354231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16647772088078553015222565 3121457266514728690354231)
                ·
                  refine ⟨4682185899772093035531347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3121457266514728690354231 4682185899772093035531347)
                  ·
                    refine ⟨7023278849658139553297021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4682185899772093035531347 7023278849658139553297021)
                    ·
                      refine ⟨2633729568621802332486383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7023278849658139553297021 2633729568621802332486383)
                      ·
                        rfl

theorem cell23_5129170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_5129170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129170 prefixEnd_5129170 := by exact prefixLift 5129170
  have htrace : WordTrace (prefixWord ++ tailWord_5129170) baseStart_5129170 baseEnd_5129170 := by
    simpa [prefixWord, tailWord_5129170, baseEnd_5129170] using wordTrace_append hprefix tailTrace_5129170
  have hstable : (prefixWord ++ tailWord_5129170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129170).length < 2 ^ (prefixWord ++ tailWord_5129170).sum := by decide
  have hdescent : baseEnd_5129170 < baseStart_5129170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129199 : List Nat := [1, 1, 2, 1, 4, 3, 4, 7]
def baseStart_5129199 : Nat := 118140960795 + 5129199 * 2 ^ 59
def prefixEnd_5129199 : Nat := 4983230072969 + 3 ^ 40 * 5129199 * 2
def baseEnd_5129199 : Nat := 97546091094843804408287

theorem tailTrace_5129199 : CollatzResearch.WordTrace tailWord_5129199 prefixEnd_5129199 97546091094843804408287 := by
  unfold tailWord_5129199
  simp only [CollatzResearch.WordTrace]
  refine ⟨187077256544795495292590651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124718171029863663528393767 187077256544795495292590651)
  ·
    refine ⟨280615884817193242938885977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187077256544795495292590651 280615884817193242938885977)
    ·
      refine ⟨210461913612894932204164483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280615884817193242938885977 210461913612894932204164483)
      ·
        refine ⟨315692870419342398306246725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210461913612894932204164483 315692870419342398306246725)
        ·
          refine ⟨59192413203626699682421261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 315692870419342398306246725 59192413203626699682421261)
          ·
            refine ⟨22197154951360012380907973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59192413203626699682421261 22197154951360012380907973)
            ·
              refine ⟨4161966553380002321420245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22197154951360012380907973 4161966553380002321420245)
              ·
                refine ⟨97546091094843804408287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4161966553380002321420245 97546091094843804408287)
                ·
                  rfl

theorem cell23_5129199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 7].length) (baseStart_5129199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129199 prefixEnd_5129199 := by exact prefixLift 5129199
  have htrace : WordTrace (prefixWord ++ tailWord_5129199) baseStart_5129199 baseEnd_5129199 := by
    simpa [prefixWord, tailWord_5129199, baseEnd_5129199] using wordTrace_append hprefix tailTrace_5129199
  have hstable : (prefixWord ++ tailWord_5129199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129199).length < 2 ^ (prefixWord ++ tailWord_5129199).sum := by decide
  have hdescent : baseEnd_5129199 < baseStart_5129199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129209 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 3, 3, 3]
def baseStart_5129209 : Nat := 118140960795 + 5129209 * 2 ^ 59
def prefixEnd_5129209 : Nat := 4983230072969 + 3 ^ 40 * 5129209 * 2
def baseEnd_5129209 : Nat := 2633749594367327679898703

theorem tailTrace_5129209 : CollatzResearch.WordTrace tailWord_5129209 prefixEnd_5129209 2633749594367327679898703 := by
  unfold tailWord_5129209
  simp only [CollatzResearch.WordTrace]
  refine ⟨187077621274759267000454681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124718414183172844666969787 187077621274759267000454681)
  ·
    refine ⟨140308215956069450250341011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187077621274759267000454681 140308215956069450250341011)
    ·
      refine ⟨210462323934104175375511517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140308215956069450250341011 210462323934104175375511517)
      ·
        refine ⟨78923371475289065765816819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210462323934104175375511517 78923371475289065765816819)
        ·
          refine ⟨118385057212933598648725229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78923371475289065765816819 118385057212933598648725229)
          ·
            refine ⟨44394396454850099493271961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118385057212933598648725229 44394396454850099493271961)
            ·
              refine ⟨33295797341137574619953971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44394396454850099493271961 33295797341137574619953971)
              ·
                refine ⟨49943696011706361929930957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33295797341137574619953971 49943696011706361929930957)
                ·
                  refine ⟨18728886004389885723724109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49943696011706361929930957 18728886004389885723724109)
                  ·
                    refine ⟨7023332251646207146396541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18728886004389885723724109 7023332251646207146396541)
                    ·
                      refine ⟨2633749594367327679898703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7023332251646207146396541 2633749594367327679898703)
                      ·
                        rfl

theorem cell23_5129209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_5129209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129209 prefixEnd_5129209 := by exact prefixLift 5129209
  have htrace : WordTrace (prefixWord ++ tailWord_5129209) baseStart_5129209 baseEnd_5129209 := by
    simpa [prefixWord, tailWord_5129209, baseEnd_5129209] using wordTrace_append hprefix tailTrace_5129209
  have hstable : (prefixWord ++ tailWord_5129209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129209).length < 2 ^ (prefixWord ++ tailWord_5129209).sum := by decide
  have hdescent : baseEnd_5129209 < baseStart_5129209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129227 : List Nat := [1, 1, 1, 1, 6, 3, 3, 2, 1, 2, 2]
def baseStart_5129227 : Nat := 118140960795 + 5129227 * 2 ^ 59
def prefixEnd_5129227 : Nat := 4983230072969 + 3 ^ 40 * 5129227 * 2
def baseEnd_5129227 : Nat := 2633758837019108609473621

theorem tailTrace_5129227 : CollatzResearch.WordTrace tailWord_5129227 prefixEnd_5129227 2633758837019108609473621 := by
  unfold tailWord_5129227
  simp only [CollatzResearch.WordTrace]
  refine ⟨187078277788694056074609935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124718851859129370716406623 187078277788694056074609935)
  ·
    refine ⟨280617416683041084111914903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187078277788694056074609935 280617416683041084111914903)
    ·
      refine ⟨420926125024561626167872355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280617416683041084111914903 420926125024561626167872355)
      ·
        refine ⟨631389187536842439251808533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420926125024561626167872355 631389187536842439251808533)
        ·
          refine ⟨29596368165789489339928525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 631389187536842439251808533 29596368165789489339928525)
          ·
            refine ⟨11098638062171058502473197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29596368165789489339928525 11098638062171058502473197)
            ·
              refine ⟨4161989273314146938427449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11098638062171058502473197 4161989273314146938427449)
              ·
                refine ⟨3121491954985610203820587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4161989273314146938427449 3121491954985610203820587)
                ·
                  refine ⟨4682237932478415305730881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3121491954985610203820587 4682237932478415305730881)
                  ·
                    refine ⟨3511678449358811479298161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4682237932478415305730881 3511678449358811479298161)
                    ·
                      refine ⟨2633758837019108609473621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3511678449358811479298161 2633758837019108609473621)
                      ·
                        rfl

theorem cell23_5129227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 1, 2, 2].length) (baseStart_5129227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129227 prefixEnd_5129227 := by exact prefixLift 5129227
  have htrace : WordTrace (prefixWord ++ tailWord_5129227) baseStart_5129227 baseEnd_5129227 := by
    simpa [prefixWord, tailWord_5129227, baseEnd_5129227] using wordTrace_append hprefix tailTrace_5129227
  have hstable : (prefixWord ++ tailWord_5129227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129227).length < 2 ^ (prefixWord ++ tailWord_5129227).sum := by decide
  have hdescent : baseEnd_5129227 < baseStart_5129227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129279 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 4]
def baseStart_5129279 : Nat := 118140960795 + 5129279 * 2 ^ 59
def prefixEnd_5129279 : Nat := 4983230072969 + 3 ^ 40 * 5129279 * 2
def baseEnd_5129279 : Nat := 2633785538013142406023381

theorem tailTrace_5129279 : CollatzResearch.WordTrace tailWord_5129279 prefixEnd_5129279 2633785538013142406023381 := by
  unfold tailWord_5129279
  simp only [CollatzResearch.WordTrace]
  refine ⟨187080174384505668955502891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124720116256337112637001927 187080174384505668955502891)
  ·
    refine ⟨280620261576758503433254337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187080174384505668955502891 280620261576758503433254337)
    ·
      refine ⟨210465196182568877574940753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280620261576758503433254337 210465196182568877574940753)
      ·
        refine ⟨157848897136926658181205565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210465196182568877574940753 157848897136926658181205565)
        ·
          refine ⟨59193336426347496817952087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157848897136926658181205565 59193336426347496817952087)
          ·
            refine ⟨88790004639521245226928131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59193336426347496817952087 88790004639521245226928131)
            ·
              refine ⟨133185006959281867840392197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88790004639521245226928131 133185006959281867840392197)
              ·
                refine ⟨24972188804865350220073537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133185006959281867840392197 24972188804865350220073537)
                ·
                  refine ⟨18729141603649012665055153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24972188804865350220073537 18729141603649012665055153)
                  ·
                    refine ⟨14046856202736759498791365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18729141603649012665055153 14046856202736759498791365)
                    ·
                      refine ⟨2633785538013142406023381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14046856202736759498791365 2633785538013142406023381)
                      ·
                        rfl

theorem cell23_5129279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_5129279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129279 prefixEnd_5129279 := by exact prefixLift 5129279
  have htrace : WordTrace (prefixWord ++ tailWord_5129279) baseStart_5129279 baseEnd_5129279 := by
    simpa [prefixWord, tailWord_5129279, baseEnd_5129279] using wordTrace_append hprefix tailTrace_5129279
  have hstable : (prefixWord ++ tailWord_5129279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129279).length < 2 ^ (prefixWord ++ tailWord_5129279).sum := by decide
  have hdescent : baseEnd_5129279 < baseStart_5129279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129299 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 3]
def baseStart_5129299 : Nat := 118140960795 + 5129299 * 2 ^ 59
def prefixEnd_5129299 : Nat := 4983230072969 + 3 ^ 40 * 5129299 * 2
def baseEnd_5129299 : Nat := 2633795807626232327773289

theorem tailTrace_5129299 : CollatzResearch.WordTrace tailWord_5129299 prefixEnd_5129299 2633795807626232327773289 := by
  unfold tailWord_5129299
  simp only [CollatzResearch.WordTrace]
  refine ⟨187080903844433212371230951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124720602562955474914153967 187080903844433212371230951)
  ·
    refine ⟨280621355766649818556846427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187080903844433212371230951 280621355766649818556846427)
    ·
      refine ⟨420932033649974727835269641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280621355766649818556846427 420932033649974727835269641)
      ·
        refine ⟨315699025237481045876452231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420932033649974727835269641 315699025237481045876452231)
        ·
          refine ⟨473548537856221568814678347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315699025237481045876452231 473548537856221568814678347)
          ·
            refine ⟨710322806784332353222017521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473548537856221568814678347 710322806784332353222017521)
            ·
              refine ⟨532742105088249264916513141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 710322806784332353222017521 532742105088249264916513141)
              ·
                refine ⟨49944572352023368585923107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 532742105088249264916513141 49944572352023368585923107)
                ·
                  refine ⟨74916858528035052878884661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49944572352023368585923107 74916858528035052878884661)
                  ·
                    refine ⟨7023455487003286207395437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74916858528035052878884661 7023455487003286207395437)
                    ·
                      refine ⟨2633795807626232327773289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7023455487003286207395437 2633795807626232327773289)
                      ·
                        rfl

theorem cell23_5129299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 3].length) (baseStart_5129299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129299 prefixEnd_5129299 := by exact prefixLift 5129299
  have htrace : WordTrace (prefixWord ++ tailWord_5129299) baseStart_5129299 baseEnd_5129299 := by
    simpa [prefixWord, tailWord_5129299, baseEnd_5129299] using wordTrace_append hprefix tailTrace_5129299
  have hstable : (prefixWord ++ tailWord_5129299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129299).length < 2 ^ (prefixWord ++ tailWord_5129299).sum := by decide
  have hdescent : baseEnd_5129299 < baseStart_5129299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129300 : List Nat := [2, 4, 1, 1, 1, 1, 4, 3, 2, 2, 2]
def baseStart_5129300 : Nat := 118140960795 + 5129300 * 2 ^ 59
def prefixEnd_5129300 : Nat := 4983230072969 + 3 ^ 40 * 5129300 * 2
def baseEnd_5129300 : Nat := 2633796321106886823860785

theorem tailTrace_5129300 : CollatzResearch.WordTrace tailWord_5129300 prefixEnd_5129300 2633796321106886823860785 := by
  unfold tailWord_5129300
  simp only [CollatzResearch.WordTrace]
  refine ⟨93540470158714794771008677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124720626878286393028011569 93540470158714794771008677)
  ·
    refine ⟨17538838154759024019564127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93540470158714794771008677 17538838154759024019564127)
    ·
      refine ⟨26308257232138536029346191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17538838154759024019564127 26308257232138536029346191)
      ·
        refine ⟨39462385848207804044019287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26308257232138536029346191 39462385848207804044019287)
        ·
          refine ⟨59193578772311706066028931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39462385848207804044019287 59193578772311706066028931)
          ·
            refine ⟨88790368158467559099043397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59193578772311706066028931 88790368158467559099043397)
            ·
              refine ⟨16648194029712667331070637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88790368158467559099043397 16648194029712667331070637)
              ·
                refine ⟨6243072761142250249151489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16648194029712667331070637 6243072761142250249151489)
                ·
                  refine ⟨4682304570856687686863617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6243072761142250249151489 4682304570856687686863617)
                  ·
                    refine ⟨3511728428142515765147713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4682304570856687686863617 3511728428142515765147713)
                    ·
                      refine ⟨2633796321106886823860785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3511728428142515765147713 2633796321106886823860785)
                      ·
                        rfl

theorem cell23_5129300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_5129300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129300 prefixEnd_5129300 := by exact prefixLift 5129300
  have htrace : WordTrace (prefixWord ++ tailWord_5129300) baseStart_5129300 baseEnd_5129300 := by
    simpa [prefixWord, tailWord_5129300, baseEnd_5129300] using wordTrace_append hprefix tailTrace_5129300
  have hstable : (prefixWord ++ tailWord_5129300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129300).length < 2 ^ (prefixWord ++ tailWord_5129300).sum := by decide
  have hdescent : baseEnd_5129300 < baseStart_5129300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129329 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 1, 2, 5]
def baseStart_5129329 : Nat := 118140960795 + 5129329 * 2 ^ 59
def prefixEnd_5129329 : Nat := 4983230072969 + 3 ^ 40 * 5129329 * 2
def baseEnd_5129329 : Nat := 2633811212045867210398151

theorem tailTrace_5129329 : CollatzResearch.WordTrace tailWord_5129329 prefixEnd_5129329 2633811212045867210398151 := by
  unfold tailWord_5129329
  simp only [CollatzResearch.WordTrace]
  refine ⟨187081998034324527494823041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124721332022883018329882027 187081998034324527494823041)
  ·
    refine ⟨140311498525743395621117281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187081998034324527494823041 140311498525743395621117281)
    ·
      refine ⟨105233623894307546715837961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140311498525743395621117281 105233623894307546715837961)
      ·
        refine ⟨78925217920730660036878471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105233623894307546715837961 78925217920730660036878471)
        ·
          refine ⟨118387826881095990055317707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78925217920730660036878471 118387826881095990055317707)
          ·
            refine ⟨177581740321643985082976561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118387826881095990055317707 177581740321643985082976561)
            ·
              refine ⟨133186305241232988812232421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177581740321643985082976561 133186305241232988812232421)
              ·
                refine ⟨24972432232731185402293579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133186305241232988812232421 24972432232731185402293579)
                ·
                  refine ⟨37458648349096778103440369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24972432232731185402293579 37458648349096778103440369)
                  ·
                    refine ⟨28093986261822583577580277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37458648349096778103440369 28093986261822583577580277)
                    ·
                      refine ⟨2633811212045867210398151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28093986261822583577580277 2633811212045867210398151)
                      ·
                        rfl

theorem cell23_5129329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_5129329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129329 prefixEnd_5129329 := by exact prefixLift 5129329
  have htrace : WordTrace (prefixWord ++ tailWord_5129329) baseStart_5129329 baseEnd_5129329 := by
    simpa [prefixWord, tailWord_5129329, baseEnd_5129329] using wordTrace_append hprefix tailTrace_5129329
  have hstable : (prefixWord ++ tailWord_5129329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129329).length < 2 ^ (prefixWord ++ tailWord_5129329).sum := by decide
  have hdescent : baseEnd_5129329 < baseStart_5129329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129376 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 3]
def baseStart_5129376 : Nat := 118140960795 + 5129376 * 2 ^ 59
def prefixEnd_5129376 : Nat := 4983230072969 + 3 ^ 40 * 5129376 * 2
def baseEnd_5129376 : Nat := 2633835345636628526510435

theorem tailTrace_5129376 : CollatzResearch.WordTrace tailWord_5129376 prefixEnd_5129376 2633835345636628526510435 := by
  unfold tailWord_5129376
  simp only [CollatzResearch.WordTrace]
  refine ⟨93541856132577127260891991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124722474843436169681189321 93541856132577127260891991)
  ·
    refine ⟨140312784198865690891337987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93541856132577127260891991 140312784198865690891337987)
    ·
      refine ⟨210469176298298536337006981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140312784198865690891337987 210469176298298536337006981)
      ·
        refine ⟨39462970555930975563188809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210469176298298536337006981 39462970555930975563188809)
        ·
          refine ⟨29597227916948231672391607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39462970555930975563188809 29597227916948231672391607)
          ·
            refine ⟨44395841875422347508587411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29597227916948231672391607 44395841875422347508587411)
            ·
              refine ⟨66593762813133521262881117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44395841875422347508587411 66593762813133521262881117)
              ·
                refine ⟨24972661054925070473580419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66593762813133521262881117 24972661054925070473580419)
                ·
                  refine ⟨37458991582387605710370629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24972661054925070473580419 37458991582387605710370629)
                  ·
                    refine ⟨7023560921697676070694493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37458991582387605710370629 7023560921697676070694493)
                    ·
                      refine ⟨2633835345636628526510435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7023560921697676070694493 2633835345636628526510435)
                      ·
                        rfl

theorem cell23_5129376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_5129376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129376 prefixEnd_5129376 := by exact prefixLift 5129376
  have htrace : WordTrace (prefixWord ++ tailWord_5129376) baseStart_5129376 baseEnd_5129376 := by
    simpa [prefixWord, tailWord_5129376, baseEnd_5129376] using wordTrace_append hprefix tailTrace_5129376
  have hstable : (prefixWord ++ tailWord_5129376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129376).length < 2 ^ (prefixWord ++ tailWord_5129376).sum := by decide
  have hdescent : baseEnd_5129376 < baseStart_5129376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129393 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 4, 2, 3]
def baseStart_5129393 : Nat := 118140960795 + 5129393 * 2 ^ 59
def prefixEnd_5129393 : Nat := 4983230072969 + 3 ^ 40 * 5129393 * 2
def baseEnd_5129393 : Nat := 2633844074807754959997857

theorem tailTrace_5129393 : CollatzResearch.WordTrace tailWord_5129393 prefixEnd_5129393 2633844074807754959997857 := by
  unfold tailWord_5129393
  simp only [CollatzResearch.WordTrace]
  refine ⟨187084332306092666425152833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124722888204061777616768555 187084332306092666425152833)
  ·
    refine ⟨140313249229569499818864625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187084332306092666425152833 140313249229569499818864625)
    ·
      refine ⟨105234936922177124864148469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140313249229569499818864625 105234936922177124864148469)
      ·
        refine ⟨9865775336454105456013919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105234936922177124864148469 9865775336454105456013919)
        ·
          refine ⟨14798663004681158184020879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9865775336454105456013919 14798663004681158184020879)
          ·
            refine ⟨22197994507021737276031319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14798663004681158184020879 22197994507021737276031319)
            ·
              refine ⟨33296991760532605914046979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22197994507021737276031319 33296991760532605914046979)
              ·
                refine ⟨49945487640798908871070469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33296991760532605914046979 49945487640798908871070469)
                ·
                  refine ⟨9364778932649795413325713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49945487640798908871070469 9364778932649795413325713)
                  ·
                    refine ⟨7023584199487346559994285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9364778932649795413325713 7023584199487346559994285)
                    ·
                      refine ⟨2633844074807754959997857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7023584199487346559994285 2633844074807754959997857)
                      ·
                        rfl

theorem cell23_5129393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_5129393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129393 prefixEnd_5129393 := by exact prefixLift 5129393
  have htrace : WordTrace (prefixWord ++ tailWord_5129393) baseStart_5129393 baseEnd_5129393 := by
    simpa [prefixWord, tailWord_5129393, baseEnd_5129393] using wordTrace_append hprefix tailTrace_5129393
  have hstable : (prefixWord ++ tailWord_5129393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129393).length < 2 ^ (prefixWord ++ tailWord_5129393).sum := by decide
  have hdescent : baseEnd_5129393 < baseStart_5129393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129419 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 7]
def baseStart_5129419 : Nat := 118140960795 + 5129419 * 2 ^ 59
def prefixEnd_5129419 : Nat := 4983230072969 + 3 ^ 40 * 5129419 * 2
def baseEnd_5129419 : Nat := 2633857425304771858272737

theorem tailTrace_5129419 : CollatzResearch.WordTrace tailWord_5129419 prefixEnd_5129419 2633857425304771858272737 := by
  unfold tailWord_5129419
  simp only [CollatzResearch.WordTrace]
  refine ⟨187085280603998472865599311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124723520402665648577066207 187085280603998472865599311)
  ·
    refine ⟨280627920905997709298398967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187085280603998472865599311 280627920905997709298398967)
    ·
      refine ⟨420941881358996563947598451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280627920905997709298398967 420941881358996563947598451)
      ·
        refine ⟨631412822038494845921397677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420941881358996563947598451 631412822038494845921397677)
        ·
          refine ⟨236779808264435567220524129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 631412822038494845921397677 236779808264435567220524129)
          ·
            refine ⟨177584856198326675415393097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236779808264435567220524129 177584856198326675415393097)
            ·
              refine ⟨133188642148745006561544823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177584856198326675415393097 133188642148745006561544823)
              ·
                refine ⟨199782963223117509842317235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133188642148745006561544823 199782963223117509842317235)
                ·
                  refine ⟨299674444834676264763475853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 199782963223117509842317235 299674444834676264763475853)
                  ·
                    refine ⟨112377916813003599286303445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 299674444834676264763475853 112377916813003599286303445)
                    ·
                      refine ⟨2633857425304771858272737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112377916813003599286303445 2633857425304771858272737)
                      ·
                        rfl

theorem cell23_5129419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 7].length) (baseStart_5129419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129419 prefixEnd_5129419 := by exact prefixLift 5129419
  have htrace : WordTrace (prefixWord ++ tailWord_5129419) baseStart_5129419 baseEnd_5129419 := by
    simpa [prefixWord, tailWord_5129419, baseEnd_5129419] using wordTrace_append hprefix tailTrace_5129419
  have hstable : (prefixWord ++ tailWord_5129419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129419).length < 2 ^ (prefixWord ++ tailWord_5129419).sum := by decide
  have hdescent : baseEnd_5129419 < baseStart_5129419 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129450 : List Nat := [3, 1, 3, 1, 1, 3, 2, 2, 2, 3, 2]
def baseStart_5129450 : Nat := 118140960795 + 5129450 * 2 ^ 59
def prefixEnd_5129450 : Nat := 4983230072969 + 3 ^ 40 * 5129450 * 2
def baseEnd_5129450 : Nat := 2633873343205061236985095

theorem tailTrace_5129450 : CollatzResearch.WordTrace tailWord_5129450 prefixEnd_5129450 2633873343205061236985095 := by
  unfold tailWord_5129450
  simp only [CollatzResearch.WordTrace]
  refine ⟨46771602816721541289994451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124724274177924110106651869 46771602816721541289994451)
  ·
    refine ⟨70157404225082311934991677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46771602816721541289994451 70157404225082311934991677)
    ·
      refine ⟨26309026584405866975621879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70157404225082311934991677 26309026584405866975621879)
      ·
        refine ⟨39463539876608800463432819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26309026584405866975621879 39463539876608800463432819)
        ·
          refine ⟨59195309814913200695149229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39463539876608800463432819 59195309814913200695149229)
          ·
            refine ⟨22198241180592450260680961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59195309814913200695149229 22198241180592450260680961)
            ·
              refine ⟨16648680885444337695510721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22198241180592450260680961 16648680885444337695510721)
              ·
                refine ⟨12486510664083253271633041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16648680885444337695510721 12486510664083253271633041)
                ·
                  refine ⟨9364882998062439953724781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12486510664083253271633041 9364882998062439953724781)
                  ·
                    refine ⟨3511831124273414982646793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9364882998062439953724781 3511831124273414982646793)
                    ·
                      refine ⟨2633873343205061236985095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3511831124273414982646793 2633873343205061236985095)
                      ·
                        rfl

theorem cell23_5129450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_5129450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129450 prefixEnd_5129450 := by exact prefixLift 5129450
  have htrace : WordTrace (prefixWord ++ tailWord_5129450) baseStart_5129450 baseEnd_5129450 := by
    simpa [prefixWord, tailWord_5129450, baseEnd_5129450] using wordTrace_append hprefix tailTrace_5129450
  have hstable : (prefixWord ++ tailWord_5129450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129450).length < 2 ^ (prefixWord ++ tailWord_5129450).sum := by decide
  have hdescent : baseEnd_5129450 < baseStart_5129450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129466 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5]
def baseStart_5129466 : Nat := 118140960795 + 5129466 * 2 ^ 59
def prefixEnd_5129466 : Nat := 4983230072969 + 3 ^ 40 * 5129466 * 2
def baseEnd_5129466 : Nat := 2633881558895533174385021

theorem tailTrace_5129466 : CollatzResearch.WordTrace tailWord_5129466 prefixEnd_5129466 2633881558895533174385021 := by
  unfold tailWord_5129466
  simp only [CollatzResearch.WordTrace]
  refine ⟨46771748708707049973140063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124724663223218799928373501 46771748708707049973140063)
  ·
    refine ⟨70157623063060574959710095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46771748708707049973140063 70157623063060574959710095)
    ·
      refine ⟨105236434594590862439565143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70157623063060574959710095 105236434594590862439565143)
      ·
        refine ⟨157854651891886293659347715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105236434594590862439565143 157854651891886293659347715)
        ·
          refine ⟨236781977837829440489021573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157854651891886293659347715 236781977837829440489021573)
          ·
            refine ⟨44396620844593020091691545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 236781977837829440489021573 44396620844593020091691545)
            ·
              refine ⟨33297465633444765068768659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44396620844593020091691545 33297465633444765068768659)
              ·
                refine ⟨49946198450167147603152989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33297465633444765068768659 49946198450167147603152989)
                ·
                  refine ⟨18729824418812680351182371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49946198450167147603152989 18729824418812680351182371)
                  ·
                    refine ⟨28094736628219020526773557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18729824418812680351182371 28094736628219020526773557)
                    ·
                      refine ⟨2633881558895533174385021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28094736628219020526773557 2633881558895533174385021)
                      ·
                        rfl

theorem cell23_5129466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_5129466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129466 prefixEnd_5129466 := by exact prefixLift 5129466
  have htrace : WordTrace (prefixWord ++ tailWord_5129466) baseStart_5129466 baseEnd_5129466 := by
    simpa [prefixWord, tailWord_5129466, baseEnd_5129466] using wordTrace_append hprefix tailTrace_5129466
  have hstable : (prefixWord ++ tailWord_5129466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129466).length < 2 ^ (prefixWord ++ tailWord_5129466).sum := by decide
  have hdescent : baseEnd_5129466 < baseStart_5129466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129473 : List Nat := [1, 2, 4, 1, 1, 4, 2, 1, 1, 6]
def baseStart_5129473 : Nat := 118140960795 + 5129473 * 2 ^ 59
def prefixEnd_5129473 : Nat := 4983230072969 + 3 ^ 40 * 5129473 * 2
def baseEnd_5129473 : Nat := 877961717753371548999163

theorem tailTrace_5129473 : CollatzResearch.WordTrace tailWord_5129473 prefixEnd_5129473 877961717753371548999163 := by
  unfold tailWord_5129473
  simp only [CollatzResearch.WordTrace]
  refine ⟨187087250145802840088065073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124724833430535226725376715 187087250145802840088065073)
  ·
    refine ⟨140315437609352130066048805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187087250145802840088065073 140315437609352130066048805)
    ·
      refine ⟨26309144551753524387384151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140315437609352130066048805 26309144551753524387384151)
      ·
        refine ⟨39463716827630286581076227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26309144551753524387384151 39463716827630286581076227)
        ·
          refine ⟨59195575241445429871614341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39463716827630286581076227 59195575241445429871614341)
          ·
            refine ⟨11099170357771018100927689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59195575241445429871614341 11099170357771018100927689)
            ·
              refine ⟨8324377768328263575695767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11099170357771018100927689 8324377768328263575695767)
              ·
                refine ⟨12486566652492395363543651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8324377768328263575695767 12486566652492395363543651)
                ·
                  refine ⟨18729849978738593045315477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12486566652492395363543651 18729849978738593045315477)
                  ·
                    refine ⟨877961717753371548999163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18729849978738593045315477 877961717753371548999163)
                    ·
                      rfl

theorem cell23_5129473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_5129473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129473 prefixEnd_5129473 := by exact prefixLift 5129473
  have htrace : WordTrace (prefixWord ++ tailWord_5129473) baseStart_5129473 baseEnd_5129473 := by
    simpa [prefixWord, tailWord_5129473, baseEnd_5129473] using wordTrace_append hprefix tailTrace_5129473
  have hstable : (prefixWord ++ tailWord_5129473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129473).length < 2 ^ (prefixWord ++ tailWord_5129473).sum := by decide
  have hdescent : baseEnd_5129473 < baseStart_5129473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129483 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 3]
def baseStart_5129483 : Nat := 118140960795 + 5129483 * 2 ^ 59
def prefixEnd_5129483 : Nat := 4983230072969 + 3 ^ 40 * 5129483 * 2
def baseEnd_5129483 : Nat := 2633890288066659607872443

theorem tailTrace_5129483 : CollatzResearch.WordTrace tailWord_5129483 prefixEnd_5129483 2633890288066659607872443 := by
  unfold tailWord_5129483
  simp only [CollatzResearch.WordTrace]
  refine ⟨187087614875766611795929103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124725076583844407863952735 187087614875766611795929103)
  ·
    refine ⟨280631422313649917693893655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187087614875766611795929103 280631422313649917693893655)
    ·
      refine ⟨420947133470474876540840483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280631422313649917693893655 420947133470474876540840483)
      ·
        refine ⟨631420700205712314811260725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420947133470474876540840483 631420700205712314811260725)
        ·
          refine ⟨59195690644285529513555693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 631420700205712314811260725 59195690644285529513555693)
          ·
            refine ⟨22198383991607073567583385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59195690644285529513555693 22198383991607073567583385)
            ·
              refine ⟨16648787993705305175687539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22198383991607073567583385 16648787993705305175687539)
              ·
                refine ⟨24973181990557957763531309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16648787993705305175687539 24973181990557957763531309)
                ·
                  refine ⟨9364943246459234161324241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24973181990557957763531309 9364943246459234161324241)
                  ·
                    refine ⟨7023707434844425620993181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9364943246459234161324241 7023707434844425620993181)
                    ·
                      refine ⟨2633890288066659607872443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7023707434844425620993181 2633890288066659607872443)
                      ·
                        rfl

theorem cell23_5129483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 3].length) (baseStart_5129483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129483 prefixEnd_5129483 := by exact prefixLift 5129483
  have htrace : WordTrace (prefixWord ++ tailWord_5129483) baseStart_5129483 baseEnd_5129483 := by
    simpa [prefixWord, tailWord_5129483, baseEnd_5129483] using wordTrace_append hprefix tailTrace_5129483
  have hstable : (prefixWord ++ tailWord_5129483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129483).length < 2 ^ (prefixWord ++ tailWord_5129483).sum := by decide
  have hdescent : baseEnd_5129483 < baseStart_5129483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129514 : List Nat := [3, 1, 4, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_5129514 : Nat := 118140960795 + 5129514 * 2 ^ 59
def prefixEnd_5129514 : Nat := 4983230072969 + 3 ^ 40 * 5129514 * 2
def baseEnd_5129514 : Nat := 2633906205966948986584801

theorem tailTrace_5129514 : CollatzResearch.WordTrace tailWord_5129514 prefixEnd_5129514 2633906205966948986584801 := by
  unfold tailWord_5129514
  simp only [CollatzResearch.WordTrace]
  refine ⟨46772186384663576022576899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124725830359102869393538397 46772186384663576022576899)
  ·
    refine ⟨70158279576995364033865349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46772186384663576022576899 70158279576995364033865349)
    ·
      refine ⟨13154677420686630756349753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70158279576995364033865349 13154677420686630756349753)
      ·
        refine ⟨9866008065514973067262315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13154677420686630756349753 9866008065514973067262315)
        ·
          refine ⟨14799012098272459600893473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9866008065514973067262315 14799012098272459600893473)
          ·
            refine ⟨11099259073704344700670105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14799012098272459600893473 11099259073704344700670105)
            ·
              refine ⟨8324444305278258525502579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11099259073704344700670105 8324444305278258525502579)
              ·
                refine ⟨12486666457917387788253869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8324444305278258525502579 12486666457917387788253869)
                ·
                  refine ⟨4682499921719020420595201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12486666457917387788253869 4682499921719020420595201)
                  ·
                    refine ⟨3511874941289265315446401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4682499921719020420595201 3511874941289265315446401)
                    ·
                      refine ⟨2633906205966948986584801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3511874941289265315446401 2633906205966948986584801)
                      ·
                        rfl

theorem cell23_5129514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_5129514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129514 prefixEnd_5129514 := by exact prefixLift 5129514
  have htrace : WordTrace (prefixWord ++ tailWord_5129514) baseStart_5129514 baseEnd_5129514 := by
    simpa [prefixWord, tailWord_5129514, baseEnd_5129514] using wordTrace_append hprefix tailTrace_5129514
  have hstable : (prefixWord ++ tailWord_5129514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129514).length < 2 ^ (prefixWord ++ tailWord_5129514).sum := by decide
  have hdescent : baseEnd_5129514 < baseStart_5129514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129546 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 1, 8]
def baseStart_5129546 : Nat := 118140960795 + 5129546 * 2 ^ 59
def prefixEnd_5129546 : Nat := 4983230072969 + 3 ^ 40 * 5129546 * 2
def baseEnd_5129546 : Nat := 877974212449297620461551

theorem tailTrace_5129546 : CollatzResearch.WordTrace tailWord_5129546 prefixEnd_5129546 877974212449297620461551 := by
  unfold tailWord_5129546
  simp only [CollatzResearch.WordTrace]
  refine ⟨46772478168634593388868123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124726608449692249036981661 46772478168634593388868123)
  ·
    refine ⟨70158717252951890083302185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46772478168634593388868123 70158717252951890083302185)
    ·
      refine ⟨52619037939713917562476639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70158717252951890083302185 52619037939713917562476639)
      ·
        refine ⟨78928556909570876343714959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52619037939713917562476639 78928556909570876343714959)
        ·
          refine ⟨118392835364356314515572439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78928556909570876343714959 118392835364356314515572439)
          ·
            refine ⟨177589253046534471773358659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118392835364356314515572439 177589253046534471773358659)
            ·
              refine ⟨266383879569801707660037989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177589253046534471773358659 266383879569801707660037989)
              ·
                refine ⟨49946977419337820186257123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266383879569801707660037989 49946977419337820186257123)
                ·
                  refine ⟨74920466129006730279385685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49946977419337820186257123 74920466129006730279385685)
                  ·
                    refine ⟨877974212449297620461551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74920466129006730279385685 877974212449297620461551)
                    ·
                      rfl

theorem cell23_5129546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_5129546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129546 prefixEnd_5129546 := by exact prefixLift 5129546
  have htrace : WordTrace (prefixWord ++ tailWord_5129546) baseStart_5129546 baseEnd_5129546 := by
    simpa [prefixWord, tailWord_5129546, baseEnd_5129546] using wordTrace_append hprefix tailTrace_5129546
  have hstable : (prefixWord ++ tailWord_5129546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129546).length < 2 ^ (prefixWord ++ tailWord_5129546).sum := by decide
  have hdescent : baseEnd_5129546 < baseStart_5129546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129557 : List Nat := [1, 3, 2, 2, 3, 1, 2, 3, 1, 3, 2]
def baseStart_5129557 : Nat := 118140960795 + 5129557 * 2 ^ 59
def prefixEnd_5129557 : Nat := 4983230072969 + 3 ^ 40 * 5129557 * 2
def baseEnd_5129557 : Nat := 2633928285635092318347103

theorem tailTrace_5129557 : CollatzResearch.WordTrace tailWord_5129557 prefixEnd_5129557 2633928285635092318347103 := by
  unfold tailWord_5129557
  simp only [CollatzResearch.WordTrace]
  refine ⟨187090313877498522434122925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124726875918332348289415283 187090313877498522434122925)
  ·
    refine ⟨70158867704061945912796097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187090313877498522434122925 70158867704061945912796097)
    ·
      refine ⟨52619150778046459434597073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70158867704061945912796097 52619150778046459434597073)
      ·
        refine ⟨39464363083534844575947805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52619150778046459434597073 39464363083534844575947805)
        ·
          refine ⟨14799136156325566715980427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39464363083534844575947805 14799136156325566715980427)
          ·
            refine ⟨22198704234488350073970641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14799136156325566715980427 22198704234488350073970641)
            ·
              refine ⟨16649028175866262555477981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22198704234488350073970641 16649028175866262555477981)
              ·
                refine ⟨6243385565949848458304243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16649028175866262555477981 6243385565949848458304243)
                ·
                  refine ⟨9365078348924772687456365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6243385565949848458304243 9365078348924772687456365)
                  ·
                    refine ⟨3511904380846789757796137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9365078348924772687456365 3511904380846789757796137)
                    ·
                      refine ⟨2633928285635092318347103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3511904380846789757796137 2633928285635092318347103)
                      ·
                        rfl

theorem cell23_5129557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_5129557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129557 prefixEnd_5129557 := by exact prefixLift 5129557
  have htrace : WordTrace (prefixWord ++ tailWord_5129557) baseStart_5129557 baseEnd_5129557 := by
    simpa [prefixWord, tailWord_5129557, baseEnd_5129557] using wordTrace_append hprefix tailTrace_5129557
  have hstable : (prefixWord ++ tailWord_5129557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129557).length < 2 ^ (prefixWord ++ tailWord_5129557).sum := by decide
  have hdescent : baseEnd_5129557 < baseStart_5129557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129565 : List Nat := [1, 4, 5, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_5129565 : Nat := 118140960795 + 5129565 * 2 ^ 59
def prefixEnd_5129565 : Nat := 4983230072969 + 3 ^ 40 * 5129565 * 2
def baseEnd_5129565 : Nat := 2633932393480328287047067

theorem tailTrace_5129565 : CollatzResearch.WordTrace tailWord_5129565 prefixEnd_5129565 2633932393480328287047067 := by
  unfold tailWord_5129565
  simp only [CollatzResearch.WordTrace]
  refine ⟨187090605661469539800414149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124727070440979693200276099 187090605661469539800414149)
  ·
    refine ⟨35079488561525538712577653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187090605661469539800414149 35079488561525538712577653)
    ·
      refine ⟨3288702052643019254304155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35079488561525538712577653 3288702052643019254304155)
      ·
        refine ⟨4933053078964528881456233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3288702052643019254304155 4933053078964528881456233)
        ·
          refine ⟨3699789809223396661092175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4933053078964528881456233 3699789809223396661092175)
          ·
            refine ⟨5549684713835094991638263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3699789809223396661092175 5549684713835094991638263)
            ·
              refine ⟨8324527070752642487457395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5549684713835094991638263 8324527070752642487457395)
              ·
                refine ⟨12486790606128963731186093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8324527070752642487457395 12486790606128963731186093)
                ·
                  refine ⟨4682546477298361399194785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12486790606128963731186093 4682546477298361399194785)
                  ·
                    refine ⟨3511909857973771049396089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4682546477298361399194785 3511909857973771049396089)
                    ·
                      refine ⟨2633932393480328287047067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3511909857973771049396089 2633932393480328287047067)
                      ·
                        rfl

theorem cell23_5129565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_5129565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129565 prefixEnd_5129565 := by exact prefixLift 5129565
  have htrace : WordTrace (prefixWord ++ tailWord_5129565) baseStart_5129565 baseEnd_5129565 := by
    simpa [prefixWord, tailWord_5129565, baseEnd_5129565] using wordTrace_append hprefix tailTrace_5129565
  have hstable : (prefixWord ++ tailWord_5129565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129565).length < 2 ^ (prefixWord ++ tailWord_5129565).sum := by decide
  have hdescent : baseEnd_5129565 < baseStart_5129565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129573 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 2, 4, 3]
def baseStart_5129573 : Nat := 118140960795 + 5129573 * 2 ^ 59
def prefixEnd_5129573 : Nat := 4983230072969 + 3 ^ 40 * 5129573 * 2
def baseEnd_5129573 : Nat := 2633936501325564255747029

theorem tailTrace_5129573 : CollatzResearch.WordTrace tailWord_5129573 prefixEnd_5129573 2633936501325564255747029 := by
  unfold tailWord_5129573
  simp only [CollatzResearch.WordTrace]
  refine ⟨187090897445440557166705373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124727264963627038111136915 187090897445440557166705373)
  ·
    refine ⟨70159086542040208937514515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187090897445440557166705373 70159086542040208937514515)
    ·
      refine ⟨105238629813060313406271773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70159086542040208937514515 105238629813060313406271773)
      ·
        refine ⟨39464486179897617527351915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105238629813060313406271773 39464486179897617527351915)
        ·
          refine ⟨59196729269846426291027873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39464486179897617527351915 59196729269846426291027873)
          ·
            refine ⟨44397546952384819718270905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59196729269846426291027873 44397546952384819718270905)
            ·
              refine ⟨33298160214288614788703179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44397546952384819718270905 33298160214288614788703179)
              ·
                refine ⟨49947240321432922183054769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33298160214288614788703179 49947240321432922183054769)
                ·
                  refine ⟨37460430241074691637291077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49947240321432922183054769 37460430241074691637291077)
                  ·
                    refine ⟨7023830670201504681992077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37460430241074691637291077 7023830670201504681992077)
                    ·
                      refine ⟨2633936501325564255747029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7023830670201504681992077 2633936501325564255747029)
                      ·
                        rfl

theorem cell23_5129573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_5129573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129573 prefixEnd_5129573 := by exact prefixLift 5129573
  have htrace : WordTrace (prefixWord ++ tailWord_5129573) baseStart_5129573 baseEnd_5129573 := by
    simpa [prefixWord, tailWord_5129573, baseEnd_5129573] using wordTrace_append hprefix tailTrace_5129573
  have hstable : (prefixWord ++ tailWord_5129573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129573).length < 2 ^ (prefixWord ++ tailWord_5129573).sum := by decide
  have hdescent : baseEnd_5129573 < baseStart_5129573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129657 : List Nat := [1, 2, 1, 4, 4, 2, 1, 1, 2, 5]
def baseStart_5129657 : Nat := 118140960795 + 5129657 * 2 ^ 59
def prefixEnd_5129657 : Nat := 4983230072969 + 3 ^ 40 * 5129657 * 2
def baseEnd_5129657 : Nat := 877993211233513975698881

theorem tailTrace_5129657 : CollatzResearch.WordTrace tailWord_5129657 prefixEnd_5129657 877993211233513975698881 := by
  unfold tailWord_5129657
  simp only [CollatzResearch.WordTrace]
  refine ⟨187093961177136239512763225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124729307451424159675175483 187093961177136239512763225)
  ·
    refine ⟨140320470882852179634572419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187093961177136239512763225 140320470882852179634572419)
    ·
      refine ⟨210480706324278269451858629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140320470882852179634572419 210480706324278269451858629)
      ·
        refine ⟨39465132435802175522223493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210480706324278269451858629 39465132435802175522223493)
        ·
          refine ⟨7399712331712907910416905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39465132435802175522223493 7399712331712907910416905)
          ·
            refine ⟨5549784248784680932812679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7399712331712907910416905 5549784248784680932812679)
            ·
              refine ⟨8324676373177021399219019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5549784248784680932812679 8324676373177021399219019)
              ·
                refine ⟨12487014559765532098828529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8324676373177021399219019 12487014559765532098828529)
                ·
                  refine ⟨9365260919824149074121397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12487014559765532098828529 9365260919824149074121397)
                  ·
                    refine ⟨877993211233513975698881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9365260919824149074121397 877993211233513975698881)
                    ·
                      rfl

theorem cell23_5129657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 5].length) (baseStart_5129657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129657 prefixEnd_5129657 := by exact prefixLift 5129657
  have htrace : WordTrace (prefixWord ++ tailWord_5129657) baseStart_5129657 baseEnd_5129657 := by
    simpa [prefixWord, tailWord_5129657, baseEnd_5129657] using wordTrace_append hprefix tailTrace_5129657
  have hstable : (prefixWord ++ tailWord_5129657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129657).length < 2 ^ (prefixWord ++ tailWord_5129657).sum := by decide
  have hdescent : baseEnd_5129657 < baseStart_5129657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129710 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_5129710 : Nat := 118140960795 + 5129710 * 2 ^ 59
def prefixEnd_5129710 : Nat := 4983230072969 + 3 ^ 40 * 5129710 * 2
def baseEnd_5129710 : Nat := 2634006848175230219733899

theorem tailTrace_5129710 : CollatzResearch.WordTrace tailWord_5129710 prefixEnd_5129710 2634006848175230219733899 := by
  unfold tailWord_5129710
  simp only [CollatzResearch.WordTrace]
  refine ⟨23386986780743028695555323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124730596163962819709628389 23386986780743028695555323)
  ·
    refine ⟨35080480171114543043332985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23386986780743028695555323 35080480171114543043332985)
    ·
      refine ⟨26310360128335907282499739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35080480171114543043332985 26310360128335907282499739)
      ·
        refine ⟨39465540192503860923749609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26310360128335907282499739 39465540192503860923749609)
        ·
          refine ⟨29599155144377895692812207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39465540192503860923749609 29599155144377895692812207)
          ·
            refine ⟨44398732716566843539218311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29599155144377895692812207 44398732716566843539218311)
            ·
              refine ⟨66598099074850265308827467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44398732716566843539218311 66598099074850265308827467)
              ·
                refine ⟨99897148612275397963241201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66598099074850265308827467 99897148612275397963241201)
                ·
                  refine ⟨74922861459206548472430901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99897148612275397963241201 74922861459206548472430901)
                  ·
                    refine ⟨7024018261800613919290397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74922861459206548472430901 7024018261800613919290397)
                    ·
                      refine ⟨2634006848175230219733899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7024018261800613919290397 2634006848175230219733899)
                      ·
                        rfl

theorem cell23_5129710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_5129710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129710 prefixEnd_5129710 := by exact prefixLift 5129710
  have htrace : WordTrace (prefixWord ++ tailWord_5129710) baseStart_5129710 baseEnd_5129710 := by
    simpa [prefixWord, tailWord_5129710, baseEnd_5129710] using wordTrace_append hprefix tailTrace_5129710
  have hstable : (prefixWord ++ tailWord_5129710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129710).length < 2 ^ (prefixWord ++ tailWord_5129710).sum := by decide
  have hdescent : baseEnd_5129710 < baseStart_5129710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129737 : List Nat := [1, 2, 1, 1, 3, 1, 5, 2, 2, 3, 2]
def baseStart_5129737 : Nat := 118140960795 + 5129737 * 2 ^ 59
def prefixEnd_5129737 : Nat := 4983230072969 + 3 ^ 40 * 5129737 * 2
def baseEnd_5129737 : Nat := 2634020712152901614096275

theorem tailTrace_5129737 : CollatzResearch.WordTrace tailWord_5129737 prefixEnd_5129737 2634020712152901614096275 := by
  unfold tailWord_5129737
  simp only [CollatzResearch.WordTrace]
  refine ⟨187096879016846413175675465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124731252677897608783783643 187096879016846413175675465)
  ·
    refine ⟨140322659262634809881756599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187096879016846413175675465 140322659262634809881756599)
    ·
      refine ⟨210483988893952214822634899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140322659262634809881756599 210483988893952214822634899)
      ·
        refine ⟨315725983340928322233952349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210483988893952214822634899 315725983340928322233952349)
        ·
          refine ⟨118397243752848120837732131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 315725983340928322233952349 118397243752848120837732131)
          ·
            refine ⟨177595865629272181256598197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118397243752848120837732131 177595865629272181256598197)
            ·
              refine ⟨16649612402744266992806081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 177595865629272181256598197 16649612402744266992806081)
              ·
                refine ⟨12487209302058200244604561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16649612402744266992806081 12487209302058200244604561)
                ·
                  refine ⟨9365406976543650183453421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12487209302058200244604561 9365406976543650183453421)
                  ·
                    refine ⟨3512027616203868818795033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9365406976543650183453421 3512027616203868818795033)
                    ·
                      refine ⟨2634020712152901614096275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3512027616203868818795033 2634020712152901614096275)
                      ·
                        rfl

theorem cell23_5129737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 3, 2].length) (baseStart_5129737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129737 prefixEnd_5129737 := by exact prefixLift 5129737
  have htrace : WordTrace (prefixWord ++ tailWord_5129737) baseStart_5129737 baseEnd_5129737 := by
    simpa [prefixWord, tailWord_5129737, baseEnd_5129737] using wordTrace_append hprefix tailTrace_5129737
  have hstable : (prefixWord ++ tailWord_5129737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129737).length < 2 ^ (prefixWord ++ tailWord_5129737).sum := by decide
  have hdescent : baseEnd_5129737 < baseStart_5129737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129784 : List Nat := [2, 1, 2, 1, 4, 3, 3, 1, 1, 1, 4]
def baseStart_5129784 : Nat := 118140960795 + 5129784 * 2 ^ 59
def prefixEnd_5129784 : Nat := 4983230072969 + 3 ^ 40 * 5129784 * 2
def baseEnd_5129784 : Nat := 2634044845743662930208559

theorem tailTrace_5129784 : CollatzResearch.WordTrace tailWord_5129784 prefixEnd_5129784 2634044845743662930208559 := by
  unfold tailWord_5129784
  simp only [CollatzResearch.WordTrace]
  refine ⟨93549296623838070101318203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124732395498450760135090937 93549296623838070101318203)
  ·
    refine ⟨140323944935757105151977305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93549296623838070101318203 140323944935757105151977305)
    ·
      refine ⟨105242958701817828863982979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140323944935757105151977305 105242958701817828863982979)
      ·
        refine ⟨157864438052726743295974469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105242958701817828863982979 157864438052726743295974469)
        ·
          refine ⟨29599582134886264367995213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157864438052726743295974469 29599582134886264367995213)
          ·
            refine ⟨11099843300582349137998205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29599582134886264367995213 11099843300582349137998205)
            ·
              refine ⟨4162441237718380926749327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11099843300582349137998205 4162441237718380926749327)
              ·
                refine ⟨6243661856577571390123991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4162441237718380926749327 6243661856577571390123991)
                ·
                  refine ⟨9365492784866357085185987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6243661856577571390123991 9365492784866357085185987)
                  ·
                    refine ⟨14048239177299535627778981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9365492784866357085185987 14048239177299535627778981)
                    ·
                      refine ⟨2634044845743662930208559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14048239177299535627778981 2634044845743662930208559)
                      ·
                        rfl

theorem cell23_5129784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 1, 1, 4].length) (baseStart_5129784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129784 prefixEnd_5129784 := by exact prefixLift 5129784
  have htrace : WordTrace (prefixWord ++ tailWord_5129784) baseStart_5129784 baseEnd_5129784 := by
    simpa [prefixWord, tailWord_5129784, baseEnd_5129784] using wordTrace_append hprefix tailTrace_5129784
  have hstable : (prefixWord ++ tailWord_5129784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129784).length < 2 ^ (prefixWord ++ tailWord_5129784).sum := by decide
  have hdescent : baseEnd_5129784 < baseStart_5129784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129838 : List Nat := [4, 1, 2, 2, 3, 2, 2, 1, 1, 2, 3]
def baseStart_5129838 : Nat := 118140960795 + 5129838 * 2 ^ 59
def prefixEnd_5129838 : Nat := 4983230072969 + 3 ^ 40 * 5129838 * 2
def baseEnd_5129838 : Nat := 2634072573699005718933311

theorem tailTrace_5129838 : CollatzResearch.WordTrace tailWord_5129838 prefixEnd_5129838 2634072573699005718933311 := by
  unfold tailWord_5129838
  simp only [CollatzResearch.WordTrace]
  refine ⟨23387570348685063428137771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124733708526320338283401445 23387570348685063428137771)
  ·
    refine ⟨35081355523027595142206657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23387570348685063428137771 35081355523027595142206657)
    ·
      refine ⟨26311016642270696356654993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35081355523027595142206657 26311016642270696356654993)
      ·
        refine ⟨19733262481703022267491245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26311016642270696356654993 19733262481703022267491245)
        ·
          refine ⟨7399973430638633350309217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19733262481703022267491245 7399973430638633350309217)
          ·
            refine ⟨5549980072978975012731913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7399973430638633350309217 5549980072978975012731913)
            ·
              refine ⟨4162485054734231259548935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5549980072978975012731913 4162485054734231259548935)
              ·
                refine ⟨6243727582101346889323403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4162485054734231259548935 6243727582101346889323403)
                ·
                  refine ⟨9365591373152020333985105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6243727582101346889323403 9365591373152020333985105)
                  ·
                    refine ⟨7024193529864015250488829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9365591373152020333985105 7024193529864015250488829)
                    ·
                      refine ⟨2634072573699005718933311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7024193529864015250488829 2634072573699005718933311)
                      ·
                        rfl

theorem cell23_5129838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_5129838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129838 prefixEnd_5129838 := by exact prefixLift 5129838
  have htrace : WordTrace (prefixWord ++ tailWord_5129838) baseStart_5129838 baseEnd_5129838 := by
    simpa [prefixWord, tailWord_5129838, baseEnd_5129838] using wordTrace_append hprefix tailTrace_5129838
  have hstable : (prefixWord ++ tailWord_5129838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129838).length < 2 ^ (prefixWord ++ tailWord_5129838).sum := by decide
  have hdescent : baseEnd_5129838 < baseStart_5129838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129987 : List Nat := [1, 1, 1, 3, 2, 2, 4, 3, 6]
def baseStart_5129987 : Nat := 118140960795 + 5129987 * 2 ^ 59
def prefixEnd_5129987 : Nat := 4983230072969 + 3 ^ 40 * 5129987 * 2
def baseEnd_5129987 : Nat := 292683231368502848441125

theorem tailTrace_5129987 : CollatzResearch.WordTrace tailWord_5129987 prefixEnd_5129987 292683231368502848441125 := by
  unfold tailWord_5129987
  simp only [CollatzResearch.WordTrace]
  refine ⟨187105997265940705872276215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124737331510627137248184143 187105997265940705872276215)
  ·
    refine ⟨280658995898911058808414323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187105997265940705872276215 280658995898911058808414323)
    ·
      refine ⟨420988493848366588212621485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280658995898911058808414323 420988493848366588212621485)
      ·
        refine ⟨157870685193137470579733057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 420988493848366588212621485 157870685193137470579733057)
        ·
          refine ⟨118403013894853102934799793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157870685193137470579733057 118403013894853102934799793)
          ·
            refine ⟨88802260421139827201099845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118403013894853102934799793 88802260421139827201099845)
            ·
              refine ⟨16650423828963717600206221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88802260421139827201099845 16650423828963717600206221)
              ·
                refine ⟨6243908935861394100077333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16650423828963717600206221 6243908935861394100077333)
                ·
                  refine ⟨292683231368502848441125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6243908935861394100077333 292683231368502848441125)
                  ·
                    rfl

theorem cell23_5129987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 6].length) (baseStart_5129987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129987 prefixEnd_5129987 := by exact prefixLift 5129987
  have htrace : WordTrace (prefixWord ++ tailWord_5129987) baseStart_5129987 baseEnd_5129987 := by
    simpa [prefixWord, tailWord_5129987, baseEnd_5129987] using wordTrace_append hprefix tailTrace_5129987
  have hstable : (prefixWord ++ tailWord_5129987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129987).length < 2 ^ (prefixWord ++ tailWord_5129987).sum := by decide
  have hdescent : baseEnd_5129987 < baseStart_5129987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5129991 : List Nat := [1, 1, 4, 4, 2, 1, 1, 2, 3, 4]
def baseStart_5129991 : Nat := 118140960795 + 5129991 * 2 ^ 59
def prefixEnd_5129991 : Nat := 4983230072969 + 3 ^ 40 * 5129991 * 2
def baseEnd_5129991 : Nat := 878050378746381206773369

theorem tailTrace_5129991 : CollatzResearch.WordTrace tailWord_5129991 prefixEnd_5129991 878050378746381206773369 := by
  unfold tailWord_5129991
  simp only [CollatzResearch.WordTrace]
  refine ⟨187106143157926214555421827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124737428771950809703614551 187106143157926214555421827)
  ·
    refine ⟨280659214736889321833132741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187106143157926214555421827 280659214736889321833132741)
    ·
      refine ⟨52623602763166747843712389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 280659214736889321833132741 52623602763166747843712389)
      ·
        refine ⟨9866925518093765220696073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52623602763166747843712389 9866925518093765220696073)
        ·
          refine ⟨7400194138570323915522055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9866925518093765220696073 7400194138570323915522055)
          ·
            refine ⟨11100291207855485873283083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7400194138570323915522055 11100291207855485873283083)
            ·
              refine ⟨16650436811783228809924625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11100291207855485873283083 16650436811783228809924625)
              ·
                refine ⟨12487827608837421607443469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16650436811783228809924625 12487827608837421607443469)
                ·
                  refine ⟨4682935353314033102791301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12487827608837421607443469 4682935353314033102791301)
                  ·
                    refine ⟨878050378746381206773369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4682935353314033102791301 878050378746381206773369)
                    ·
                      rfl

theorem cell23_5129991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_5129991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5129991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5129991 prefixEnd_5129991 := by exact prefixLift 5129991
  have htrace : WordTrace (prefixWord ++ tailWord_5129991) baseStart_5129991 baseEnd_5129991 := by
    simpa [prefixWord, tailWord_5129991, baseEnd_5129991] using wordTrace_append hprefix tailTrace_5129991
  have hstable : (prefixWord ++ tailWord_5129991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5129991).length < 2 ^ (prefixWord ++ tailWord_5129991).sum := by decide
  have hdescent : baseEnd_5129991 < baseStart_5129991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5129991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130038 : List Nat := [5, 1, 2, 2, 1, 2, 3, 1, 6]
def baseStart_5130038 : Nat := 118140960795 + 5130038 * 2 ^ 59
def prefixEnd_5130038 : Nat := 4983230072969 + 3 ^ 40 * 5130038 * 2
def baseEnd_5130038 : Nat := 292686141092211659603599

theorem tailTrace_5130038 : CollatzResearch.WordTrace tailWord_5130038 prefixEnd_5130038 292686141092211659603599 := by
  unfold tailWord_5130038
  simp only [CollatzResearch.WordTrace]
  refine ⟨11694241086797246348898923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124738571592503961054921845 11694241086797246348898923)
  ·
    refine ⟨17541361630195869523348385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11694241086797246348898923 17541361630195869523348385)
    ·
      refine ⟨13156021222646902142511289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17541361630195869523348385 13156021222646902142511289)
      ·
        refine ⟨9867015916985176606883467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13156021222646902142511289 9867015916985176606883467)
        ·
          refine ⟨14800523875477764910325201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9867015916985176606883467 14800523875477764910325201)
          ·
            refine ⟨11100392906608323682743901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14800523875477764910325201 11100392906608323682743901)
            ·
              refine ⟨4162647339978121381028963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11100392906608323682743901 4162647339978121381028963)
              ·
                refine ⟨6243971009967182071543445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4162647339978121381028963 6243971009967182071543445)
                ·
                  refine ⟨292686141092211659603599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6243971009967182071543445 292686141092211659603599)
                  ·
                    rfl

theorem cell23_5130038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_5130038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130038 prefixEnd_5130038 := by exact prefixLift 5130038
  have htrace : WordTrace (prefixWord ++ tailWord_5130038) baseStart_5130038 baseEnd_5130038 := by
    simpa [prefixWord, tailWord_5130038, baseEnd_5130038] using wordTrace_append hprefix tailTrace_5130038
  have hstable : (prefixWord ++ tailWord_5130038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130038).length < 2 ^ (prefixWord ++ tailWord_5130038).sum := by decide
  have hdescent : baseEnd_5130038 < baseStart_5130038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130057 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 3, 1, 5]
def baseStart_5130057 : Nat := 118140960795 + 5130057 * 2 ^ 59
def prefixEnd_5130057 : Nat := 4983230072969 + 3 ^ 40 * 5130057 * 2
def baseEnd_5130057 : Nat := 2634185025962340362094803

theorem tailTrace_5130057 : CollatzResearch.WordTrace tailWord_5130057 prefixEnd_5130057 2634185025962340362094803 := by
  unfold tailWord_5130057
  simp only [CollatzResearch.WordTrace]
  refine ⟨187108550375687107827324425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124739033583791405218216283 187108550375687107827324425)
  ·
    refine ⟨140331412781765330870493319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187108550375687107827324425 140331412781765330870493319)
    ·
      refine ⟨210497119172647996305739979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140331412781765330870493319 210497119172647996305739979)
      ·
        refine ⟨315745678758971994458609969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210497119172647996305739979 315745678758971994458609969)
        ·
          refine ⟨236809259069228995843957477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315745678758971994458609969 236809259069228995843957477)
          ·
            refine ⟨44401736075480436720742027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 236809259069228995843957477 44401736075480436720742027)
            ·
              refine ⟨66602604113220655081113041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44401736075480436720742027 66602604113220655081113041)
              ·
                refine ⟨49951953084915491310834781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66602604113220655081113041 49951953084915491310834781)
                ·
                  refine ⟨18731982406843309241563043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49951953084915491310834781 18731982406843309241563043)
                  ·
                    refine ⟨28097973610264963862344565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18731982406843309241563043 28097973610264963862344565)
                    ·
                      refine ⟨2634185025962340362094803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28097973610264963862344565 2634185025962340362094803)
                      ·
                        rfl

theorem cell23_5130057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 1, 5].length) (baseStart_5130057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130057 prefixEnd_5130057 := by exact prefixLift 5130057
  have htrace : WordTrace (prefixWord ++ tailWord_5130057) baseStart_5130057 baseEnd_5130057 := by
    simpa [prefixWord, tailWord_5130057, baseEnd_5130057] using wordTrace_append hprefix tailTrace_5130057
  have hstable : (prefixWord ++ tailWord_5130057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130057).length < 2 ^ (prefixWord ++ tailWord_5130057).sum := by decide
  have hdescent : baseEnd_5130057 < baseStart_5130057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130065 : List Nat := [1, 2, 2, 1, 5, 3, 1, 3, 1, 1, 3]
def baseStart_5130065 : Nat := 118140960795 + 5130065 * 2 ^ 59
def prefixEnd_5130065 : Nat := 4983230072969 + 3 ^ 40 * 5130065 * 2
def baseEnd_5130065 : Nat := 2634189133807576330794767

theorem tailTrace_5130065 : CollatzResearch.WordTrace tailWord_5130065 prefixEnd_5130065 2634189133807576330794767 := by
  unfold tailWord_5130065
  simp only [CollatzResearch.WordTrace]
  refine ⟨187108842159658125193615649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124739228106438750129077099 187108842159658125193615649)
  ·
    refine ⟨140331631619743593895211737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187108842159658125193615649 140331631619743593895211737)
    ·
      refine ⟨105248723714807695421408803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140331631619743593895211737 105248723714807695421408803)
      ·
        refine ⟨157873085572211543132113205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105248723714807695421408803 157873085572211543132113205)
        ·
          refine ⟨14800601772394832168635613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157873085572211543132113205 14800601772394832168635613)
          ·
            refine ⟨5550225664648062063238355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14800601772394832168635613 5550225664648062063238355)
            ·
              refine ⟨8325338496972093094857533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5550225664648062063238355 8325338496972093094857533)
              ·
                refine ⟨3122001936364534910571575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8325338496972093094857533 3122001936364534910571575)
                ·
                  refine ⟨4683002904546802365857363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3122001936364534910571575 4683002904546802365857363)
                  ·
                    refine ⟨7024504356820203548786045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4683002904546802365857363 7024504356820203548786045)
                    ·
                      refine ⟨2634189133807576330794767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7024504356820203548786045 2634189133807576330794767)
                      ·
                        rfl

theorem cell23_5130065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 1, 1, 3].length) (baseStart_5130065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130065 prefixEnd_5130065 := by exact prefixLift 5130065
  have htrace : WordTrace (prefixWord ++ tailWord_5130065) baseStart_5130065 baseEnd_5130065 := by
    simpa [prefixWord, tailWord_5130065, baseEnd_5130065] using wordTrace_append hprefix tailTrace_5130065
  have hstable : (prefixWord ++ tailWord_5130065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130065).length < 2 ^ (prefixWord ++ tailWord_5130065).sum := by decide
  have hdescent : baseEnd_5130065 < baseStart_5130065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130074 : List Nat := [3, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5]
def baseStart_5130074 : Nat := 118140960795 + 5130074 * 2 ^ 59
def prefixEnd_5130074 : Nat := 4983230072969 + 3 ^ 40 * 5130074 * 2
def baseEnd_5130074 : Nat := 2634193755133466795582225

theorem tailTrace_5130074 : CollatzResearch.WordTrace tailWord_5130074 prefixEnd_5130074 2634193755133466795582225 := by
  unfold tailWord_5130074
  simp only [CollatzResearch.WordTrace]
  refine ⟨46777292604156379932673319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124739446944417013153795517 46777292604156379932673319)
  ·
    refine ⟨70165938906234569899009979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46777292604156379932673319 70165938906234569899009979)
    ·
      refine ⟨105248908359351854848514969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70165938906234569899009979 105248908359351854848514969)
      ·
        refine ⟨78936681269513891136386227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105248908359351854848514969 78936681269513891136386227)
        ·
          refine ⟨118405021904270836704579341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78936681269513891136386227 118405021904270836704579341)
          ·
            refine ⟨44401883214101563764217253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118405021904270836704579341 44401883214101563764217253)
            ·
              refine ⟨8325353102644043205790735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44401883214101563764217253 8325353102644043205790735)
              ·
                refine ⟨12488029653966064808686103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8325353102644043205790735 12488029653966064808686103)
                ·
                  refine ⟨18732044480949097213029155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12488029653966064808686103 18732044480949097213029155)
                  ·
                    refine ⟨28098066721423645819543733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18732044480949097213029155 28098066721423645819543733)
                    ·
                      refine ⟨2634193755133466795582225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28098066721423645819543733 2634193755133466795582225)
                      ·
                        rfl

theorem cell23_5130074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_5130074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130074 prefixEnd_5130074 := by exact prefixLift 5130074
  have htrace : WordTrace (prefixWord ++ tailWord_5130074) baseStart_5130074 baseEnd_5130074 := by
    simpa [prefixWord, tailWord_5130074, baseEnd_5130074] using wordTrace_append hprefix tailTrace_5130074
  have hstable : (prefixWord ++ tailWord_5130074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130074).length < 2 ^ (prefixWord ++ tailWord_5130074).sum := by decide
  have hdescent : baseEnd_5130074 < baseStart_5130074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130082 : List Nat := [3, 3, 2, 1, 2, 2, 3, 2, 1, 1, 3]
def baseStart_5130082 : Nat := 118140960795 + 5130082 * 2 ^ 59
def prefixEnd_5130082 : Nat := 4983230072969 + 3 ^ 40 * 5130082 * 2
def baseEnd_5130082 : Nat := 2634197862978702764282189

theorem tailTrace_5130082 : CollatzResearch.WordTrace tailWord_5130082 prefixEnd_5130082 2634197862978702764282189 := by
  unfold tailWord_5130082
  simp only [CollatzResearch.WordTrace]
  refine ⟨46777365550149134274246125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124739641467064358064656333 46777365550149134274246125)
  ·
    refine ⟨17541512081305925352842297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46777365550149134274246125 17541512081305925352842297)
    ·
      refine ⟨13156134060979444014631723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17541512081305925352842297 13156134060979444014631723)
      ·
        refine ⟨19734201091469166021947585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13156134060979444014631723 19734201091469166021947585)
        ·
          refine ⟨14800650818601874516460689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19734201091469166021947585 14800650818601874516460689)
          ·
            refine ⟨11100488113951405887345517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14800650818601874516460689 11100488113951405887345517)
            ·
              refine ⟨4162683042731777207754569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11100488113951405887345517 4162683042731777207754569)
              ·
                refine ⟨3122012282048832905815927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4162683042731777207754569 3122012282048832905815927)
                ·
                  refine ⟨4683018423073249358723891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3122012282048832905815927 4683018423073249358723891)
                  ·
                    refine ⟨7024527634609874038085837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4683018423073249358723891 7024527634609874038085837)
                    ·
                      refine ⟨2634197862978702764282189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7024527634609874038085837 2634197862978702764282189)
                      ·
                        rfl

theorem cell23_5130082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_5130082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130082 prefixEnd_5130082 := by exact prefixLift 5130082
  have htrace : WordTrace (prefixWord ++ tailWord_5130082) baseStart_5130082 baseEnd_5130082 := by
    simpa [prefixWord, tailWord_5130082, baseEnd_5130082] using wordTrace_append hprefix tailTrace_5130082
  have hstable : (prefixWord ++ tailWord_5130082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130082).length < 2 ^ (prefixWord ++ tailWord_5130082).sum := by decide
  have hdescent : baseEnd_5130082 < baseStart_5130082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130094 : List Nat := [4, 1, 2, 3, 1, 1, 1, 10]
def baseStart_5130094 : Nat := 118140960795 + 5130094 * 2 ^ 59
def prefixEnd_5130094 : Nat := 4983230072969 + 3 ^ 40 * 5130094 * 2
def baseEnd_5130094 : Nat := 97563112027650248790079

theorem tailTrace_5130094 : CollatzResearch.WordTrace tailWord_5130094 prefixEnd_5130094 97563112027650248790079 := by
  unfold tailWord_5130094
  simp only [CollatzResearch.WordTrace]
  refine ⟨23388737484569132893302667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124739933251035375430947557 23388737484569132893302667)
  ·
    refine ⟨35083106226853699339954001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23388737484569132893302667 35083106226853699339954001)
    ·
      refine ⟨26312329670140274504965501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35083106226853699339954001 26312329670140274504965501)
      ·
        refine ⟨9867123626302602939362063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26312329670140274504965501 9867123626302602939362063)
        ·
          refine ⟨14800685439453904409043095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9867123626302602939362063 14800685439453904409043095)
          ·
            refine ⟨22201028159180856613564643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14800685439453904409043095 22201028159180856613564643)
            ·
              refine ⟨33301542238771284920346965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22201028159180856613564643 33301542238771284920346965)
              ·
                refine ⟨97563112027650248790079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33301542238771284920346965 97563112027650248790079)
                ·
                  rfl

theorem cell23_5130094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 10].length) (baseStart_5130094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130094 prefixEnd_5130094 := by exact prefixLift 5130094
  have htrace : WordTrace (prefixWord ++ tailWord_5130094) baseStart_5130094 baseEnd_5130094 := by
    simpa [prefixWord, tailWord_5130094, baseEnd_5130094] using wordTrace_append hprefix tailTrace_5130094
  have hstable : (prefixWord ++ tailWord_5130094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130094).length < 2 ^ (prefixWord ++ tailWord_5130094).sum := by decide
  have hdescent : baseEnd_5130094 < baseStart_5130094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130097 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 2, 2, 6]
def baseStart_5130097 : Nat := 118140960795 + 5130097 * 2 ^ 59
def prefixEnd_5130097 : Nat := 4983230072969 + 3 ^ 40 * 5130097 * 2
def baseEnd_5130097 : Nat := 2634205565188520205594619

theorem tailTrace_5130097 : CollatzResearch.WordTrace tailWord_5130097 prefixEnd_5130097 2634205565188520205594619 := by
  unfold tailWord_5130097
  simp only [CollatzResearch.WordTrace]
  refine ⟨187110009295542194658780545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124740006197028129772520363 187110009295542194658780545)
  ·
    refine ⟨140332506971656645994085409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187110009295542194658780545 140332506971656645994085409)
    ·
      refine ⟨105249380228742484495564057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140332506971656645994085409 105249380228742484495564057)
      ·
        refine ⟨78937035171556863371673043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105249380228742484495564057 78937035171556863371673043)
        ·
          refine ⟨118405552757335295057509565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78937035171556863371673043 118405552757335295057509565)
          ·
            refine ⟨44402082284000735646566087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118405552757335295057509565 44402082284000735646566087)
            ·
              refine ⟨66603123426001103469849131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44402082284000735646566087 66603123426001103469849131)
              ·
                refine ⟨99904685139001655204773697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66603123426001103469849131 99904685139001655204773697)
                ·
                  refine ⟨74928513854251241403580273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99904685139001655204773697 74928513854251241403580273)
                  ·
                    refine ⟨56196385390688431052685205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74928513854251241403580273 56196385390688431052685205)
                    ·
                      refine ⟨2634205565188520205594619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56196385390688431052685205 2634205565188520205594619)
                      ·
                        rfl

theorem cell23_5130097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_5130097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130097 prefixEnd_5130097 := by exact prefixLift 5130097
  have htrace : WordTrace (prefixWord ++ tailWord_5130097) baseStart_5130097 baseEnd_5130097 := by
    simpa [prefixWord, tailWord_5130097, baseEnd_5130097] using wordTrace_append hprefix tailTrace_5130097
  have hstable : (prefixWord ++ tailWord_5130097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130097).length < 2 ^ (prefixWord ++ tailWord_5130097).sum := by decide
  have hdescent : baseEnd_5130097 < baseStart_5130097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130138 : List Nat := [3, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3]
def baseStart_5130138 : Nat := 118140960795 + 5130138 * 2 ^ 59
def prefixEnd_5130138 : Nat := 4983230072969 + 3 ^ 40 * 5130138 * 2
def baseEnd_5130138 : Nat := 2634226617895354545181931

theorem tailTrace_5130138 : CollatzResearch.WordTrace tailWord_5130138 prefixEnd_5130138 2634226617895354545181931 := by
  unfold tailWord_5130138
  simp only [CollatzResearch.WordTrace]
  refine ⟨46777876172098414665255767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124741003125595772440682045 46777876172098414665255767)
  ·
    refine ⟨70166814258147621997883651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46777876172098414665255767 70166814258147621997883651)
    ·
      refine ⟨105250221387221432996825477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70166814258147621997883651 105250221387221432996825477)
      ·
        refine ⟨19734416510104018686904777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105250221387221432996825477 19734416510104018686904777)
        ·
          refine ⟨14800812382578014015178583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19734416510104018686904777 14800812382578014015178583)
          ·
            refine ⟨22201218573867021022767875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14800812382578014015178583 22201218573867021022767875)
            ·
              refine ⟨33301827860800531534151813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22201218573867021022767875 33301827860800531534151813)
              ·
                refine ⟨6244092723900099662653465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33301827860800531534151813 6244092723900099662653465)
                ·
                  refine ⟨4683069542925074746990099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6244092723900099662653465 4683069542925074746990099)
                  ·
                    refine ⟨7024604314387612120485149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4683069542925074746990099 7024604314387612120485149)
                    ·
                      refine ⟨2634226617895354545181931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7024604314387612120485149 2634226617895354545181931)
                      ·
                        rfl

theorem cell23_5130138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_5130138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130138 prefixEnd_5130138 := by exact prefixLift 5130138
  have htrace : WordTrace (prefixWord ++ tailWord_5130138) baseStart_5130138 baseEnd_5130138 := by
    simpa [prefixWord, tailWord_5130138, baseEnd_5130138] using wordTrace_append hprefix tailTrace_5130138
  have hstable : (prefixWord ++ tailWord_5130138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130138).length < 2 ^ (prefixWord ++ tailWord_5130138).sum := by decide
  have hdescent : baseEnd_5130138 < baseStart_5130138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130201 : List Nat := [1, 2, 1, 2, 6, 1, 2, 1, 7]
def baseStart_5130201 : Nat := 118140960795 + 5130201 * 2 ^ 59
def prefixEnd_5130201 : Nat := 4983230072969 + 3 ^ 40 * 5130201 * 2
def baseEnd_5130201 : Nat := 292695440797398644299349

theorem tailTrace_5130201 : CollatzResearch.WordTrace tailWord_5130201 prefixEnd_5130201 292695440797398644299349 := by
  unfold tailWord_5130201
  simp only [CollatzResearch.WordTrace]
  refine ⟨187113802487165420420566457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124742534991443613613710971 187113802487165420420566457)
  ·
    refine ⟨140335351865374065315424843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187113802487165420420566457 140335351865374065315424843)
    ·
      refine ⟨210503027798061097973137265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140335351865374065315424843 210503027798061097973137265)
      ·
        refine ⟨157877270848545823479852949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210503027798061097973137265 157877270848545823479852949)
        ·
          refine ⟨7400497071025585475618107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 157877270848545823479852949 7400497071025585475618107)
          ·
            refine ⟨11100745606538378213427161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7400497071025585475618107 11100745606538378213427161)
            ·
              refine ⟨8325559204903783660070371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11100745606538378213427161 8325559204903783660070371)
              ·
                refine ⟨12488338807355675490105557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8325559204903783660070371 12488338807355675490105557)
                ·
                  refine ⟨292695440797398644299349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12488338807355675490105557 292695440797398644299349)
                  ·
                    rfl

theorem cell23_5130201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 7].length) (baseStart_5130201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130201 prefixEnd_5130201 := by exact prefixLift 5130201
  have htrace : WordTrace (prefixWord ++ tailWord_5130201) baseStart_5130201 baseEnd_5130201 := by
    simpa [prefixWord, tailWord_5130201, baseEnd_5130201] using wordTrace_append hprefix tailTrace_5130201
  have hstable : (prefixWord ++ tailWord_5130201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130201).length < 2 ^ (prefixWord ++ tailWord_5130201).sum := by decide
  have hdescent : baseEnd_5130201 < baseStart_5130201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130211 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 3]
def baseStart_5130211 : Nat := 118140960795 + 5130211 * 2 ^ 59
def prefixEnd_5130211 : Nat := 4983230072969 + 3 ^ 40 * 5130211 * 2
def baseEnd_5130211 : Nat := 2634264101983132759569095

theorem tailTrace_5130211 : CollatzResearch.WordTrace tailWord_5130211 prefixEnd_5130211 2634264101983132759569095 := by
  unfold tailWord_5130211
  simp only [CollatzResearch.WordTrace]
  refine ⟨187114167217129192128430487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124742778144752794752286991 187114167217129192128430487)
  ·
    refine ⟨280671250825693788192645731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187114167217129192128430487 280671250825693788192645731)
    ·
      refine ⟨421006876238540682288968597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280671250825693788192645731 421006876238540682288968597)
      ·
        refine ⟨19734697323681594482295403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 421006876238540682288968597 19734697323681594482295403)
        ·
          refine ⟨29602045985522391723443105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19734697323681594482295403 29602045985522391723443105)
          ·
            refine ⟨22201534489141793792582329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29602045985522391723443105 22201534489141793792582329)
            ·
              refine ⟨16651150866856345344436747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22201534489141793792582329 16651150866856345344436747)
              ·
                refine ⟨24976726300284518016655121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16651150866856345344436747 24976726300284518016655121)
                ·
                  refine ⟨18732544725213388512491341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24976726300284518016655121 18732544725213388512491341)
                  ·
                    refine ⟨7024704271955020692184253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18732544725213388512491341 7024704271955020692184253)
                    ·
                      refine ⟨2634264101983132759569095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7024704271955020692184253 2634264101983132759569095)
                      ·
                        rfl

theorem cell23_5130211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_5130211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130211 prefixEnd_5130211 := by exact prefixLift 5130211
  have htrace : WordTrace (prefixWord ++ tailWord_5130211) baseStart_5130211 baseEnd_5130211 := by
    simpa [prefixWord, tailWord_5130211, baseEnd_5130211] using wordTrace_append hprefix tailTrace_5130211
  have hstable : (prefixWord ++ tailWord_5130211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130211).length < 2 ^ (prefixWord ++ tailWord_5130211).sum := by decide
  have hdescent : baseEnd_5130211 < baseStart_5130211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130251 : List Nat := [1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 4]
def baseStart_5130251 : Nat := 118140960795 + 5130251 * 2 ^ 59
def prefixEnd_5130251 : Nat := 4983230072969 + 3 ^ 40 * 5130251 * 2
def baseEnd_5130251 : Nat := 2634284641209312603068911

theorem tailTrace_5130251 : CollatzResearch.WordTrace tailWord_5130251 prefixEnd_5130251 2634284641209312603068911 := by
  unfold tailWord_5130251
  simp only [CollatzResearch.WordTrace]
  refine ⟨187115626136984278959886607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124743750757989519306591071 187115626136984278959886607)
  ·
    refine ⟨280673439205476418439829911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187115626136984278959886607 280673439205476418439829911)
    ·
      refine ⟨421010158808214627659744867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280673439205476418439829911 421010158808214627659744867)
      ·
        refine ⟨631515238212321941489617301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421010158808214627659744867 631515238212321941489617301)
        ·
          refine ⟨29602276791202591007325811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 631515238212321941489617301 29602276791202591007325811)
          ·
            refine ⟨44403415186803886510988717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29602276791202591007325811 44403415186803886510988717)
            ·
              refine ⟨16651280695051457441620769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44403415186803886510988717 16651280695051457441620769)
              ·
                refine ⟨12488460521288593081215577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16651280695051457441620769 12488460521288593081215577)
                ·
                  refine ⟨9366345390966444810911683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12488460521288593081215577 9366345390966444810911683)
                  ·
                    refine ⟨14049518086449667216367525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9366345390966444810911683 14049518086449667216367525)
                    ·
                      refine ⟨2634284641209312603068911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14049518086449667216367525 2634284641209312603068911)
                      ·
                        rfl

theorem cell23_5130251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 4].length) (baseStart_5130251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130251 prefixEnd_5130251 := by exact prefixLift 5130251
  have htrace : WordTrace (prefixWord ++ tailWord_5130251) baseStart_5130251 baseEnd_5130251 := by
    simpa [prefixWord, tailWord_5130251, baseEnd_5130251] using wordTrace_append hprefix tailTrace_5130251
  have hstable : (prefixWord ++ tailWord_5130251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130251).length < 2 ^ (prefixWord ++ tailWord_5130251).sum := by decide
  have hdescent : baseEnd_5130251 < baseStart_5130251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130271 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 3]
def baseStart_5130271 : Nat := 118140960795 + 5130271 * 2 ^ 59
def prefixEnd_5130271 : Nat := 4983230072969 + 3 ^ 40 * 5130271 * 2
def baseEnd_5130271 : Nat := 2634294910822402524818819

theorem tailTrace_5130271 : CollatzResearch.WordTrace tailWord_5130271 prefixEnd_5130271 2634294910822402524818819 := by
  unfold tailWord_5130271
  simp only [CollatzResearch.WordTrace]
  refine ⟨187116355596911822375614667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124744237064607881583743111 187116355596911822375614667)
  ·
    refine ⟨280674533395367733563422001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187116355596911822375614667 280674533395367733563422001)
    ·
      refine ⟨210505900046525800172566501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280674533395367733563422001 210505900046525800172566501)
      ·
        refine ⟨39469856258723587532356219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210505900046525800172566501 39469856258723587532356219)
        ·
          refine ⟨59204784388085381298534329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39469856258723587532356219 59204784388085381298534329)
          ·
            refine ⟨44403588291064035973900747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59204784388085381298534329 44403588291064035973900747)
            ·
              refine ⟨66605382436596053960851121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44403588291064035973900747 66605382436596053960851121)
              ·
                refine ⟨49954036827447040470638341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66605382436596053960851121 49954036827447040470638341)
                ·
                  refine ⟨9366381905146320088244689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49954036827447040470638341 9366381905146320088244689)
                  ·
                    refine ⟨7024786428859740066183517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9366381905146320088244689 7024786428859740066183517)
                    ·
                      refine ⟨2634294910822402524818819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7024786428859740066183517 2634294910822402524818819)
                      ·
                        rfl

theorem cell23_5130271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_5130271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130271 prefixEnd_5130271 := by exact prefixLift 5130271
  have htrace : WordTrace (prefixWord ++ tailWord_5130271) baseStart_5130271 baseEnd_5130271 := by
    simpa [prefixWord, tailWord_5130271, baseEnd_5130271] using wordTrace_append hprefix tailTrace_5130271
  have hstable : (prefixWord ++ tailWord_5130271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130271).length < 2 ^ (prefixWord ++ tailWord_5130271).sum := by decide
  have hdescent : baseEnd_5130271 < baseStart_5130271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130288 : List Nat := [2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 3]
def baseStart_5130288 : Nat := 118140960795 + 5130288 * 2 ^ 59
def prefixEnd_5130288 : Nat := 4983230072969 + 3 ^ 40 * 5130288 * 2
def baseEnd_5130288 : Nat := 2634303639993528958306241

theorem tailTrace_5130288 : CollatzResearch.WordTrace tailWord_5130288 prefixEnd_5130288 2634303639993528958306241 := by
  unfold tailWord_5130288
  simp only [CollatzResearch.WordTrace]
  refine ⟨93558487818925117139491759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124744650425233489519322345 93558487818925117139491759)
  ·
    refine ⟨140337731728387675709237639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93558487818925117139491759 140337731728387675709237639)
    ·
      refine ⟨210506597592581513563856459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140337731728387675709237639 210506597592581513563856459)
      ·
        refine ⟨315759896388872270345784689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210506597592581513563856459 315759896388872270345784689)
        ·
          refine ⟨236819922291654202759338517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315759896388872270345784689 236819922291654202759338517)
          ·
            refine ⟨11100933857421290754343993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 236819922291654202759338517 11100933857421290754343993)
            ·
              refine ⟨8325700393065968065757995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11100933857421290754343993 8325700393065968065757995)
              ·
                refine ⟨12488550589598952098636993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8325700393065968065757995 12488550589598952098636993)
                ·
                  refine ⟨9366412942199214073977745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12488550589598952098636993 9366412942199214073977745)
                  ·
                    refine ⟨7024809706649410555483309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9366412942199214073977745 7024809706649410555483309)
                    ·
                      refine ⟨2634303639993528958306241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7024809706649410555483309 2634303639993528958306241)
                      ·
                        rfl

theorem cell23_5130288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 3].length) (baseStart_5130288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130288 prefixEnd_5130288 := by exact prefixLift 5130288
  have htrace : WordTrace (prefixWord ++ tailWord_5130288) baseStart_5130288 baseEnd_5130288 := by
    simpa [prefixWord, tailWord_5130288, baseEnd_5130288] using wordTrace_append hprefix tailTrace_5130288
  have hstable : (prefixWord ++ tailWord_5130288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130288).length < 2 ^ (prefixWord ++ tailWord_5130288).sum := by decide
  have hdescent : baseEnd_5130288 < baseStart_5130288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130351 : List Nat := [1, 1, 2, 1, 3, 4, 2, 2, 1, 6]
def baseStart_5130351 : Nat := 118140960795 + 5130351 * 2 ^ 59
def prefixEnd_5130351 : Nat := 4983230072969 + 3 ^ 40 * 5130351 * 2
def baseEnd_5130351 : Nat := 878111996424920737272817

theorem tailTrace_5130351 : CollatzResearch.WordTrace tailWord_5130351 prefixEnd_5130351 878111996424920737272817 := by
  unfold tailWord_5130351
  simp only [CollatzResearch.WordTrace]
  refine ⟨187119273436621996038526907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124746182291081330692351271 187119273436621996038526907)
  ·
    refine ⟨280678910154932994057790361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187119273436621996038526907 280678910154932994057790361)
    ·
      refine ⟨210509182616199745543342771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280678910154932994057790361 210509182616199745543342771)
      ·
        refine ⟨315763773924299618315014157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210509182616199745543342771 315763773924299618315014157)
        ·
          refine ⟨118411415221612356868130309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 315763773924299618315014157 118411415221612356868130309)
          ·
            refine ⟨22202140354052316912774433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118411415221612356868130309 22202140354052316912774433)
            ·
              refine ⟨16651605265539237684580825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22202140354052316912774433 16651605265539237684580825)
              ·
                refine ⟨12488703949154428263435619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16651605265539237684580825 12488703949154428263435619)
                ·
                  refine ⟨18733055923731642395153429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12488703949154428263435619 18733055923731642395153429)
                  ·
                    refine ⟨878111996424920737272817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18733055923731642395153429 878111996424920737272817)
                    ·
                      rfl

theorem cell23_5130351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 6].length) (baseStart_5130351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130351 prefixEnd_5130351 := by exact prefixLift 5130351
  have htrace : WordTrace (prefixWord ++ tailWord_5130351) baseStart_5130351 baseEnd_5130351 := by
    simpa [prefixWord, tailWord_5130351, baseEnd_5130351] using wordTrace_append hprefix tailTrace_5130351
  have hstable : (prefixWord ++ tailWord_5130351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130351).length < 2 ^ (prefixWord ++ tailWord_5130351).sum := by decide
  have hdescent : baseEnd_5130351 < baseStart_5130351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130352 : List Nat := [2, 1, 1, 1, 5, 3, 2, 3, 1, 1, 3]
def baseStart_5130352 : Nat := 118140960795 + 5130352 * 2 ^ 59
def prefixEnd_5130352 : Nat := 4983230072969 + 3 ^ 40 * 5130352 * 2
def baseEnd_5130352 : Nat := 2634336502755416707905947

theorem tailTrace_5130352 : CollatzResearch.WordTrace tailWord_5130352 prefixEnd_5130352 2634336502755416707905947 := by
  unfold tailWord_5130352
  simp only [CollatzResearch.WordTrace]
  refine ⟨93559654954809186604656655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124746206606412248806208873 93559654954809186604656655)
  ·
    refine ⟨140339482432213779906984983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93559654954809186604656655 140339482432213779906984983)
    ·
      refine ⟨210509223648320669860477475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140339482432213779906984983 210509223648320669860477475)
      ·
        refine ⟨315763835472481004790716213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210509223648320669860477475 315763835472481004790716213)
        ·
          refine ⟨29602859575545094199129645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 315763835472481004790716213 29602859575545094199129645)
          ·
            refine ⟨11101072340829410324673617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29602859575545094199129645 11101072340829410324673617)
            ·
              refine ⟨8325804255622057743505213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11101072340829410324673617 8325804255622057743505213)
              ·
                refine ⟨3122176595858271653814455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8325804255622057743505213 3122176595858271653814455)
                ·
                  refine ⟨4683264893787407480721683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3122176595858271653814455 4683264893787407480721683)
                  ·
                    refine ⟨7024897340681111221082525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4683264893787407480721683 7024897340681111221082525)
                    ·
                      refine ⟨2634336502755416707905947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7024897340681111221082525 2634336502755416707905947)
                      ·
                        rfl

theorem cell23_5130352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 1, 1, 3].length) (baseStart_5130352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130352 prefixEnd_5130352 := by exact prefixLift 5130352
  have htrace : WordTrace (prefixWord ++ tailWord_5130352) baseStart_5130352 baseEnd_5130352 := by
    simpa [prefixWord, tailWord_5130352, baseEnd_5130352] using wordTrace_append hprefix tailTrace_5130352
  have hstable : (prefixWord ++ tailWord_5130352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130352).length < 2 ^ (prefixWord ++ tailWord_5130352).sum := by decide
  have hdescent : baseEnd_5130352 < baseStart_5130352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130375 : List Nat := [1, 1, 4, 2, 1, 1, 3, 3, 3, 2, 2]
def baseStart_5130375 : Nat := 118140960795 + 5130375 * 2 ^ 59
def prefixEnd_5130375 : Nat := 4983230072969 + 3 ^ 40 * 5130375 * 2
def baseEnd_5130375 : Nat := 2634348312810470117918341

theorem tailTrace_5130375 : CollatzResearch.WordTrace tailWord_5130375 prefixEnd_5130375 2634348312810470117918341 := by
  unfold tailWord_5130375
  simp only [CollatzResearch.WordTrace]
  refine ⟨187120148788535048137400579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124746765859023365424933719 187120148788535048137400579)
  ·
    refine ⟨280680223182802572206100869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187120148788535048137400579 280680223182802572206100869)
    ·
      refine ⟨52627541846775482288643913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 280680223182802572206100869 52627541846775482288643913)
      ·
        refine ⟨39470656385081611716482935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52627541846775482288643913 39470656385081611716482935)
        ·
          refine ⟨59205984577622417574724403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39470656385081611716482935 59205984577622417574724403)
          ·
            refine ⟨88808976866433626362086605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59205984577622417574724403 88808976866433626362086605)
            ·
              refine ⟨33303366324912609885782477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88808976866433626362086605 33303366324912609885782477)
              ·
                refine ⟨12488762371842228707168429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33303366324912609885782477 12488762371842228707168429)
                ·
                  refine ⟨4683285889440835765188161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12488762371842228707168429 4683285889440835765188161)
                  ·
                    refine ⟨3512464417080626823891121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4683285889440835765188161 3512464417080626823891121)
                    ·
                      refine ⟨2634348312810470117918341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3512464417080626823891121 2634348312810470117918341)
                      ·
                        rfl

theorem cell23_5130375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_5130375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130375 prefixEnd_5130375 := by exact prefixLift 5130375
  have htrace : WordTrace (prefixWord ++ tailWord_5130375) baseStart_5130375 baseEnd_5130375 := by
    simpa [prefixWord, tailWord_5130375, baseEnd_5130375] using wordTrace_append hprefix tailTrace_5130375
  have hstable : (prefixWord ++ tailWord_5130375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130375).length < 2 ^ (prefixWord ++ tailWord_5130375).sum := by decide
  have hdescent : baseEnd_5130375 < baseStart_5130375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130378 : List Nat := [3, 1, 2, 3, 1, 3, 1, 2, 1, 1, 5]
def baseStart_5130378 : Nat := 118140960795 + 5130378 * 2 ^ 59
def prefixEnd_5130378 : Nat := 4983230072969 + 3 ^ 40 * 5130378 * 2
def baseEnd_5130378 : Nat := 2634349853252433606180827

theorem tailTrace_5130378 : CollatzResearch.WordTrace tailWord_5130378 prefixEnd_5130378 2634349853252433606180827 := by
  unfold tailWord_5130378
  simp only [CollatzResearch.WordTrace]
  refine ⟨46780064551881044912439947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124746838805016119766506525 46780064551881044912439947)
  ·
    refine ⟨70170096827821567368659921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46780064551881044912439947 70170096827821567368659921)
    ·
      refine ⟨52627572620866175526494941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70170096827821567368659921 52627572620866175526494941)
      ·
        refine ⟨19735339732824815822435603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52627572620866175526494941 19735339732824815822435603)
        ·
          refine ⟨29603009599237223733653405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19735339732824815822435603 29603009599237223733653405)
          ·
            refine ⟨11101128599713958900120027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29603009599237223733653405 11101128599713958900120027)
            ·
              refine ⟨16651692899570938350180041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11101128599713958900120027 16651692899570938350180041)
              ·
                refine ⟨12488769674678203762635031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16651692899570938350180041 12488769674678203762635031)
                ·
                  refine ⟨18733154512017305643952547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12488769674678203762635031 18733154512017305643952547)
                  ·
                    refine ⟨28099731768025958465928821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18733154512017305643952547 28099731768025958465928821)
                    ·
                      refine ⟨2634349853252433606180827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28099731768025958465928821 2634349853252433606180827)
                      ·
                        rfl

theorem cell23_5130378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_5130378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130378 prefixEnd_5130378 := by exact prefixLift 5130378
  have htrace : WordTrace (prefixWord ++ tailWord_5130378) baseStart_5130378 baseEnd_5130378 := by
    simpa [prefixWord, tailWord_5130378, baseEnd_5130378] using wordTrace_append hprefix tailTrace_5130378
  have hstable : (prefixWord ++ tailWord_5130378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130378).length < 2 ^ (prefixWord ++ tailWord_5130378).sum := by decide
  have hdescent : baseEnd_5130378 < baseStart_5130378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130420 : List Nat := [2, 5, 3, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_5130420 : Nat := 118140960795 + 5130420 * 2 ^ 59
def prefixEnd_5130420 : Nat := 4983230072969 + 3 ^ 40 * 5130420 * 2
def baseEnd_5130420 : Nat := 2634371419439922441855635

theorem tailTrace_5130420 : CollatzResearch.WordTrace tailWord_5130420 prefixEnd_5130420 2634371419439922441855635 := by
  unfold tailWord_5130420
  simp only [CollatzResearch.WordTrace]
  refine ⟨93560895036686010411394357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124747860048914680548525809 93560895036686010411394357)
  ·
    refine ⟨8771333909689313476068221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93560895036686010411394357 8771333909689313476068221)
    ·
      refine ⟨3289250216133492553525583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8771333909689313476068221 3289250216133492553525583)
      ·
        refine ⟨4933875324200238830288375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3289250216133492553525583 4933875324200238830288375)
        ·
          refine ⟨7400812986300358245432563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4933875324200238830288375 7400812986300358245432563)
          ·
            refine ⟨11101219479450537368148845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7400812986300358245432563 11101219479450537368148845)
            ·
              refine ⟨4162957304793951513055817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11101219479450537368148845 4162957304793951513055817)
              ·
                refine ⟨3122217978595463634791863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4162957304793951513055817 3122217978595463634791863)
                ·
                  refine ⟨4683326967893195452187795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3122217978595463634791863 4683326967893195452187795)
                  ·
                    refine ⟨7024990451839793178281693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4683326967893195452187795 7024990451839793178281693)
                    ·
                      refine ⟨2634371419439922441855635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7024990451839793178281693 2634371419439922441855635)
                      ·
                        rfl

theorem cell23_5130420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_5130420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130420 prefixEnd_5130420 := by exact prefixLift 5130420
  have htrace : WordTrace (prefixWord ++ tailWord_5130420) baseStart_5130420 baseEnd_5130420 := by
    simpa [prefixWord, tailWord_5130420, baseEnd_5130420] using wordTrace_append hprefix tailTrace_5130420
  have hstable : (prefixWord ++ tailWord_5130420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130420).length < 2 ^ (prefixWord ++ tailWord_5130420).sum := by decide
  have hdescent : baseEnd_5130420 < baseStart_5130420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130425 : List Nat := [1, 2, 1, 4, 1, 2, 2, 4, 2, 1, 3]
def baseStart_5130425 : Nat := 118140960795 + 5130425 * 2 ^ 59
def prefixEnd_5130425 : Nat := 4983230072969 + 3 ^ 40 * 5130425 * 2
def baseEnd_5130425 : Nat := 2634373986843194922293111

theorem tailTrace_5130425 : CollatzResearch.WordTrace tailWord_5130425 prefixEnd_5130425 2634373986843194922293111 := by
  unfold tailWord_5130425
  simp only [CollatzResearch.WordTrace]
  refine ⟨187121972438353906676720729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124747981625569271117813819 187121972438353906676720729)
  ·
    refine ⟨140341479328765430007540547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187121972438353906676720729 140341479328765430007540547)
    ·
      refine ⟨210512218993148145011310821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140341479328765430007540547 210512218993148145011310821)
      ·
        refine ⟨39471041061215277189620779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210512218993148145011310821 39471041061215277189620779)
        ·
          refine ⟨59206561591822915784431169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39471041061215277189620779 59206561591822915784431169)
          ·
            refine ⟨44404921193867186838323377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59206561591822915784431169 44404921193867186838323377)
            ·
              refine ⟨33303690895400390128742533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44404921193867186838323377 33303690895400390128742533)
              ·
                refine ⟨6244442042887573149139225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33303690895400390128742533 6244442042887573149139225)
                ·
                  refine ⟨4683331532165679861854419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6244442042887573149139225 4683331532165679861854419)
                  ·
                    refine ⟨7024997298248519792781629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4683331532165679861854419 7024997298248519792781629)
                    ·
                      refine ⟨2634373986843194922293111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7024997298248519792781629 2634373986843194922293111)
                      ·
                        rfl

theorem cell23_5130425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_5130425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130425 prefixEnd_5130425 := by exact prefixLift 5130425
  have htrace : WordTrace (prefixWord ++ tailWord_5130425) baseStart_5130425 baseEnd_5130425 := by
    simpa [prefixWord, tailWord_5130425, baseEnd_5130425] using wordTrace_append hprefix tailTrace_5130425
  have hstable : (prefixWord ++ tailWord_5130425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130425).length < 2 ^ (prefixWord ++ tailWord_5130425).sum := by decide
  have hdescent : baseEnd_5130425 < baseStart_5130425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130431 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 4]
def baseStart_5130431 : Nat := 118140960795 + 5130431 * 2 ^ 59
def prefixEnd_5130431 : Nat := 4983230072969 + 3 ^ 40 * 5130431 * 2
def baseEnd_5130431 : Nat := 2634377067727121898818083

theorem tailTrace_5130431 : CollatzResearch.WordTrace tailWord_5130431 prefixEnd_5130431 2634377067727121898818083 := by
  unfold tailWord_5130431
  simp only [CollatzResearch.WordTrace]
  refine ⟨187122191276332169701439147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124748127517554779800959431 187122191276332169701439147)
  ·
    refine ⟨280683286914498254552158721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187122191276332169701439147 280683286914498254552158721)
    ·
      refine ⟨210512465185873690914119041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280683286914498254552158721 210512465185873690914119041)
      ·
        refine ⟨157884348889405268185589281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210512465185873690914119041 157884348889405268185589281)
        ·
          refine ⟨118413261667053951139191961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157884348889405268185589281 118413261667053951139191961)
          ·
            refine ⟨88809946250290463354393971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118413261667053951139191961 88809946250290463354393971)
            ·
              refine ⟨133214919375435695031590957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88809946250290463354393971 133214919375435695031590957)
              ·
                refine ⟨49955594765788385636846609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133214919375435695031590957 49955594765788385636846609)
                ·
                  refine ⟨37466696074341289227634957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49955594765788385636846609 37466696074341289227634957)
                  ·
                    refine ⟨14050011027877983460363109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37466696074341289227634957 14050011027877983460363109)
                    ·
                      refine ⟨2634377067727121898818083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14050011027877983460363109 2634377067727121898818083)
                      ·
                        rfl

theorem cell23_5130431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_5130431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130431 prefixEnd_5130431 := by exact prefixLift 5130431
  have htrace : WordTrace (prefixWord ++ tailWord_5130431) baseStart_5130431 baseEnd_5130431 := by
    simpa [prefixWord, tailWord_5130431, baseEnd_5130431] using wordTrace_append hprefix tailTrace_5130431
  have hstable : (prefixWord ++ tailWord_5130431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130431).length < 2 ^ (prefixWord ++ tailWord_5130431).sum := by decide
  have hdescent : baseEnd_5130431 < baseStart_5130431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130448 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 7, 4, 2]
def baseStart_5130448 : Nat := 118140960795 + 5130448 * 2 ^ 59
def prefixEnd_5130448 : Nat := 4983230072969 + 3 ^ 40 * 5130448 * 2
def baseEnd_5130448 : Nat := 2634385796898248332305505

theorem tailTrace_5130448 : CollatzResearch.WordTrace tailWord_5130448 prefixEnd_5130448 2634385796898248332305505 := by
  unfold tailWord_5130448
  simp only [CollatzResearch.WordTrace]
  refine ⟨93561405658635290802403999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124748540878180387736538665 93561405658635290802403999)
  ·
    refine ⟨140342108487952936203605999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93561405658635290802403999 140342108487952936203605999)
    ·
      refine ⟨210513162731929404305408999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140342108487952936203605999 210513162731929404305408999)
      ·
        refine ⟨315769744097894106458113499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210513162731929404305408999 315769744097894106458113499)
        ·
          refine ⟨473654616146841159687170249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315769744097894106458113499 473654616146841159687170249)
          ·
            refine ⟨355240962110130869765377687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473654616146841159687170249 355240962110130869765377687)
            ·
              refine ⟨532861443165196304648066531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355240962110130869765377687 532861443165196304648066531)
              ·
                refine ⟨799292164747794456972099797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532861443165196304648066531 799292164747794456972099797)
                ·
                  refine ⟨18733410111276432585283589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 799292164747794456972099797 18733410111276432585283589)
                  ·
                    refine ⟨3512514395864331109740673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18733410111276432585283589 3512514395864331109740673)
                    ·
                      refine ⟨2634385796898248332305505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3512514395864331109740673 2634385796898248332305505)
                      ·
                        rfl

theorem cell23_5130448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 7, 4, 2].length) (baseStart_5130448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130448 prefixEnd_5130448 := by exact prefixLift 5130448
  have htrace : WordTrace (prefixWord ++ tailWord_5130448) baseStart_5130448 baseEnd_5130448 := by
    simpa [prefixWord, tailWord_5130448, baseEnd_5130448] using wordTrace_append hprefix tailTrace_5130448
  have hstable : (prefixWord ++ tailWord_5130448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130448).length < 2 ^ (prefixWord ++ tailWord_5130448).sum := by decide
  have hdescent : baseEnd_5130448 < baseStart_5130448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130465 : List Nat := [1, 2, 3, 1, 3, 1, 3, 2, 1, 4, 2]
def baseStart_5130465 : Nat := 118140960795 + 5130465 * 2 ^ 59
def prefixEnd_5130465 : Nat := 4983230072969 + 3 ^ 40 * 5130465 * 2
def baseEnd_5130465 : Nat := 2634394526069374765792927

theorem tailTrace_5130465 : CollatzResearch.WordTrace tailWord_5130465 prefixEnd_5130465 2634394526069374765792927 := by
  unfold tailWord_5130465
  simp only [CollatzResearch.WordTrace]
  refine ⟨187123431358208993508176849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124748954238805995672117899 187123431358208993508176849)
  ·
    refine ⟨140342573518656745131132637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187123431358208993508176849 140342573518656745131132637)
    ·
      refine ⟨52628465069496279424174739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140342573518656745131132637 52628465069496279424174739)
      ·
        refine ⟨78942697604244419136262109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52628465069496279424174739 78942697604244419136262109)
        ·
          refine ⟨29603511601591657176098291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78942697604244419136262109 29603511601591657176098291)
          ·
            refine ⟨44405267402387485764147437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29603511601591657176098291 44405267402387485764147437)
            ·
              refine ⟨16651975275895307161555289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44405267402387485764147437 16651975275895307161555289)
              ·
                refine ⟨12488981456921480371166467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16651975275895307161555289 12488981456921480371166467)
                ·
                  refine ⟨18733472185382220556749701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12488981456921480371166467 18733472185382220556749701)
                  ·
                    refine ⟨3512526034759166354390569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18733472185382220556749701 3512526034759166354390569)
                    ·
                      refine ⟨2634394526069374765792927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3512526034759166354390569 2634394526069374765792927)
                      ·
                        rfl

theorem cell23_5130465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_5130465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130465 prefixEnd_5130465 := by exact prefixLift 5130465
  have htrace : WordTrace (prefixWord ++ tailWord_5130465) baseStart_5130465 baseEnd_5130465 := by
    simpa [prefixWord, tailWord_5130465, baseEnd_5130465] using wordTrace_append hprefix tailTrace_5130465
  have hstable : (prefixWord ++ tailWord_5130465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130465).length < 2 ^ (prefixWord ++ tailWord_5130465).sum := by decide
  have hdescent : baseEnd_5130465 < baseStart_5130465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130469 : List Nat := [1, 3, 1, 4, 2, 2, 3, 1, 1, 3, 2]
def baseStart_5130469 : Nat := 118140960795 + 5130469 * 2 ^ 59
def prefixEnd_5130469 : Nat := 4983230072969 + 3 ^ 40 * 5130469 * 2
def baseEnd_5130469 : Nat := 2634396579991992750142909

theorem tailTrace_5130469 : CollatzResearch.WordTrace tailWord_5130469 prefixEnd_5130469 2634396579991992750142909 := by
  unfold tailWord_5130469
  simp only [CollatzResearch.WordTrace]
  refine ⟨187123577250194502191322461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124749051500129668127548307 187123577250194502191322461)
  ·
    refine ⟨70171341468822938321745923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187123577250194502191322461 70171341468822938321745923)
    ·
      refine ⟨105257012203234407482618885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70171341468822938321745923 105257012203234407482618885)
      ·
        refine ⟨19735689788106451402991041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105257012203234407482618885 19735689788106451402991041)
        ·
          refine ⟨14801767341079838552243281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19735689788106451402991041 14801767341079838552243281)
          ·
            refine ⟨11101325505809878914182461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14801767341079838552243281 11101325505809878914182461)
            ·
              refine ⟨4162997064678704592818423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11101325505809878914182461 4162997064678704592818423)
              ·
                refine ⟨6244495597018056889227635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4162997064678704592818423 6244495597018056889227635)
                ·
                  refine ⟨9366743395527085333841453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6244495597018056889227635 9366743395527085333841453)
                  ·
                    refine ⟨3512528773322657000190545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9366743395527085333841453 3512528773322657000190545)
                    ·
                      refine ⟨2634396579991992750142909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3512528773322657000190545 2634396579991992750142909)
                      ·
                        rfl

theorem cell23_5130469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_5130469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130469 prefixEnd_5130469 := by exact prefixLift 5130469
  have htrace : WordTrace (prefixWord ++ tailWord_5130469) baseStart_5130469 baseEnd_5130469 := by
    simpa [prefixWord, tailWord_5130469, baseEnd_5130469] using wordTrace_append hprefix tailTrace_5130469
  have hstable : (prefixWord ++ tailWord_5130469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130469).length < 2 ^ (prefixWord ++ tailWord_5130469).sum := by decide
  have hdescent : baseEnd_5130469 < baseStart_5130469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130478 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_5130478 : Nat := 118140960795 + 5130478 * 2 ^ 59
def prefixEnd_5130478 : Nat := 4983230072969 + 3 ^ 40 * 5130478 * 2
def baseEnd_5130478 : Nat := 2634401201317883214930367

theorem tailTrace_5130478 : CollatzResearch.WordTrace tailWord_5130478 prefixEnd_5130478 2634401201317883214930367 := by
  unfold tailWord_5130478
  simp only [CollatzResearch.WordTrace]
  refine ⟨23390488188395237091050011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124749270338107931152266725 23390488188395237091050011)
  ·
    refine ⟨35085732282592855636575017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23390488188395237091050011 35085732282592855636575017)
    ·
      refine ⟨26314299211944641727431263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35085732282592855636575017 26314299211944641727431263)
      ·
        refine ⟨39471448817916962591146895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26314299211944641727431263 39471448817916962591146895)
        ·
          refine ⟨59207173226875443886720343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39471448817916962591146895 59207173226875443886720343)
          ·
            refine ⟨88810759840313165830080515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59207173226875443886720343 88810759840313165830080515)
            ·
              refine ⟨133216139760469748745120773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88810759840313165830080515 133216139760469748745120773)
              ·
                refine ⟨24978026205088077889710145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133216139760469748745120773 24978026205088077889710145)
                ·
                  refine ⟨18733519653816058417282609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24978026205088077889710145 18733519653816058417282609)
                  ·
                    refine ⟨14050139740362043812961957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18733519653816058417282609 14050139740362043812961957)
                    ·
                      refine ⟨2634401201317883214930367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14050139740362043812961957 2634401201317883214930367)
                      ·
                        rfl

theorem cell23_5130478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_5130478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130478 prefixEnd_5130478 := by exact prefixLift 5130478
  have htrace : WordTrace (prefixWord ++ tailWord_5130478) baseStart_5130478 baseEnd_5130478 := by
    simpa [prefixWord, tailWord_5130478, baseEnd_5130478] using wordTrace_append hprefix tailTrace_5130478
  have hstable : (prefixWord ++ tailWord_5130478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130478).length < 2 ^ (prefixWord ++ tailWord_5130478).sum := by decide
  have hdescent : baseEnd_5130478 < baseStart_5130478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130481 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 7]
def baseStart_5130481 : Nat := 118140960795 + 5130481 * 2 ^ 59
def prefixEnd_5130481 : Nat := 4983230072969 + 3 ^ 40 * 5130481 * 2
def baseEnd_5130481 : Nat := 2634402741759846703192853

theorem tailTrace_5130481 : CollatzResearch.WordTrace tailWord_5130481 prefixEnd_5130481 2634402741759846703192853 := by
  unfold tailWord_5130481
  simp only [CollatzResearch.WordTrace]
  refine ⟨187124014926151028240759297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124749343284100685493839531 187124014926151028240759297)
  ·
    refine ⟨140343011194613271180569473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187124014926151028240759297 140343011194613271180569473)
    ·
      refine ⟨105257258395959953385427105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140343011194613271180569473 105257258395959953385427105)
      ·
        refine ⟨78942943796969965039070329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105257258395959953385427105 78942943796969965039070329)
        ·
          refine ⟨59207207847727473779302747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78942943796969965039070329 59207207847727473779302747)
          ·
            refine ⟨88810811771591210668954121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59207207847727473779302747 88810811771591210668954121)
            ·
              refine ⟨66608108828693408001715591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88810811771591210668954121 66608108828693408001715591)
              ·
                refine ⟨99912163243040112002573387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66608108828693408001715591 99912163243040112002573387)
                ·
                  refine ⟨149868244864560168003860081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99912163243040112002573387 149868244864560168003860081)
                  ·
                    refine ⟨112401183648420126002895061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 149868244864560168003860081 112401183648420126002895061)
                    ·
                      refine ⟨2634402741759846703192853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112401183648420126002895061 2634402741759846703192853)
                      ·
                        rfl

theorem cell23_5130481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_5130481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130481 prefixEnd_5130481 := by exact prefixLift 5130481
  have htrace : WordTrace (prefixWord ++ tailWord_5130481) baseStart_5130481 baseEnd_5130481 := by
    simpa [prefixWord, tailWord_5130481, baseEnd_5130481] using wordTrace_append hprefix tailTrace_5130481
  have hstable : (prefixWord ++ tailWord_5130481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130481).length < 2 ^ (prefixWord ++ tailWord_5130481).sum := by decide
  have hdescent : baseEnd_5130481 < baseStart_5130481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130511 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 7]
def baseStart_5130511 : Nat := 118140960795 + 5130511 * 2 ^ 59
def prefixEnd_5130511 : Nat := 4983230072969 + 3 ^ 40 * 5130511 * 2
def baseEnd_5130511 : Nat := 2634418146179481585817715

theorem tailTrace_5130511 : CollatzResearch.WordTrace tailWord_5130511 prefixEnd_5130511 2634418146179481585817715 := by
  unfold tailWord_5130511
  simp only [CollatzResearch.WordTrace]
  refine ⟨187125109116042343364351387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124750072744028228909567591 187125109116042343364351387)
  ·
    refine ⟨280687663674063515046527081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187125109116042343364351387 280687663674063515046527081)
    ·
      refine ⟨210515747755547636284895311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280687663674063515046527081 210515747755547636284895311)
      ·
        refine ⟨315773621633321454427342967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210515747755547636284895311 315773621633321454427342967)
        ·
          refine ⟨473660432449982181641014451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315773621633321454427342967 473660432449982181641014451)
          ·
            refine ⟨710490648674973272461521677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473660432449982181641014451 710490648674973272461521677)
            ·
              refine ⟨266433993253114977173070629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 710490648674973272461521677 266433993253114977173070629)
              ·
                refine ⟨49956373734959058219950743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266433993253114977173070629 49956373734959058219950743)
                ·
                  refine ⟨74934560602438587329926115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49956373734959058219950743 74934560602438587329926115)
                  ·
                    refine ⟨112401840903657880994889173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74934560602438587329926115 112401840903657880994889173)
                    ·
                      refine ⟨2634418146179481585817715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112401840903657880994889173 2634418146179481585817715)
                      ·
                        rfl

theorem cell23_5130511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_5130511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130511 prefixEnd_5130511 := by exact prefixLift 5130511
  have htrace : WordTrace (prefixWord ++ tailWord_5130511) baseStart_5130511 baseEnd_5130511 := by
    simpa [prefixWord, tailWord_5130511, baseEnd_5130511] using wordTrace_append hprefix tailTrace_5130511
  have hstable : (prefixWord ++ tailWord_5130511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130511).length < 2 ^ (prefixWord ++ tailWord_5130511).sum := by decide
  have hdescent : baseEnd_5130511 < baseStart_5130511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130522 : List Nat := [3, 1, 1, 3, 4, 1, 2, 3, 5]
def baseStart_5130522 : Nat := 118140960795 + 5130522 * 2 ^ 59
def prefixEnd_5130522 : Nat := 4983230072969 + 3 ^ 40 * 5130522 * 2
def baseEnd_5130522 : Nat := 292713754940742338086685

theorem tailTrace_5130522 : CollatzResearch.WordTrace tailWord_5130522 prefixEnd_5130522 292713754940742338086685 := by
  unfold tailWord_5130522
  simp only [CollatzResearch.WordTrace]
  refine ⟨46781377579750623060750455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124750340212668328162001213 46781377579750623060750455)
  ·
    refine ⟨70172066369625934591125683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46781377579750623060750455 70172066369625934591125683)
    ·
      refine ⟨105258099554438901886688525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70172066369625934591125683 105258099554438901886688525)
      ·
        refine ⟨39471787332914588207508197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105258099554438901886688525 39471787332914588207508197)
        ·
          refine ⟨7400960124921485288907787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39471787332914588207508197 7400960124921485288907787)
          ·
            refine ⟨11101440187382227933361681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7400960124921485288907787 11101440187382227933361681)
            ·
              refine ⟨8326080140536670950021261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11101440187382227933361681 8326080140536670950021261)
              ·
                refine ⟨3122280052701251606257973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8326080140536670950021261 3122280052701251606257973)
                ·
                  refine ⟨292713754940742338086685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3122280052701251606257973 292713754940742338086685)
                  ·
                    rfl

theorem cell23_5130522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 5].length) (baseStart_5130522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130522 prefixEnd_5130522 := by exact prefixLift 5130522
  have htrace : WordTrace (prefixWord ++ tailWord_5130522) baseStart_5130522 baseEnd_5130522 := by
    simpa [prefixWord, tailWord_5130522, baseEnd_5130522] using wordTrace_append hprefix tailTrace_5130522
  have hstable : (prefixWord ++ tailWord_5130522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130522).length < 2 ^ (prefixWord ++ tailWord_5130522).sum := by decide
  have hdescent : baseEnd_5130522 < baseStart_5130522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130578 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 8]
def baseStart_5130578 : Nat := 118140960795 + 5130578 * 2 ^ 59
def prefixEnd_5130578 : Nat := 4983230072969 + 3 ^ 40 * 5130578 * 2
def baseEnd_5130578 : Nat := 292716949931481424853323

theorem tailTrace_5130578 : CollatzResearch.WordTrace tailWord_5130578 prefixEnd_5130578 292716949931481424853323 := by
  unfold tailWord_5130578
  simp only [CollatzResearch.WordTrace]
  refine ⟨46781888201699903451760097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124751701871199742538026925 46781888201699903451760097)
  ·
    refine ⟨35086416151274927588820073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46781888201699903451760097 35086416151274927588820073)
    ·
      refine ⟨26314812113456195691615055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35086416151274927588820073 26314812113456195691615055)
      ·
        refine ⟨39472218170184293537422583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26314812113456195691615055 39472218170184293537422583)
        ·
          refine ⟨59208327255276440306133875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39472218170184293537422583 59208327255276440306133875)
          ·
            refine ⟨88812490882914660459200813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59208327255276440306133875 88812490882914660459200813)
            ·
              refine ⟨33304684081092997672200305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88812490882914660459200813 33304684081092997672200305)
              ·
                refine ⟨24978513060819748254150229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33304684081092997672200305 24978513060819748254150229)
                ·
                  refine ⟨292716949931481424853323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24978513060819748254150229 292716949931481424853323)
                  ·
                    rfl

theorem cell23_5130578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_5130578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130578 prefixEnd_5130578 := by exact prefixLift 5130578
  have htrace : WordTrace (prefixWord ++ tailWord_5130578) baseStart_5130578 baseEnd_5130578 := by
    simpa [prefixWord, tailWord_5130578, baseEnd_5130578] using wordTrace_append hprefix tailTrace_5130578
  have hstable : (prefixWord ++ tailWord_5130578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130578).length < 2 ^ (prefixWord ++ tailWord_5130578).sum := by decide
  have hdescent : baseEnd_5130578 < baseStart_5130578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130590 : List Nat := [4, 4, 2, 1, 1, 1, 3, 2, 5]
def baseStart_5130590 : Nat := 118140960795 + 5130590 * 2 ^ 59
def prefixEnd_5130590 : Nat := 4983230072969 + 3 ^ 40 * 5130590 * 2
def baseEnd_5130590 : Nat := 292717634572354086303317

theorem tailTrace_5130590 : CollatzResearch.WordTrace tailWord_5130590 prefixEnd_5130590 292717634572354086303317 := by
  unfold tailWord_5130590
  simp only [CollatzResearch.WordTrace]
  refine ⟨23390998810344517482059653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124751993655170759904318149 23390998810344517482059653)
  ·
    refine ⟨4385812276939597027886185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23390998810344517482059653 4385812276939597027886185)
    ·
      refine ⟨3289359207704697770914639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4385812276939597027886185 3289359207704697770914639)
      ·
        refine ⟨4934038811557046656371959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3289359207704697770914639 4934038811557046656371959)
        ·
          refine ⟨7401058217335569984557939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4934038811557046656371959 7401058217335569984557939)
          ·
            refine ⟨11101587326003354976836909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7401058217335569984557939 11101587326003354976836909)
            ·
              refine ⟨4163095247251258116313841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11101587326003354976836909 4163095247251258116313841)
              ·
                refine ⟨3122321435438443587235381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4163095247251258116313841 3122321435438443587235381)
                ·
                  refine ⟨292717634572354086303317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3122321435438443587235381 292717634572354086303317)
                  ·
                    rfl

theorem cell23_5130590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_5130590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130590 prefixEnd_5130590 := by exact prefixLift 5130590
  have htrace : WordTrace (prefixWord ++ tailWord_5130590) baseStart_5130590 baseEnd_5130590 := by
    simpa [prefixWord, tailWord_5130590, baseEnd_5130590] using wordTrace_append hprefix tailTrace_5130590
  have hstable : (prefixWord ++ tailWord_5130590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130590).length < 2 ^ (prefixWord ++ tailWord_5130590).sum := by decide
  have hdescent : baseEnd_5130590 < baseStart_5130590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130592 : List Nat := [2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 3]
def baseStart_5130592 : Nat := 118140960795 + 5130592 * 2 ^ 59
def prefixEnd_5130592 : Nat := 4983230072969 + 3 ^ 40 * 5130592 * 2
def baseEnd_5130592 : Nat := 2634459738112495768904843

theorem tailTrace_5130592 : CollatzResearch.WordTrace tailWord_5130592 prefixEnd_5130592 2634459738112495768904843 := by
  unfold tailWord_5130592
  simp only [CollatzResearch.WordTrace]
  refine ⟨93564031714374447099025015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124752042285832596132033353 93564031714374447099025015)
  ·
    refine ⟨140346047571561670648537523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93564031714374447099025015 140346047571561670648537523)
    ·
      refine ⟨210519071357342505972806285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140346047571561670648537523 210519071357342505972806285)
      ·
        refine ⟨78944651759003439739802357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210519071357342505972806285 78944651759003439739802357)
        ·
          refine ⟨7401061102406572475606471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78944651759003439739802357 7401061102406572475606471)
          ·
            refine ⟨11101591653609858713409707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7401061102406572475606471 11101591653609858713409707)
            ·
              refine ⟨16652387480414788070114561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11101591653609858713409707 16652387480414788070114561)
              ·
                refine ⟨12489290610311091052585921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16652387480414788070114561 12489290610311091052585921)
                ·
                  refine ⟨9366967957733318289439441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12489290610311091052585921 9366967957733318289439441)
                  ·
                    refine ⟨7025225968299988717079581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9366967957733318289439441 7025225968299988717079581)
                    ·
                      refine ⟨2634459738112495768904843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7025225968299988717079581 2634459738112495768904843)
                      ·
                        rfl

theorem cell23_5130592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_5130592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130592 prefixEnd_5130592 := by exact prefixLift 5130592
  have htrace : WordTrace (prefixWord ++ tailWord_5130592) baseStart_5130592 baseEnd_5130592 := by
    simpa [prefixWord, tailWord_5130592, baseEnd_5130592] using wordTrace_append hprefix tailTrace_5130592
  have hstable : (prefixWord ++ tailWord_5130592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130592).length < 2 ^ (prefixWord ++ tailWord_5130592).sum := by decide
  have hdescent : baseEnd_5130592 < baseStart_5130592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130615 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 1, 5, 2]
def baseStart_5130615 : Nat := 118140960795 + 5130615 * 2 ^ 59
def prefixEnd_5130615 : Nat := 4983230072969 + 3 ^ 40 * 5130615 * 2
def baseEnd_5130615 : Nat := 2634471548167549178917237

theorem tailTrace_5130615 : CollatzResearch.WordTrace tailWord_5130615 prefixEnd_5130615 2634471548167549178917237 := by
  unfold tailWord_5130615
  simp only [CollatzResearch.WordTrace]
  refine ⟨187128902307665569126137299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124752601538443712750758199 187128902307665569126137299)
  ·
    refine ⟨280693353461498353689205949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187128902307665569126137299 280693353461498353689205949)
    ·
      refine ⟨105260007548061882633452231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280693353461498353689205949 105260007548061882633452231)
      ·
        refine ⟨157890011322092823950178347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105260007548061882633452231 157890011322092823950178347)
        ·
          refine ⟨236835016983139235925267521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157890011322092823950178347 236835016983139235925267521)
          ·
            refine ⟨177626262737354426943950641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236835016983139235925267521 177626262737354426943950641)
            ·
              refine ⟨133219697053015820207962981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177626262737354426943950641 133219697053015820207962981)
              ·
                refine ⟨24978693197440466288993059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133219697053015820207962981 24978693197440466288993059)
                ·
                  refine ⟨37468039796160699433489589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24978693197440466288993059 37468039796160699433489589)
                  ·
                    refine ⟨3512628730890065571889649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37468039796160699433489589 3512628730890065571889649)
                    ·
                      refine ⟨2634471548167549178917237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3512628730890065571889649 2634471548167549178917237)
                      ·
                        rfl

theorem cell23_5130615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 5, 2].length) (baseStart_5130615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130615 prefixEnd_5130615 := by exact prefixLift 5130615
  have htrace : WordTrace (prefixWord ++ tailWord_5130615) baseStart_5130615 baseEnd_5130615 := by
    simpa [prefixWord, tailWord_5130615, baseEnd_5130615] using wordTrace_append hprefix tailTrace_5130615
  have hstable : (prefixWord ++ tailWord_5130615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130615).length < 2 ^ (prefixWord ++ tailWord_5130615).sum := by decide
  have hdescent : baseEnd_5130615 < baseStart_5130615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130626 : List Nat := [3, 4, 2, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_5130626 : Nat := 118140960795 + 5130626 * 2 ^ 59
def prefixEnd_5130626 : Nat := 4983230072969 + 3 ^ 40 * 5130626 * 2
def baseEnd_5130626 : Nat := 2634477196454748635879687

theorem tailTrace_5130626 : CollatzResearch.WordTrace tailWord_5130626 prefixEnd_5130626 2634477196454748635879687 := by
  unfold tailWord_5130626
  simp only [CollatzResearch.WordTrace]
  refine ⟨46782325877656429501196933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124752869007083812003191821 46782325877656429501196933)
  ·
    refine ⟨8771686102060580531474425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46782325877656429501196933 8771686102060580531474425)
    ·
      refine ⟨6578764576545435398605819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8771686102060580531474425 6578764576545435398605819)
      ·
        refine ⟨9868146864818153097908729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6578764576545435398605819 9868146864818153097908729)
        ·
          refine ⟨7401110148613614823431547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9868146864818153097908729 7401110148613614823431547)
          ·
            refine ⟨11101665222920422235147321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7401110148613614823431547 11101665222920422235147321)
            ·
              refine ⟨8326248917190316676360491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11101665222920422235147321 8326248917190316676360491)
              ·
                refine ⟨12489373375785475014540737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8326248917190316676360491 12489373375785475014540737)
                ·
                  refine ⟨9367030031839106260905553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12489373375785475014540737 9367030031839106260905553)
                  ·
                    refine ⟨7025272523879329695679165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9367030031839106260905553 7025272523879329695679165)
                    ·
                      refine ⟨2634477196454748635879687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7025272523879329695679165 2634477196454748635879687)
                      ·
                        rfl

theorem cell23_5130626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_5130626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130626 prefixEnd_5130626 := by exact prefixLift 5130626
  have htrace : WordTrace (prefixWord ++ tailWord_5130626) baseStart_5130626 baseEnd_5130626 := by
    simpa [prefixWord, tailWord_5130626, baseEnd_5130626] using wordTrace_append hprefix tailTrace_5130626
  have hstable : (prefixWord ++ tailWord_5130626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130626).length < 2 ^ (prefixWord ++ tailWord_5130626).sum := by decide
  have hdescent : baseEnd_5130626 < baseStart_5130626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130656 : List Nat := [2, 1, 1, 4, 1, 3, 4, 2, 1, 1, 3]
def baseStart_5130656 : Nat := 118140960795 + 5130656 * 2 ^ 59
def prefixEnd_5130656 : Nat := 4983230072969 + 3 ^ 40 * 5130656 * 2
def baseEnd_5130656 : Nat := 2634492600874383518504549

theorem tailTrace_5130656 : CollatzResearch.WordTrace tailWord_5130656 prefixEnd_5130656 2634492600874383518504549 := by
  unfold tailWord_5130656
  simp only [CollatzResearch.WordTrace]
  refine ⟨93565198850258516564189911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124753598467011355418919881 93565198850258516564189911)
  ·
    refine ⟨140347798275387774846284867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93565198850258516564189911 140347798275387774846284867)
    ·
      refine ⟨210521697413081662269427301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140347798275387774846284867 210521697413081662269427301)
      ·
        refine ⟨39472818264952811675517619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210521697413081662269427301 39472818264952811675517619)
        ·
          refine ⟨59209227397429217513276429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39472818264952811675517619 59209227397429217513276429)
          ·
            refine ⟨22203460274035956567478661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59209227397429217513276429 22203460274035956567478661)
            ·
              refine ⟨4163148801381741856402249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22203460274035956567478661 4163148801381741856402249)
              ·
                refine ⟨3122361601036306392301687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4163148801381741856402249 3122361601036306392301687)
                ·
                  refine ⟨4683542401554459588452531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3122361601036306392301687 4683542401554459588452531)
                  ·
                    refine ⟨7025313602331689382678797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4683542401554459588452531 7025313602331689382678797)
                    ·
                      refine ⟨2634492600874383518504549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7025313602331689382678797 2634492600874383518504549)
                      ·
                        rfl

theorem cell23_5130656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_5130656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130656 prefixEnd_5130656 := by exact prefixLift 5130656
  have htrace : WordTrace (prefixWord ++ tailWord_5130656) baseStart_5130656 baseEnd_5130656 := by
    simpa [prefixWord, tailWord_5130656, baseEnd_5130656] using wordTrace_append hprefix tailTrace_5130656
  have hstable : (prefixWord ++ tailWord_5130656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130656).length < 2 ^ (prefixWord ++ tailWord_5130656).sum := by decide
  have hdescent : baseEnd_5130656 < baseStart_5130656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130679 : List Nat := [1, 1, 3, 1, 3, 4, 1, 2, 3, 2, 2]
def baseStart_5130679 : Nat := 118140960795 + 5130679 * 2 ^ 59
def prefixEnd_5130679 : Nat := 4983230072969 + 3 ^ 40 * 5130679 * 2
def baseEnd_5130679 : Nat := 2634504410929436928516943

theorem tailTrace_5130679 : CollatzResearch.WordTrace tailWord_5130679 prefixEnd_5130679 2634504410929436928516943 := by
  unfold tailWord_5130679
  simp only [CollatzResearch.WordTrace]
  refine ⟨187131236579433708056467091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124754157719622472037644727 187131236579433708056467091)
  ·
    refine ⟨280696854869150562084700637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187131236579433708056467091 280696854869150562084700637)
    ·
      refine ⟨105261320575931460781762739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280696854869150562084700637 105261320575931460781762739)
      ·
        refine ⟨157891980863897191172644109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105261320575931460781762739 157891980863897191172644109)
        ·
          refine ⟨59209492823961446689741541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157891980863897191172644109 59209492823961446689741541)
          ·
            refine ⟨11101779904492771254326539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59209492823961446689741541 11101779904492771254326539)
            ·
              refine ⟨16652669856739156881489809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11101779904492771254326539 16652669856739156881489809)
              ·
                refine ⟨12489502392554367661117357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16652669856739156881489809 12489502392554367661117357)
                ·
                  refine ⟨4683563397207887872919009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12489502392554367661117357 4683563397207887872919009)
                  ·
                    refine ⟨3512672547905915904689257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4683563397207887872919009 3512672547905915904689257)
                    ·
                      refine ⟨2634504410929436928516943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3512672547905915904689257 2634504410929436928516943)
                      ·
                        rfl

theorem cell23_5130679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 2, 2].length) (baseStart_5130679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130679 prefixEnd_5130679 := by exact prefixLift 5130679
  have htrace : WordTrace (prefixWord ++ tailWord_5130679) baseStart_5130679 baseEnd_5130679 := by
    simpa [prefixWord, tailWord_5130679, baseEnd_5130679] using wordTrace_append hprefix tailTrace_5130679
  have hstable : (prefixWord ++ tailWord_5130679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130679).length < 2 ^ (prefixWord ++ tailWord_5130679).sum := by decide
  have hdescent : baseEnd_5130679 < baseStart_5130679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130696 : List Nat := [2, 1, 3, 1, 3, 2, 1, 5, 1, 2, 2]
def baseStart_5130696 : Nat := 118140960795 + 5130696 * 2 ^ 59
def prefixEnd_5130696 : Nat := 4983230072969 + 3 ^ 40 * 5130696 * 2
def baseEnd_5130696 : Nat := 2634513140100563362004365

theorem tailTrace_5130696 : CollatzResearch.WordTrace tailWord_5130696 prefixEnd_5130696 2634513140100563362004365 := by
  unfold tailWord_5130696
  simp only [CollatzResearch.WordTrace]
  refine ⟨93565928310186059979917971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124754571080248079973223961 93565928310186059979917971)
  ·
    refine ⟨140348892465279089969876957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93565928310186059979917971 140348892465279089969876957)
    ·
      refine ⟨52630834674479658738703859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140348892465279089969876957 52630834674479658738703859)
      ·
        refine ⟨78946252011719488108055789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52630834674479658738703859 78946252011719488108055789)
        ·
          refine ⟨29604844504394808040520921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78946252011719488108055789 29604844504394808040520921)
          ·
            refine ⟨22203633378296106030390691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29604844504394808040520921 22203633378296106030390691)
            ·
              refine ⟨33305450067444159045586037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22203633378296106030390691 33305450067444159045586037)
              ·
                refine ⟨3122385943822889910523691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33305450067444159045586037 3122385943822889910523691)
                ·
                  refine ⟨4683578915734334865785537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3122385943822889910523691 4683578915734334865785537)
                  ·
                    refine ⟨3512684186800751149339153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4683578915734334865785537 3512684186800751149339153)
                    ·
                      refine ⟨2634513140100563362004365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3512684186800751149339153 2634513140100563362004365)
                      ·
                        rfl

theorem cell23_5130696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 1, 2, 2].length) (baseStart_5130696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130696 prefixEnd_5130696 := by exact prefixLift 5130696
  have htrace : WordTrace (prefixWord ++ tailWord_5130696) baseStart_5130696 baseEnd_5130696 := by
    simpa [prefixWord, tailWord_5130696, baseEnd_5130696] using wordTrace_append hprefix tailTrace_5130696
  have hstable : (prefixWord ++ tailWord_5130696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130696).length < 2 ^ (prefixWord ++ tailWord_5130696).sum := by decide
  have hdescent : baseEnd_5130696 < baseStart_5130696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130739 : List Nat := [1, 1, 1, 2, 2, 2, 6, 2, 1, 3, 2]
def baseStart_5130739 : Nat := 118140960795 + 5130739 * 2 ^ 59
def prefixEnd_5130739 : Nat := 4983230072969 + 3 ^ 40 * 5130739 * 2
def baseEnd_5130739 : Nat := 2634535219768706693766667

theorem tailTrace_5130739 : CollatzResearch.WordTrace tailWord_5130739 prefixEnd_5130739 2634535219768706693766667 := by
  unfold tailWord_5130739
  simp only [CollatzResearch.WordTrace]
  refine ⟨187133424959216338303651271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124755616639477558869100847 187133424959216338303651271)
  ·
    refine ⟨280700137438824507455476907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187133424959216338303651271 280700137438824507455476907)
    ·
      refine ⟨421050206158236761183215361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280700137438824507455476907 421050206158236761183215361)
      ·
        refine ⟨315787654618677570887411521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421050206158236761183215361 315787654618677570887411521)
        ·
          refine ⟨236840740964008178165558641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315787654618677570887411521 236840740964008178165558641)
          ·
            refine ⟨177630555723006133624168981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236840740964008178165558641 177630555723006133624168981)
            ·
              refine ⟨8326432299515912513632921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 177630555723006133624168981 8326432299515912513632921)
              ·
                refine ⟨6244824224636934385224691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8326432299515912513632921 6244824224636934385224691)
                ·
                  refine ⟨9367236336955401577837037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6244824224636934385224691 9367236336955401577837037)
                  ·
                    refine ⟨3512713626358275591688889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9367236336955401577837037 3512713626358275591688889)
                    ·
                      refine ⟨2634535219768706693766667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3512713626358275591688889 2634535219768706693766667)
                      ·
                        rfl

theorem cell23_5130739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 3, 2].length) (baseStart_5130739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130739 prefixEnd_5130739 := by exact prefixLift 5130739
  have htrace : WordTrace (prefixWord ++ tailWord_5130739) baseStart_5130739 baseEnd_5130739 := by
    simpa [prefixWord, tailWord_5130739, baseEnd_5130739] using wordTrace_append hprefix tailTrace_5130739
  have hstable : (prefixWord ++ tailWord_5130739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130739).length < 2 ^ (prefixWord ++ tailWord_5130739).sum := by decide
  have hdescent : baseEnd_5130739 < baseStart_5130739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130755 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 5]
def baseStart_5130755 : Nat := 118140960795 + 5130755 * 2 ^ 59
def prefixEnd_5130755 : Nat := 4983230072969 + 3 ^ 40 * 5130755 * 2
def baseEnd_5130755 : Nat := 2634543435459178631166593

theorem tailTrace_5130755 : CollatzResearch.WordTrace tailWord_5130755 prefixEnd_5130755 2634543435459178631166593 := by
  unfold tailWord_5130755
  simp only [CollatzResearch.WordTrace]
  refine ⟨187134008527158373036233719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124756005684772248690822479 187134008527158373036233719)
  ·
    refine ⟨280701012790737559554350579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187134008527158373036233719 280701012790737559554350579)
    ·
      refine ⟨421051519186106339331525869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280701012790737559554350579 421051519186106339331525869)
      ·
        refine ⟨157894319694789877249322201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 421051519186106339331525869 157894319694789877249322201)
        ·
          refine ⟨118420739771092407936991651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157894319694789877249322201 118420739771092407936991651)
          ·
            refine ⟨177631109656638611905487477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118420739771092407936991651 177631109656638611905487477)
            ·
              refine ⟨16652916530309869866139451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 177631109656638611905487477 16652916530309869866139451)
              ·
                refine ⟨24979374795464804799209177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16652916530309869866139451 24979374795464804799209177)
                ·
                  refine ⟨18734531096598603599406883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24979374795464804799209177 18734531096598603599406883)
                  ·
                    refine ⟨28101796644897905399110325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18734531096598603599406883 28101796644897905399110325)
                    ·
                      refine ⟨2634543435459178631166593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28101796644897905399110325 2634543435459178631166593)
                      ·
                        rfl

theorem cell23_5130755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_5130755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130755 prefixEnd_5130755 := by exact prefixLift 5130755
  have htrace : WordTrace (prefixWord ++ tailWord_5130755) baseStart_5130755 baseEnd_5130755 := by
    simpa [prefixWord, tailWord_5130755, baseEnd_5130755] using wordTrace_append hprefix tailTrace_5130755
  have hstable : (prefixWord ++ tailWord_5130755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130755).length < 2 ^ (prefixWord ++ tailWord_5130755).sum := by decide
  have hdescent : baseEnd_5130755 < baseStart_5130755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130756 : List Nat := [2, 3, 2, 3, 1, 1, 2, 3, 1, 3, 2]
def baseStart_5130756 : Nat := 118140960795 + 5130756 * 2 ^ 59
def prefixEnd_5130756 : Nat := 4983230072969 + 3 ^ 40 * 5130756 * 2
def baseEnd_5130756 : Nat := 2634543948939833127254089

theorem tailTrace_5130756 : CollatzResearch.WordTrace tailWord_5130756 prefixEnd_5130756 2634543948939833127254089 := by
  unfold tailWord_5130756
  simp only [CollatzResearch.WordTrace]
  refine ⟨93567022500077375103510061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124756030000103166804680081 93567022500077375103510061)
  ·
    refine ⟨35087633437529015663816273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93567022500077375103510061 35087633437529015663816273)
    ·
      refine ⟨26315725078146761747862205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35087633437529015663816273 26315725078146761747862205)
      ·
        refine ⟨9868396904305035655448327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26315725078146761747862205 9868396904305035655448327)
        ·
          refine ⟨14802595356457553483172491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9868396904305035655448327 14802595356457553483172491)
          ·
            refine ⟨22203893034686330224758737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14802595356457553483172491 22203893034686330224758737)
            ·
              refine ⟨16652919776014747668569053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22203893034686330224758737 16652919776014747668569053)
              ·
                refine ⟨6244844916005530375713395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16652919776014747668569053 6244844916005530375713395)
                ·
                  refine ⟨9367267374008295563570093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6244844916005530375713395 9367267374008295563570093)
                  ·
                    refine ⟨3512725265253110836338785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9367267374008295563570093 3512725265253110836338785)
                    ·
                      refine ⟨2634543948939833127254089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3512725265253110836338785 2634543948939833127254089)
                      ·
                        rfl

theorem cell23_5130756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_5130756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130756 prefixEnd_5130756 := by exact prefixLift 5130756
  have htrace : WordTrace (prefixWord ++ tailWord_5130756) baseStart_5130756 baseEnd_5130756 := by
    simpa [prefixWord, tailWord_5130756, baseEnd_5130756] using wordTrace_append hprefix tailTrace_5130756
  have hstable : (prefixWord ++ tailWord_5130756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130756).length < 2 ^ (prefixWord ++ tailWord_5130756).sum := by decide
  have hdescent : baseEnd_5130756 < baseStart_5130756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130815 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 5]
def baseStart_5130815 : Nat := 118140960795 + 5130815 * 2 ^ 59
def prefixEnd_5130815 : Nat := 4983230072969 + 3 ^ 40 * 5130815 * 2
def baseEnd_5130815 : Nat := 2634574244298448396416317

theorem tailTrace_5130815 : CollatzResearch.WordTrace tailWord_5130815 prefixEnd_5130815 2634574244298448396416317 := by
  unfold tailWord_5130815
  simp only [CollatzResearch.WordTrace]
  refine ⟨187136196906941003283417899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124757464604627335522278599 187136196906941003283417899)
  ·
    refine ⟨280704295360411504925126849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187136196906941003283417899 280704295360411504925126849)
    ·
      refine ⟨210528221520308628693845137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280704295360411504925126849 210528221520308628693845137)
      ·
        refine ⟨157896166140231471520383853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210528221520308628693845137 157896166140231471520383853)
        ·
          refine ⟨59211062302586801820143945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157896166140231471520383853 59211062302586801820143945)
          ·
            refine ⟨44408296726940101365107959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59211062302586801820143945 44408296726940101365107959)
            ·
              refine ⟨66612445090410152047661939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44408296726940101365107959 66612445090410152047661939)
              ·
                refine ⟨99918667635615228071492909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66612445090410152047661939 99918667635615228071492909)
                ·
                  refine ⟨37469500363355710526809841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99918667635615228071492909 37469500363355710526809841)
                  ·
                    refine ⟨28102125272516782895107381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37469500363355710526809841 28102125272516782895107381)
                    ·
                      refine ⟨2634574244298448396416317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28102125272516782895107381 2634574244298448396416317)
                      ·
                        rfl

theorem cell23_5130815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_5130815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130815 prefixEnd_5130815 := by exact prefixLift 5130815
  have htrace : WordTrace (prefixWord ++ tailWord_5130815) baseStart_5130815 baseEnd_5130815 := by
    simpa [prefixWord, tailWord_5130815, baseEnd_5130815] using wordTrace_append hprefix tailTrace_5130815
  have hstable : (prefixWord ++ tailWord_5130815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130815).length < 2 ^ (prefixWord ++ tailWord_5130815).sum := by decide
  have hdescent : baseEnd_5130815 < baseStart_5130815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130825 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 5, 3, 4]
def baseStart_5130825 : Nat := 118140960795 + 5130825 * 2 ^ 59
def prefixEnd_5130825 : Nat := 4983230072969 + 3 ^ 40 * 5130825 * 2
def baseEnd_5130825 : Nat := 2634579379104993357291271

theorem tailTrace_5130825 : CollatzResearch.WordTrace tailWord_5130825 prefixEnd_5130825 2634579379104993357291271 := by
  unfold tailWord_5130825
  simp only [CollatzResearch.WordTrace]
  refine ⟨187136561636904774991281929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124757707757936516660854619 187136561636904774991281929)
  ·
    refine ⟨140352421227678581243461447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187136561636904774991281929 140352421227678581243461447)
    ·
      refine ⟨210528631841517871865192171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140352421227678581243461447 210528631841517871865192171)
      ·
        refine ⟨315792947762276807797788257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210528631841517871865192171 315792947762276807797788257)
        ·
          refine ⟨236844710821707605848341193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315792947762276807797788257 236844710821707605848341193)
          ·
            refine ⟨177633533116280704386255895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236844710821707605848341193 177633533116280704386255895)
            ·
              refine ⟨266450299674421056579383843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177633533116280704386255895 266450299674421056579383843)
              ·
                refine ⟨399675449511631584869075765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266450299674421056579383843 399675449511631584869075765)
                ·
                  refine ⟨37469573391715461081475853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 399675449511631584869075765 37469573391715461081475853)
                  ·
                    refine ⟨14051090021893297905553445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37469573391715461081475853 14051090021893297905553445)
                    ·
                      refine ⟨2634579379104993357291271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14051090021893297905553445 2634579379104993357291271)
                      ·
                        rfl

theorem cell23_5130825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_5130825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130825 prefixEnd_5130825 := by exact prefixLift 5130825
  have htrace : WordTrace (prefixWord ++ tailWord_5130825) baseStart_5130825 baseEnd_5130825 := by
    simpa [prefixWord, tailWord_5130825, baseEnd_5130825] using wordTrace_append hprefix tailTrace_5130825
  have hstable : (prefixWord ++ tailWord_5130825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130825).length < 2 ^ (prefixWord ++ tailWord_5130825).sum := by decide
  have hdescent : baseEnd_5130825 < baseStart_5130825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130826 : List Nat := [3, 1, 2, 1, 1, 6, 2, 2, 5]
def baseStart_5130826 : Nat := 118140960795 + 5130826 * 2 ^ 59
def prefixEnd_5130826 : Nat := 4983230072969 + 3 ^ 40 * 5130826 * 2
def baseEnd_5130826 : Nat := 292731099176183094819863

theorem tailTrace_5130826 : CollatzResearch.WordTrace tailWord_5130826 prefixEnd_5130826 292731099176183094819863 := by
  unfold tailWord_5130826
  simp only [CollatzResearch.WordTrace]
  refine ⟨46784149527475288040517083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124757732073267434774712221 46784149527475288040517083)
  ·
    refine ⟨70176224291212932060775625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46784149527475288040517083 70176224291212932060775625)
    ·
      refine ⟨52632168218409699045581719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70176224291212932060775625 52632168218409699045581719)
      ·
        refine ⟨78948252327614548568372579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52632168218409699045581719 78948252327614548568372579)
        ·
          refine ⟨118422378491421822852558869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78948252327614548568372579 118422378491421822852558869)
          ·
            refine ⟨5551048991785397946213697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 118422378491421822852558869 5551048991785397946213697)
            ·
              refine ⟨4163286743839048459660273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5551048991785397946213697 4163286743839048459660273)
              ·
                refine ⟨3122465057879286344745205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4163286743839048459660273 3122465057879286344745205)
                ·
                  refine ⟨292731099176183094819863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3122465057879286344745205 292731099176183094819863)
                  ·
                    rfl

theorem cell23_5130826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 5].length) (baseStart_5130826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130826 prefixEnd_5130826 := by exact prefixLift 5130826
  have htrace : WordTrace (prefixWord ++ tailWord_5130826) baseStart_5130826 baseEnd_5130826 := by
    simpa [prefixWord, tailWord_5130826, baseEnd_5130826] using wordTrace_append hprefix tailTrace_5130826
  have hstable : (prefixWord ++ tailWord_5130826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130826).length < 2 ^ (prefixWord ++ tailWord_5130826).sum := by decide
  have hdescent : baseEnd_5130826 < baseStart_5130826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130856 : List Nat := [2, 1, 4, 3, 2, 2, 1, 1, 2, 5]
def baseStart_5130856 : Nat := 118140960795 + 5130856 * 2 ^ 59
def prefixEnd_5130856 : Nat := 4983230072969 + 3 ^ 40 * 5130856 * 2
def baseEnd_5130856 : Nat := 878198432335094245334543

theorem tailTrace_5130856 : CollatzResearch.WordTrace tailWord_5130856 prefixEnd_5130856 878198432335094245334543 := by
  unfold tailWord_5130856
  simp only [CollatzResearch.WordTrace]
  refine ⟨93568846149896233642830211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124758461533194978190440281 93568846149896233642830211)
  ·
    refine ⟨140353269224844350464245317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93568846149896233642830211 140353269224844350464245317)
    ·
      refine ⟨26316237979658315712045997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140353269224844350464245317 26316237979658315712045997)
      ·
        refine ⟨9868589242371868392017249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26316237979658315712045997 9868589242371868392017249)
        ·
          refine ⟨7401441931778901294012937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9868589242371868392017249 7401441931778901294012937)
          ·
            refine ⟨5551081448834175970509703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7401441931778901294012937 5551081448834175970509703)
            ·
              refine ⟨8326622173251263955764555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5551081448834175970509703 8326622173251263955764555)
              ·
                refine ⟨12489933259876895933646833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8326622173251263955764555 12489933259876895933646833)
                ·
                  refine ⟨9367449944907671950235125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12489933259876895933646833 9367449944907671950235125)
                  ·
                    refine ⟨878198432335094245334543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9367449944907671950235125 878198432335094245334543)
                    ·
                      rfl

theorem cell23_5130856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_5130856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130856 prefixEnd_5130856 := by exact prefixLift 5130856
  have htrace : WordTrace (prefixWord ++ tailWord_5130856) baseStart_5130856 baseEnd_5130856 := by
    simpa [prefixWord, tailWord_5130856, baseEnd_5130856] using wordTrace_append hprefix tailTrace_5130856
  have hstable : (prefixWord ++ tailWord_5130856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130856).length < 2 ^ (prefixWord ++ tailWord_5130856).sum := by decide
  have hdescent : baseEnd_5130856 < baseStart_5130856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130969 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 3, 2, 3]
def baseStart_5130969 : Nat := 118140960795 + 5130969 * 2 ^ 59
def prefixEnd_5130969 : Nat := 4983230072969 + 3 ^ 40 * 5130969 * 2
def baseEnd_5130969 : Nat := 2634653320319240793890609

theorem tailTrace_5130969 : CollatzResearch.WordTrace tailWord_5130969 prefixEnd_5130969 2634653320319240793890609 := by
  unfold tailWord_5130969
  simp only [CollatzResearch.WordTrace]
  refine ⟨187141813748383087584523961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124761209165588725056349307 187141813748383087584523961)
  ·
    refine ⟨140356360311287315688392971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187141813748383087584523961 140356360311287315688392971)
    ·
      refine ⟨210534540466930973532589457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140356360311287315688392971 210534540466930973532589457)
      ·
        refine ⟨157900905350198230149442093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210534540466930973532589457 157900905350198230149442093)
        ·
          refine ⟨59212839506324336306040785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157900905350198230149442093 59212839506324336306040785)
          ·
            refine ⟨44409629629743252229530589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59212839506324336306040785 44409629629743252229530589)
            ·
              refine ⟨16653611111153719586073971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44409629629743252229530589 16653611111153719586073971)
              ·
                refine ⟨24980416666730579379110957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16653611111153719586073971 24980416666730579379110957)
                ·
                  refine ⟨9367656250023967267166609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24980416666730579379110957 9367656250023967267166609)
                  ·
                    refine ⟨7025742187517975450374957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9367656250023967267166609 7025742187517975450374957)
                    ·
                      refine ⟨2634653320319240793890609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7025742187517975450374957 2634653320319240793890609)
                      ·
                        rfl

theorem cell23_5130969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_5130969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130969 prefixEnd_5130969 := by exact prefixLift 5130969
  have htrace : WordTrace (prefixWord ++ tailWord_5130969) baseStart_5130969 baseEnd_5130969 := by
    simpa [prefixWord, tailWord_5130969, baseEnd_5130969] using wordTrace_append hprefix tailTrace_5130969
  have hstable : (prefixWord ++ tailWord_5130969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130969).length < 2 ^ (prefixWord ++ tailWord_5130969).sum := by decide
  have hdescent : baseEnd_5130969 < baseStart_5130969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130979 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 4]
def baseStart_5130979 : Nat := 118140960795 + 5130979 * 2 ^ 59
def prefixEnd_5130979 : Nat := 4983230072969 + 3 ^ 40 * 5130979 * 2
def baseEnd_5130979 : Nat := 2634658455125785754765563

theorem tailTrace_5130979 : CollatzResearch.WordTrace tailWord_5130979 prefixEnd_5130979 2634658455125785754765563 := by
  unfold tailWord_5130979
  simp only [CollatzResearch.WordTrace]
  refine ⟨187142178478346859292387991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124761452318897906194925327 187142178478346859292387991)
  ·
    refine ⟨280713267717520288938581987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187142178478346859292387991 280713267717520288938581987)
    ·
      refine ⟨421069901576280433407872981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280713267717520288938581987 421069901576280433407872981)
      ·
        refine ⟨9868825818194072657997023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 421069901576280433407872981 9868825818194072657997023)
        ·
          refine ⟨14803238727291108986995535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9868825818194072657997023 14803238727291108986995535)
          ·
            refine ⟨22204858090936663480493303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14803238727291108986995535 22204858090936663480493303)
            ·
              refine ⟨33307287136404995220739955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22204858090936663480493303 33307287136404995220739955)
              ·
                refine ⟨49960930704607492831109933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33307287136404995220739955 49960930704607492831109933)
                ·
                  refine ⟨18735349014227809811666225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49960930704607492831109933 18735349014227809811666225)
                  ·
                    refine ⟨14051511760670857358749669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18735349014227809811666225 14051511760670857358749669)
                    ·
                      refine ⟨2634658455125785754765563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14051511760670857358749669 2634658455125785754765563)
                      ·
                        rfl

theorem cell23_5130979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_5130979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5130979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5130979 prefixEnd_5130979 := by exact prefixLift 5130979
  have htrace : WordTrace (prefixWord ++ tailWord_5130979) baseStart_5130979 baseEnd_5130979 := by
    simpa [prefixWord, tailWord_5130979, baseEnd_5130979] using wordTrace_append hprefix tailTrace_5130979
  have hstable : (prefixWord ++ tailWord_5130979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130979).length < 2 ^ (prefixWord ++ tailWord_5130979).sum := by decide
  have hdescent : baseEnd_5130979 < baseStart_5130979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131002 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 2, 7]
def baseStart_5131002 : Nat := 118140960795 + 5131002 * 2 ^ 59
def prefixEnd_5131002 : Nat := 4983230072969 + 3 ^ 40 * 5131002 * 2
def baseEnd_5131002 : Nat := 878223421726946388259319

theorem tailTrace_5131002 : CollatzResearch.WordTrace tailWord_5131002 prefixEnd_5131002 878223421726946388259319 := by
  unfold tailWord_5131002
  simp only [CollatzResearch.WordTrace]
  refine ⟨46785754339315883555118815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124762011571509022813650173 46785754339315883555118815)
  ·
    refine ⟨70178631508973825332678223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46785754339315883555118815 70178631508973825332678223)
    ·
      refine ⟨105267947263460737999017335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70178631508973825332678223 105267947263460737999017335)
      ·
        refine ⟨157901920895191106998526003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105267947263460737999017335 157901920895191106998526003)
        ·
          refine ⟨236852881342786660497789005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157901920895191106998526003 236852881342786660497789005)
          ·
            refine ⟨88819830503544997686670877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 236852881342786660497789005 88819830503544997686670877)
            ·
              refine ⟨33307436438829374132501579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88819830503544997686670877 33307436438829374132501579)
              ·
                refine ⟨49961154658244061198752369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33307436438829374132501579 49961154658244061198752369)
                ·
                  refine ⟨37470865993683045899064277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49961154658244061198752369 37470865993683045899064277)
                  ·
                    refine ⟨878223421726946388259319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37470865993683045899064277 878223421726946388259319)
                    ·
                      rfl

theorem cell23_5131002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_5131002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131002 prefixEnd_5131002 := by exact prefixLift 5131002
  have htrace : WordTrace (prefixWord ++ tailWord_5131002) baseStart_5131002 baseEnd_5131002 := by
    simpa [prefixWord, tailWord_5131002, baseEnd_5131002] using wordTrace_append hprefix tailTrace_5131002
  have hstable : (prefixWord ++ tailWord_5131002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131002).length < 2 ^ (prefixWord ++ tailWord_5131002).sum := by decide
  have hdescent : baseEnd_5131002 < baseStart_5131002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131006 : List Nat := [4, 2, 2, 1, 2, 3, 1, 8]
def baseStart_5131006 : Nat := 118140960795 + 5131006 * 2 ^ 59
def prefixEnd_5131006 : Nat := 4983230072969 + 3 ^ 40 * 5131006 * 2
def baseEnd_5131006 : Nat := 97580456263091005523257

theorem tailTrace_5131006 : CollatzResearch.WordTrace tailWord_5131006 prefixEnd_5131006 97580456263091005523257 := by
  unfold tailWord_5131006
  simp only [CollatzResearch.WordTrace]
  refine ⟨23392895406156130362952609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124762108832832695269080581 23392895406156130362952609)
  ·
    refine ⟨17544671554617097772214457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23392895406156130362952609 17544671554617097772214457)
    ·
      refine ⟨13158503665962823329160843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17544671554617097772214457 13158503665962823329160843)
      ·
        refine ⟨19737755498944234993741265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13158503665962823329160843 19737755498944234993741265)
        ·
          refine ⟨14803316624208176245305949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19737755498944234993741265 14803316624208176245305949)
          ·
            refine ⟨5551243734078066091989731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14803316624208176245305949 5551243734078066091989731)
            ·
              refine ⟨8326865601117099137984597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5551243734078066091989731 8326865601117099137984597)
              ·
                refine ⟨97580456263091005523257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8326865601117099137984597 97580456263091005523257)
                ·
                  rfl

theorem cell23_5131006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 8].length) (baseStart_5131006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131006 prefixEnd_5131006 := by exact prefixLift 5131006
  have htrace : WordTrace (prefixWord ++ tailWord_5131006) baseStart_5131006 baseEnd_5131006 := by
    simpa [prefixWord, tailWord_5131006, baseEnd_5131006] using wordTrace_append hprefix tailTrace_5131006
  have hstable : (prefixWord ++ tailWord_5131006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131006).length < 2 ^ (prefixWord ++ tailWord_5131006).sum := by decide
  have hdescent : baseEnd_5131006 < baseStart_5131006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131016 : List Nat := [2, 1, 3, 2, 2, 3, 2, 1, 1, 3, 3]
def baseStart_5131016 : Nat := 118140960795 + 5131016 * 2 ^ 59
def prefixEnd_5131016 : Nat := 4983230072969 + 3 ^ 40 * 5131016 * 2
def baseEnd_5131016 : Nat := 2634677453910002110002893

theorem tailTrace_5131016 : CollatzResearch.WordTrace tailWord_5131016 prefixEnd_5131016 2634677453910002110002893 := by
  unfold tailWord_5131016
  simp only [CollatzResearch.WordTrace]
  refine ⟨93571763989606407305742451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124762351986141876407656601 93571763989606407305742451)
  ·
    refine ⟨140357645984409610958613677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93571763989606407305742451 140357645984409610958613677)
    ·
      refine ⟨52634117244153604109480129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140357645984409610958613677 52634117244153604109480129)
      ·
        refine ⟨39475587933115203082110097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52634117244153604109480129 39475587933115203082110097)
        ·
          refine ⟨29606690949836402311582573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39475587933115203082110097 29606690949836402311582573)
          ·
            refine ⟨11102509106188650866843465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29606690949836402311582573 11102509106188650866843465)
            ·
              refine ⟨8326881829641488150132599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11102509106188650866843465 8326881829641488150132599)
              ·
                refine ⟨12490322744462232225198899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8326881829641488150132599 12490322744462232225198899)
                ·
                  refine ⟨18735484116693348337798349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12490322744462232225198899 18735484116693348337798349)
                  ·
                    refine ⟨7025806543760005626674381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18735484116693348337798349 7025806543760005626674381)
                    ·
                      refine ⟨2634677453910002110002893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7025806543760005626674381 2634677453910002110002893)
                      ·
                        rfl

theorem cell23_5131016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_5131016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131016 prefixEnd_5131016 := by exact prefixLift 5131016
  have htrace : WordTrace (prefixWord ++ tailWord_5131016) baseStart_5131016 baseEnd_5131016 := by
    simpa [prefixWord, tailWord_5131016, baseEnd_5131016] using wordTrace_append hprefix tailTrace_5131016
  have hstable : (prefixWord ++ tailWord_5131016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131016).length < 2 ^ (prefixWord ++ tailWord_5131016).sum := by decide
  have hdescent : baseEnd_5131016 < baseStart_5131016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131032 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 3, 8]
def baseStart_5131032 : Nat := 118140960795 + 5131032 * 2 ^ 59
def prefixEnd_5131032 : Nat := 4983230072969 + 3 ^ 40 * 5131032 * 2
def baseEnd_5131032 : Nat := 878228556533491349134273

theorem tailTrace_5131032 : CollatzResearch.WordTrace tailWord_5131032 prefixEnd_5131032 878228556533491349134273 := by
  unfold tailWord_5131032
  simp only [CollatzResearch.WordTrace]
  refine ⟨93572055773577424672033675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124762741031436566229378233 93572055773577424672033675)
  ·
    refine ⟨140358083660366137008050513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93572055773577424672033675 140358083660366137008050513)
    ·
      refine ⟨105268562745274602756037885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140358083660366137008050513 105268562745274602756037885)
      ·
        refine ⟨39475711029477976033514207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105268562745274602756037885 39475711029477976033514207)
        ·
          refine ⟨59213566544216964050271311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39475711029477976033514207 59213566544216964050271311)
          ·
            refine ⟨88820349816325446075406967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59213566544216964050271311 88820349816325446075406967)
            ·
              refine ⟨133230524724488169113110451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88820349816325446075406967 133230524724488169113110451)
              ·
                refine ⟨199845787086732253669665677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133230524724488169113110451 199845787086732253669665677)
                ·
                  refine ⟨74942170157524595126124629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199845787086732253669665677 74942170157524595126124629)
                  ·
                    refine ⟨878228556533491349134273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74942170157524595126124629 878228556533491349134273)
                    ·
                      rfl

theorem cell23_5131032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_5131032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131032 prefixEnd_5131032 := by exact prefixLift 5131032
  have htrace : WordTrace (prefixWord ++ tailWord_5131032) baseStart_5131032 baseEnd_5131032 := by
    simpa [prefixWord, tailWord_5131032, baseEnd_5131032] using wordTrace_append hprefix tailTrace_5131032
  have hstable : (prefixWord ++ tailWord_5131032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131032).length < 2 ^ (prefixWord ++ tailWord_5131032).sum := by decide
  have hdescent : baseEnd_5131032 < baseStart_5131032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131037 : List Nat := [1, 4, 2, 4, 1, 2, 2, 1, 1, 2, 3]
def baseStart_5131037 : Nat := 118140960795 + 5131037 * 2 ^ 59
def prefixEnd_5131037 : Nat := 4983230072969 + 3 ^ 40 * 5131037 * 2
def baseEnd_5131037 : Nat := 2634688237003746527840297

theorem tailTrace_5131037 : CollatzResearch.WordTrace tailWord_5131037 prefixEnd_5131037 2634688237003746527840297 := by
  unfold tailWord_5131037
  simp only [CollatzResearch.WordTrace]
  refine ⟨187144293912136735197999365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124762862608091156798666243 187144293912136735197999365)
  ·
    refine ⟨35089555108525637849624881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187144293912136735197999365 35089555108525637849624881)
    ·
      refine ⟨26317166331394228387218661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35089555108525637849624881 26317166331394228387218661)
      ·
        refine ⟨4934468687136417822603499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26317166331394228387218661 4934468687136417822603499)
        ·
          refine ⟨7401703030704626733905249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4934468687136417822603499 7401703030704626733905249)
          ·
            refine ⟨5551277273028470050428937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7401703030704626733905249 5551277273028470050428937)
            ·
              refine ⟨4163457954771352537821703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5551277273028470050428937 4163457954771352537821703)
              ·
                refine ⟨6245186932157028806732555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4163457954771352537821703 6245186932157028806732555)
                ·
                  refine ⟨9367780398235543210098833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6245186932157028806732555 9367780398235543210098833)
                  ·
                    refine ⟨7025835298676657407574125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9367780398235543210098833 7025835298676657407574125)
                    ·
                      refine ⟨2634688237003746527840297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7025835298676657407574125 2634688237003746527840297)
                      ·
                        rfl

theorem cell23_5131037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_5131037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131037 prefixEnd_5131037 := by exact prefixLift 5131037
  have htrace : WordTrace (prefixWord ++ tailWord_5131037) baseStart_5131037 baseEnd_5131037 := by
    simpa [prefixWord, tailWord_5131037, baseEnd_5131037] using wordTrace_append hprefix tailTrace_5131037
  have hstable : (prefixWord ++ tailWord_5131037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131037).length < 2 ^ (prefixWord ++ tailWord_5131037).sum := by decide
  have hdescent : baseEnd_5131037 < baseStart_5131037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131050 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_5131050 : Nat := 118140960795 + 5131050 * 2 ^ 59
def prefixEnd_5131050 : Nat := 4983230072969 + 3 ^ 40 * 5131050 * 2
def baseEnd_5131050 : Nat := 2634694912252254976977737

theorem tailTrace_5131050 : CollatzResearch.WordTrace tailWord_5131050 prefixEnd_5131050 2634694912252254976977737 := by
  unfold tailWord_5131050
  simp only [CollatzResearch.WordTrace]
  refine ⟨46786192015272409604555651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124763178707393092278815069 46786192015272409604555651)
  ·
    refine ⟨70179288022908614406833477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46786192015272409604555651 70179288022908614406833477)
    ·
      refine ⟨13158616504295365201281277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70179288022908614406833477 13158616504295365201281277)
      ·
        refine ⟨4934481189110761950480479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13158616504295365201281277 4934481189110761950480479)
        ·
          refine ⟨7401721783666142925720719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4934481189110761950480479 7401721783666142925720719)
          ·
            refine ⟨11102582675499214388581079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7401721783666142925720719 11102582675499214388581079)
            ·
              refine ⟨16653874013248821582871619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11102582675499214388581079 16653874013248821582871619)
              ·
                refine ⟨24980811019873232374307429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16653874013248821582871619 24980811019873232374307429)
                ·
                  refine ⟨4683902066226231070182643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24980811019873232374307429 4683902066226231070182643)
                  ·
                    refine ⟨7025853099339346605273965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4683902066226231070182643 7025853099339346605273965)
                    ·
                      refine ⟨2634694912252254976977737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7025853099339346605273965 2634694912252254976977737)
                      ·
                        rfl

theorem cell23_5131050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_5131050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131050 prefixEnd_5131050 := by exact prefixLift 5131050
  have htrace : WordTrace (prefixWord ++ tailWord_5131050) baseStart_5131050 baseEnd_5131050 := by
    simpa [prefixWord, tailWord_5131050, baseEnd_5131050] using wordTrace_append hprefix tailTrace_5131050
  have hstable : (prefixWord ++ tailWord_5131050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131050).length < 2 ^ (prefixWord ++ tailWord_5131050).sum := by decide
  have hdescent : baseEnd_5131050 < baseStart_5131050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131072 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 9]
def baseStart_5131072 : Nat := 118140960795 + 5131072 * 2 ^ 59
def prefixEnd_5131072 : Nat := 4983230072969 + 3 ^ 40 * 5131072 * 2
def baseEnd_5131072 : Nat := 2634706208826653890902635

theorem tailTrace_5131072 : CollatzResearch.WordTrace tailWord_5131072 prefixEnd_5131072 2634706208826653890902635 := by
  unfold tailWord_5131072
  simp only [CollatzResearch.WordTrace]
  refine ⟨93572785233504968087761735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124763713644673290783682313 93572785233504968087761735)
  ·
    refine ⟨140359177850257452131642603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93572785233504968087761735 140359177850257452131642603)
    ·
      refine ⟨210538766775386178197463905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140359177850257452131642603 210538766775386178197463905)
      ·
        refine ⟨157904075081539633648097929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210538766775386178197463905 157904075081539633648097929)
        ·
          refine ⟨118428056311154725236073447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157904075081539633648097929 118428056311154725236073447)
          ·
            refine ⟨177642084466732087854110171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118428056311154725236073447 177642084466732087854110171)
            ·
              refine ⟨266463126700098131781165257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177642084466732087854110171 266463126700098131781165257)
              ·
                refine ⟨199847345025073598835873943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266463126700098131781165257 199847345025073598835873943)
                ·
                  refine ⟨299771017537610398253810915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 199847345025073598835873943 299771017537610398253810915)
                  ·
                    refine ⟨449656526306415597380716373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 299771017537610398253810915 449656526306415597380716373)
                    ·
                      refine ⟨2634706208826653890902635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 449656526306415597380716373 2634706208826653890902635)
                      ·
                        rfl

theorem cell23_5131072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_5131072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131072 prefixEnd_5131072 := by exact prefixLift 5131072
  have htrace : WordTrace (prefixWord ++ tailWord_5131072) baseStart_5131072 baseEnd_5131072 := by
    simpa [prefixWord, tailWord_5131072, baseEnd_5131072] using wordTrace_append hprefix tailTrace_5131072
  have hstable : (prefixWord ++ tailWord_5131072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131072).length < 2 ^ (prefixWord ++ tailWord_5131072).sum := by decide
  have hdescent : baseEnd_5131072 < baseStart_5131072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131109 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 4, 5]
def baseStart_5131109 : Nat := 118140960795 + 5131109 * 2 ^ 59
def prefixEnd_5131109 : Nat := 4983230072969 + 3 ^ 40 * 5131109 * 2
def baseEnd_5131109 : Nat := 878241735870290082046655

theorem tailTrace_5131109 : CollatzResearch.WordTrace tailWord_5131109 prefixEnd_5131109 878241735870290082046655 := by
  unfold tailWord_5131109
  simp only [CollatzResearch.WordTrace]
  refine ⟨187146919967875891494620381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124764613311917260996413587 187146919967875891494620381)
  ·
    refine ⟨70180094987953459310482643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187146919967875891494620381 70180094987953459310482643)
    ·
      refine ⟨105270142481930188965723965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70180094987953459310482643 105270142481930188965723965)
      ·
        refine ⟨39476303430723820862146487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105270142481930188965723965 39476303430723820862146487)
        ·
          refine ⟨59214455146085731293219731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39476303430723820862146487 59214455146085731293219731)
          ·
            refine ⟨88821682719128596939829597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59214455146085731293219731 88821682719128596939829597)
            ·
              refine ⟨33308131019673223852436099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88821682719128596939829597 33308131019673223852436099)
              ·
                refine ⟨49962196529509835778654149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33308131019673223852436099 49962196529509835778654149)
                ·
                  refine ⟨9367911849283094208497653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49962196529509835778654149 9367911849283094208497653)
                  ·
                    refine ⟨878241735870290082046655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9367911849283094208497653 878241735870290082046655)
                    ·
                      rfl

theorem cell23_5131109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_5131109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131109 prefixEnd_5131109 := by exact prefixLift 5131109
  have htrace : WordTrace (prefixWord ++ tailWord_5131109) baseStart_5131109 baseEnd_5131109 := by
    simpa [prefixWord, tailWord_5131109, baseEnd_5131109] using wordTrace_append hprefix tailTrace_5131109
  have hstable : (prefixWord ++ tailWord_5131109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131109).length < 2 ^ (prefixWord ++ tailWord_5131109).sum := by decide
  have hdescent : baseEnd_5131109 < baseStart_5131109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131116 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 2, 5, 2]
def baseStart_5131116 : Nat := 118140960795 + 5131116 * 2 ^ 59
def prefixEnd_5131116 : Nat := 4983230072969 + 3 ^ 40 * 5131116 * 2
def baseEnd_5131116 : Nat := 2634728801975451718752433

theorem tailTrace_5131116 : CollatzResearch.WordTrace tailWord_5131116 prefixEnd_5131116 2634728801975451718752433 := by
  unfold tailWord_5131116
  simp only [CollatzResearch.WordTrace]
  refine ⟨93573587639425265845062601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124764783519233687793416801 93573587639425265845062601)
  ·
    refine ⟨70180190729568949383796951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93573587639425265845062601 70180190729568949383796951)
    ·
      refine ⟨105270286094353424075695427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70180190729568949383796951 105270286094353424075695427)
      ·
        refine ⟨157905429141530136113543141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105270286094353424075695427 157905429141530136113543141)
        ·
          refine ⟨29607267964036900521289339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157905429141530136113543141 29607267964036900521289339)
          ·
            refine ⟨44410901946055350781934009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29607267964036900521289339 44410901946055350781934009)
            ·
              refine ⟨33308176459541513086450507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44410901946055350781934009 33308176459541513086450507)
              ·
                refine ⟨49962264689312269629675761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33308176459541513086450507 49962264689312269629675761)
                ·
                  refine ⟨37471698516984202222256821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49962264689312269629675761 37471698516984202222256821)
                  ·
                    refine ⟨3512971735967268958336577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37471698516984202222256821 3512971735967268958336577)
                    ·
                      refine ⟨2634728801975451718752433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3512971735967268958336577 2634728801975451718752433)
                      ·
                        rfl

theorem cell23_5131116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 5, 2].length) (baseStart_5131116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131116 prefixEnd_5131116 := by exact prefixLift 5131116
  have htrace : WordTrace (prefixWord ++ tailWord_5131116) baseStart_5131116 baseEnd_5131116 := by
    simpa [prefixWord, tailWord_5131116, baseEnd_5131116] using wordTrace_append hprefix tailTrace_5131116
  have hstable : (prefixWord ++ tailWord_5131116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131116).length < 2 ^ (prefixWord ++ tailWord_5131116).sum := by decide
  have hdescent : baseEnd_5131116 < baseStart_5131116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131159 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 6]
def baseStart_5131159 : Nat := 118140960795 + 5131159 * 2 ^ 59
def prefixEnd_5131159 : Nat := 4983230072969 + 3 ^ 40 * 5131159 * 2
def baseEnd_5131159 : Nat := 2634750881643595050514735

theorem tailTrace_5131159 : CollatzResearch.WordTrace tailWord_5131159 prefixEnd_5131159 2634750881643595050514735 := by
  unfold tailWord_5131159
  simp only [CollatzResearch.WordTrace]
  refine ⟨187148743617694750033940531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124765829078463166689293687 187148743617694750033940531)
  ·
    refine ⟨280723115426542125050910797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187148743617694750033940531 280723115426542125050910797)
    ·
      refine ⟨105271168284953296894091549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280723115426542125050910797 105271168284953296894091549)
      ·
        refine ⟨39476688106857486335284331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105271168284953296894091549 39476688106857486335284331)
        ·
          refine ⟨59215032160286229502926497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39476688106857486335284331 59215032160286229502926497)
          ·
            refine ⟨44411274120214672127194873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59215032160286229502926497 44411274120214672127194873)
            ·
              refine ⟨33308455590161004095396155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44411274120214672127194873 33308455590161004095396155)
              ·
                refine ⟨49962683385241506143094233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33308455590161004095396155 49962683385241506143094233)
                ·
                  refine ⟨37472012538931129607320675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49962683385241506143094233 37472012538931129607320675)
                  ·
                    refine ⟨56208018808396694410981013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37472012538931129607320675 56208018808396694410981013)
                    ·
                      refine ⟨2634750881643595050514735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56208018808396694410981013 2634750881643595050514735)
                      ·
                        rfl

theorem cell23_5131159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_5131159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131159 prefixEnd_5131159 := by exact prefixLift 5131159
  have htrace : WordTrace (prefixWord ++ tailWord_5131159) baseStart_5131159 baseEnd_5131159 := by
    simpa [prefixWord, tailWord_5131159, baseEnd_5131159] using wordTrace_append hprefix tailTrace_5131159
  have hstable : (prefixWord ++ tailWord_5131159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131159).length < 2 ^ (prefixWord ++ tailWord_5131159).sum := by decide
  have hdescent : baseEnd_5131159 < baseStart_5131159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131236 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 3, 1, 4]
def baseStart_5131236 : Nat := 118140960795 + 5131236 * 2 ^ 59
def prefixEnd_5131236 : Nat := 4983230072969 + 3 ^ 40 * 5131236 * 2
def baseEnd_5131236 : Nat := 2634790419653991249251881

theorem tailTrace_5131236 : CollatzResearch.WordTrace tailWord_5131236 prefixEnd_5131236 2634790419653991249251881 := by
  unfold tailWord_5131236
  simp only [CollatzResearch.WordTrace]
  refine ⟨93575776019207896092246781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124767701358943861456329041 93575776019207896092246781)
  ·
    refine ⟨35090916007202961034592543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93575776019207896092246781 35090916007202961034592543)
    ·
      refine ⟨52636374010804441551888815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35090916007202961034592543 52636374010804441551888815)
      ·
        refine ⟨78954561016206662327833223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52636374010804441551888815 78954561016206662327833223)
        ·
          refine ⟨118431841524309993491749835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78954561016206662327833223 118431841524309993491749835)
          ·
            refine ⟨177647762286464990237624753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118431841524309993491749835 177647762286464990237624753)
            ·
              refine ⟨133235821714848742678218565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177647762286464990237624753 133235821714848742678218565)
              ·
                refine ⟨24981716571534139252165981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133235821714848742678218565 24981716571534139252165981)
                ·
                  refine ⟨9368143714325302219562243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24981716571534139252165981 9368143714325302219562243)
                  ·
                    refine ⟨14052215571487953329343365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9368143714325302219562243 14052215571487953329343365)
                    ·
                      refine ⟨2634790419653991249251881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14052215571487953329343365 2634790419653991249251881)
                      ·
                        rfl

theorem cell23_5131236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_5131236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131236 prefixEnd_5131236 := by exact prefixLift 5131236
  have htrace : WordTrace (prefixWord ++ tailWord_5131236) baseStart_5131236 baseEnd_5131236 := by
    simpa [prefixWord, tailWord_5131236, baseEnd_5131236] using wordTrace_append hprefix tailTrace_5131236
  have hstable : (prefixWord ++ tailWord_5131236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131236).length < 2 ^ (prefixWord ++ tailWord_5131236).sum := by decide
  have hdescent : baseEnd_5131236 < baseStart_5131236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131276 : List Nat := [2, 2, 1, 2, 3, 4, 9]
def baseStart_5131276 : Nat := 118140960795 + 5131276 * 2 ^ 59
def prefixEnd_5131276 : Nat := 4983230072969 + 3 ^ 40 * 5131276 * 2
def baseEnd_5131276 : Nat := 32528530356545322132737

theorem tailTrace_5131276 : CollatzResearch.WordTrace tailWord_5131276 prefixEnd_5131276 32528530356545322132737 := by
  unfold tailWord_5131276
  simp only [CollatzResearch.WordTrace]
  refine ⟨93576505479135439507974841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124768673972180586010633121 93576505479135439507974841)
  ·
    refine ⟨70182379109351579630981131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93576505479135439507974841 70182379109351579630981131)
    ·
      refine ⟨105273568664027369446471697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70182379109351579630981131 105273568664027369446471697)
      ·
        refine ⟨78955176498020527084853773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105273568664027369446471697 78955176498020527084853773)
        ·
          refine ⟨29608191186757697656820165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78955176498020527084853773 29608191186757697656820165)
          ·
            refine ⟨5551535847517068310653781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29608191186757697656820165 5551535847517068310653781)
            ·
              refine ⟨32528530356545322132737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5551535847517068310653781 32528530356545322132737)
              ·
                rfl

theorem cell23_5131276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 9].length) (baseStart_5131276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131276 prefixEnd_5131276 := by exact prefixLift 5131276
  have htrace : WordTrace (prefixWord ++ tailWord_5131276) baseStart_5131276 baseEnd_5131276 := by
    simpa [prefixWord, tailWord_5131276, baseEnd_5131276] using wordTrace_append hprefix tailTrace_5131276
  have hstable : (prefixWord ++ tailWord_5131276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131276).length < 2 ^ (prefixWord ++ tailWord_5131276).sum := by decide
  have hdescent : baseEnd_5131276 < baseStart_5131276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131279 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 8]
def baseStart_5131279 : Nat := 118140960795 + 5131279 * 2 ^ 59
def prefixEnd_5131279 : Nat := 4983230072969 + 3 ^ 40 * 5131279 * 2
def baseEnd_5131279 : Nat := 2634812499322134581014183

theorem tailTrace_5131279 : CollatzResearch.WordTrace tailWord_5131279 prefixEnd_5131279 2634812499322134581014183 := by
  unfold tailWord_5131279
  simp only [CollatzResearch.WordTrace]
  refine ⟨187153120377260010528308891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124768746918173340352205927 187153120377260010528308891)
  ·
    refine ⟨280729680565890015792463337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187153120377260010528308891 280729680565890015792463337)
    ·
      refine ⟨210547260424417511844347503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280729680565890015792463337 210547260424417511844347503)
      ·
        refine ⟨315820890636626267766521255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210547260424417511844347503 315820890636626267766521255)
        ·
          refine ⟨473731335954939401649781883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315820890636626267766521255 473731335954939401649781883)
          ·
            refine ⟨710597003932409102474672825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473731335954939401649781883 710597003932409102474672825)
            ·
              refine ⟨532947752949306826856004619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 710597003932409102474672825 532947752949306826856004619)
              ·
                refine ⟨799421629423960240284006929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532947752949306826856004619 799421629423960240284006929)
                ·
                  refine ⟨599566222067970180213005197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 799421629423960240284006929 599566222067970180213005197)
                  ·
                    refine ⟨224837333275488817579876949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 599566222067970180213005197 224837333275488817579876949)
                    ·
                      refine ⟨2634812499322134581014183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 224837333275488817579876949 2634812499322134581014183)
                      ·
                        rfl

theorem cell23_5131279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_5131279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131279 prefixEnd_5131279 := by exact prefixLift 5131279
  have htrace : WordTrace (prefixWord ++ tailWord_5131279) baseStart_5131279 baseEnd_5131279 := by
    simpa [prefixWord, tailWord_5131279, baseEnd_5131279] using wordTrace_append hprefix tailTrace_5131279
  have hstable : (prefixWord ++ tailWord_5131279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131279).length < 2 ^ (prefixWord ++ tailWord_5131279).sum := by decide
  have hdescent : baseEnd_5131279 < baseStart_5131279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
