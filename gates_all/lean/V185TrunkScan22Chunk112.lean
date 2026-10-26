import V185TrunkScan22Chunk111

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1004414 : List Nat := [4, 2, 3, 1, 2, 1, 1, 4, 4]
def baseStart_1004414 : Nat := 118140960795 + 1004414 * 2 ^ 59
def prefixEnd_1004414 : Nat := 4983230072969 + 3 ^ 40 * 1004414 * 2
def baseEnd_1004414 : Nat := 114610479578919657623509

theorem tailTrace_1004414 : CollatzResearch.WordTrace tailWord_1004414 prefixEnd_1004414 114610479578919657623509 := by
  unfold tailWord_1004414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4579248522898386637411537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24422658788791395399528197 4579248522898386637411537)
  ·
    refine ⟨3434436392173789978058653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4579248522898386637411537 3434436392173789978058653)
    ·
      refine ⟨1287913647065171241771995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3434436392173789978058653 1287913647065171241771995)
      ·
        refine ⟨1931870470597756862657993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1287913647065171241771995 1931870470597756862657993)
        ·
          refine ⟨1448902852948317646993495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1931870470597756862657993 1448902852948317646993495)
          ·
            refine ⟨2173354279422476470490243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448902852948317646993495 2173354279422476470490243)
            ·
              refine ⟨3260031419133714705735365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2173354279422476470490243 3260031419133714705735365)
              ·
                refine ⟨611255891087571507325381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3260031419133714705735365 611255891087571507325381)
                ·
                  refine ⟨114610479578919657623509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 611255891087571507325381 114610479578919657623509)
                  ·
                    rfl

theorem cell22_1004414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_1004414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004414 prefixEnd_1004414 := by exact prefixLift 1004414
  have htrace : WordTrace (prefixWord ++ tailWord_1004414) baseStart_1004414 baseEnd_1004414 := by
    simpa [prefixWord, tailWord_1004414, baseEnd_1004414] using wordTrace_append hprefix tailTrace_1004414
  have hstable : (prefixWord ++ tailWord_1004414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004414).length < 2 ^ (prefixWord ++ tailWord_1004414).sum := by decide
  have hdescent : baseEnd_1004414 < baseStart_1004414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004444 : List Nat := [2, 2, 3, 3, 3, 1, 1, 1, 2, 4]
def baseStart_1004444 : Nat := 118140960795 + 1004444 * 2 ^ 59
def prefixEnd_1004444 : Nat := 4983230072969 + 3 ^ 40 * 1004444 * 2
def baseEnd_1004444 : Nat := 343841708349848894620435

theorem tailTrace_1004444 : CollatzResearch.WordTrace tailWord_1004444 prefixEnd_1004444 343841708349848894620435 := by
  unfold tailWord_1004444
  simp only [CollatzResearch.WordTrace]
  refine ⟨18317541186539204111442193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24423388248718938815256257 18317541186539204111442193)
  ·
    refine ⟨13738155889904403083581645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18317541186539204111442193 13738155889904403083581645)
    ·
      refine ⟨5151808458714151156343117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13738155889904403083581645 5151808458714151156343117)
      ·
        refine ⟨1931928172017806683628669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5151808458714151156343117 1931928172017806683628669)
        ·
          refine ⟨724473064506677506360751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1931928172017806683628669 724473064506677506360751)
          ·
            refine ⟨1086709596760016259541127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724473064506677506360751 1086709596760016259541127)
            ·
              refine ⟨1630064395140024389311691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086709596760016259541127 1630064395140024389311691)
              ·
                refine ⟨2445096592710036583967537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1630064395140024389311691 2445096592710036583967537)
                ·
                  refine ⟨1833822444532527437975653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2445096592710036583967537 1833822444532527437975653)
                  ·
                    refine ⟨343841708349848894620435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1833822444532527437975653 343841708349848894620435)
                    ·
                      rfl

theorem cell22_1004444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_1004444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004444 prefixEnd_1004444 := by exact prefixLift 1004444
  have htrace : WordTrace (prefixWord ++ tailWord_1004444) baseStart_1004444 baseEnd_1004444 := by
    simpa [prefixWord, tailWord_1004444, baseEnd_1004444] using wordTrace_append hprefix tailTrace_1004444
  have hstable : (prefixWord ++ tailWord_1004444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004444).length < 2 ^ (prefixWord ++ tailWord_1004444).sum := by decide
  have hdescent : baseEnd_1004444 < baseStart_1004444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004457 : List Nat := [1, 2, 1, 1, 1, 1, 8, 3, 1, 3]
def baseStart_1004457 : Nat := 118140960795 + 1004457 * 2 ^ 59
def prefixEnd_1004457 : Nat := 4983230072969 + 3 ^ 40 * 1004457 * 2
def baseEnd_1004457 : Nat := 343846158515521194045395

theorem tailTrace_1004457 : CollatzResearch.WordTrace tailWord_1004457 prefixEnd_1004457 343846158515521194045395 := by
  unfold tailWord_1004457
  simp only [CollatzResearch.WordTrace]
  refine ⟨36635556522031311443107625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24423704348020874295405083 36635556522031311443107625)
  ·
    refine ⟨27476667391523483582330719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36635556522031311443107625 27476667391523483582330719)
    ·
      refine ⟨41215001087285225373496079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27476667391523483582330719 41215001087285225373496079)
      ·
        refine ⟨61822501630927838060244119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41215001087285225373496079 61822501630927838060244119)
        ·
          refine ⟨92733752446391757090366179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61822501630927838060244119 92733752446391757090366179)
          ·
            refine ⟨139100628669587635635549269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92733752446391757090366179 139100628669587635635549269)
            ·
              refine ⟨1630085492221730105104093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 139100628669587635635549269 1630085492221730105104093)
              ·
                refine ⟨611282059583148789414035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1630085492221730105104093 611282059583148789414035)
                ·
                  refine ⟨916923089374723184121053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 611282059583148789414035 916923089374723184121053)
                  ·
                    refine ⟨343846158515521194045395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 916923089374723184121053 343846158515521194045395)
                    ·
                      rfl

theorem cell22_1004457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 1, 3].length) (baseStart_1004457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004457 prefixEnd_1004457 := by exact prefixLift 1004457
  have htrace : WordTrace (prefixWord ++ tailWord_1004457) baseStart_1004457 baseEnd_1004457 := by
    simpa [prefixWord, tailWord_1004457, baseEnd_1004457] using wordTrace_append hprefix tailTrace_1004457
  have hstable : (prefixWord ++ tailWord_1004457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004457).length < 2 ^ (prefixWord ++ tailWord_1004457).sum := by decide
  have hdescent : baseEnd_1004457 < baseStart_1004457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004493 : List Nat := [1, 6, 3, 1, 2, 1, 2, 6]
def baseStart_1004493 : Nat := 118140960795 + 1004493 * 2 ^ 59
def prefixEnd_1004493 : Nat := 4983230072969 + 3 ^ 40 * 1004493 * 2
def baseEnd_1004493 : Nat := 38206498005692122238365

theorem tailTrace_1004493 : CollatzResearch.WordTrace tailWord_1004493 prefixEnd_1004493 38206498005692122238365 := by
  unfold tailWord_1004493
  simp only [CollatzResearch.WordTrace]
  refine ⟨36636869549900889591418133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24424579699933926394278755 36636869549900889591418133)
  ·
    refine ⟨1717353260151604199597725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36636869549900889591418133 1717353260151604199597725)
    ·
      refine ⟨644007472556851574849147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1717353260151604199597725 644007472556851574849147)
      ·
        refine ⟨966011208835277362273721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644007472556851574849147 966011208835277362273721)
        ·
          refine ⟨724508406626458021705291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 966011208835277362273721 724508406626458021705291)
          ·
            refine ⟨1086762609939687032557937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724508406626458021705291 1086762609939687032557937)
            ·
              refine ⟨815071957454765274418453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1086762609939687032557937 815071957454765274418453)
              ·
                refine ⟨38206498005692122238365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 815071957454765274418453 38206498005692122238365)
                ·
                  rfl

theorem cell22_1004493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 6].length) (baseStart_1004493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004493 prefixEnd_1004493 := by exact prefixLift 1004493
  have htrace : WordTrace (prefixWord ++ tailWord_1004493) baseStart_1004493 baseEnd_1004493 := by
    simpa [prefixWord, tailWord_1004493, baseEnd_1004493] using wordTrace_append hprefix tailTrace_1004493
  have hstable : (prefixWord ++ tailWord_1004493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004493).length < 2 ^ (prefixWord ++ tailWord_1004493).sum := by decide
  have hdescent : baseEnd_1004493 < baseStart_1004493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004513 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 3, 5]
def baseStart_1004513 : Nat := 118140960795 + 1004513 * 2 ^ 59
def prefixEnd_1004513 : Nat := 4983230072969 + 3 ^ 40 * 1004513 * 2
def baseEnd_1004513 : Nat := 343865328459955714645223

theorem tailTrace_1004513 : CollatzResearch.WordTrace tailWord_1004513 prefixEnd_1004513 343865328459955714645223 := by
  unfold tailWord_1004513
  simp only [CollatzResearch.WordTrace]
  refine ⟨36637599009828433007146193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24425066006552288671430795 36637599009828433007146193)
  ·
    refine ⟨27478199257371324755359645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36637599009828433007146193 27478199257371324755359645)
    ·
      refine ⟨10304324721514246783259867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27478199257371324755359645 10304324721514246783259867)
      ·
        refine ⟨15456487082271370174889801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10304324721514246783259867 15456487082271370174889801)
        ·
          refine ⟨11592365311703527631167351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15456487082271370174889801 11592365311703527631167351)
          ·
            refine ⟨17388547967555291446751027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11592365311703527631167351 17388547967555291446751027)
            ·
              refine ⟨26082821951332937170126541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17388547967555291446751027 26082821951332937170126541)
              ·
                refine ⟨9781058231749851438797453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26082821951332937170126541 9781058231749851438797453)
                ·
                  refine ⟨3667896836906194289549045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9781058231749851438797453 3667896836906194289549045)
                  ·
                    refine ⟨343865328459955714645223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3667896836906194289549045 343865328459955714645223)
                    ·
                      rfl

theorem cell22_1004513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_1004513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004513 prefixEnd_1004513 := by exact prefixLift 1004513
  have htrace : WordTrace (prefixWord ++ tailWord_1004513) baseStart_1004513 baseEnd_1004513 := by
    simpa [prefixWord, tailWord_1004513, baseEnd_1004513] using wordTrace_append hprefix tailTrace_1004513
  have hstable : (prefixWord ++ tailWord_1004513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004513).length < 2 ^ (prefixWord ++ tailWord_1004513).sum := by decide
  have hdescent : baseEnd_1004513 < baseStart_1004513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004590 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1004590 : Nat := 118140960795 + 1004590 * 2 ^ 59
def prefixEnd_1004590 : Nat := 4983230072969 + 3 ^ 40 * 1004590 * 2
def baseEnd_1004590 : Nat := 343891687133553180469987

theorem tailTrace_1004590 : CollatzResearch.WordTrace tailWord_1004590 prefixEnd_1004590 343891687133553180469987 := by
  unfold tailWord_1004590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4580050928818684394712403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24426938287032983438466149 4580050928818684394712403)
  ·
    refine ⟨6870076393228026592068605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4580050928818684394712403 6870076393228026592068605)
    ·
      refine ⟨2576278647460509972025727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6870076393228026592068605 2576278647460509972025727)
      ·
        refine ⟨3864417971190764958038591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2576278647460509972025727 3864417971190764958038591)
        ·
          refine ⟨5796626956786147437057887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3864417971190764958038591 5796626956786147437057887)
          ·
            refine ⟨8694940435179221155586831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5796626956786147437057887 8694940435179221155586831)
            ·
              refine ⟨13042410652768831733380247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8694940435179221155586831 13042410652768831733380247)
              ·
                refine ⟨19563615979153247600070371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13042410652768831733380247 19563615979153247600070371)
                ·
                  refine ⟨29345423968729871400105557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19563615979153247600070371 29345423968729871400105557)
                  ·
                    refine ⟨343891687133553180469987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29345423968729871400105557 343891687133553180469987)
                    ·
                      rfl

theorem cell22_1004590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1004590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004590 prefixEnd_1004590 := by exact prefixLift 1004590
  have htrace : WordTrace (prefixWord ++ tailWord_1004590) baseStart_1004590 baseEnd_1004590 := by
    simpa [prefixWord, tailWord_1004590, baseEnd_1004590] using wordTrace_append hprefix tailTrace_1004590
  have hstable : (prefixWord ++ tailWord_1004590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004590).length < 2 ^ (prefixWord ++ tailWord_1004590).sum := by decide
  have hdescent : baseEnd_1004590 < baseStart_1004590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004609 : List Nat := [1, 2, 5, 1, 3, 1, 1, 2, 3, 3]
def baseStart_1004609 : Nat := 118140960795 + 1004609 * 2 ^ 59
def prefixEnd_1004609 : Nat := 4983230072969 + 3 ^ 40 * 1004609 * 2
def baseEnd_1004609 : Nat := 343898191221843464244929

theorem tailTrace_1004609 : CollatzResearch.WordTrace tailWord_1004609 prefixEnd_1004609 343898191221843464244929 := by
  unfold tailWord_1004609
  simp only [CollatzResearch.WordTrace]
  refine ⟨36641100417480641402640881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24427400278320427601760587 36641100417480641402640881)
  ·
    refine ⟨27480825313110481051980661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36641100417480641402640881 27480825313110481051980661)
    ·
      refine ⟨2576327373104107598623187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27480825313110481051980661 2576327373104107598623187)
      ·
        refine ⟨3864491059656161397934781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2576327373104107598623187 3864491059656161397934781)
        ·
          refine ⟨1449184147371060524225543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3864491059656161397934781 1449184147371060524225543)
          ·
            refine ⟨2173776221056590786338315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1449184147371060524225543 2173776221056590786338315)
            ·
              refine ⟨3260664331584886179507473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2173776221056590786338315 3260664331584886179507473)
              ·
                refine ⟨2445498248688664634630605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3260664331584886179507473 2445498248688664634630605)
                ·
                  refine ⟨917061843258249237986477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2445498248688664634630605 917061843258249237986477)
                  ·
                    refine ⟨343898191221843464244929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 917061843258249237986477 343898191221843464244929)
                    ·
                      rfl

theorem cell22_1004609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_1004609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004609 prefixEnd_1004609 := by exact prefixLift 1004609
  have htrace : WordTrace (prefixWord ++ tailWord_1004609) baseStart_1004609 baseEnd_1004609 := by
    simpa [prefixWord, tailWord_1004609, baseEnd_1004609] using wordTrace_append hprefix tailTrace_1004609
  have hstable : (prefixWord ++ tailWord_1004609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004609).length < 2 ^ (prefixWord ++ tailWord_1004609).sum := by decide
  have hdescent : baseEnd_1004609 < baseStart_1004609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004626 : List Nat := [3, 2, 2, 1, 3, 2, 2, 3, 1, 3]
def baseStart_1004626 : Nat := 118140960795 + 1004626 * 2 ^ 59
def prefixEnd_1004626 : Nat := 4983230072969 + 3 ^ 40 * 1004626 * 2
def baseEnd_1004626 : Nat := 343904010669261086569877

theorem tailTrace_1004626 : CollatzResearch.WordTrace tailWord_1004626 prefixEnd_1004626 343904010669261086569877 := by
  unfold tailWord_1004626
  simp only [CollatzResearch.WordTrace]
  refine ⟨9160430114604763326502433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24427813638946035537339821 9160430114604763326502433)
  ·
    refine ⟨6870322585953572494876825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9160430114604763326502433 6870322585953572494876825)
    ·
      refine ⟨5152741939465179371157619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6870322585953572494876825 5152741939465179371157619)
      ·
        refine ⟨7729112909197769056736429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5152741939465179371157619 7729112909197769056736429)
        ·
          refine ⟨2898417340949163396276161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7729112909197769056736429 2898417340949163396276161)
          ·
            refine ⟨2173813005711872547207121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2898417340949163396276161 2173813005711872547207121)
            ·
              refine ⟨1630359754283904410405341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2173813005711872547207121 1630359754283904410405341)
              ·
                refine ⟨611384907856464153902003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1630359754283904410405341 611384907856464153902003)
                ·
                  refine ⟨917077361784696230853005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 611384907856464153902003 917077361784696230853005)
                  ·
                    refine ⟨343904010669261086569877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 917077361784696230853005 343904010669261086569877)
                    ·
                      rfl

theorem cell22_1004626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_1004626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004626 prefixEnd_1004626 := by exact prefixLift 1004626
  have htrace : WordTrace (prefixWord ++ tailWord_1004626) baseStart_1004626 baseEnd_1004626 := by
    simpa [prefixWord, tailWord_1004626, baseEnd_1004626] using wordTrace_append hprefix tailTrace_1004626
  have hstable : (prefixWord ++ tailWord_1004626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004626).length < 2 ^ (prefixWord ++ tailWord_1004626).sum := by decide
  have hdescent : baseEnd_1004626 < baseStart_1004626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004682 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 6, 3]
def baseStart_1004682 : Nat := 118140960795 + 1004682 * 2 ^ 59
def prefixEnd_1004682 : Nat := 4983230072969 + 3 ^ 40 * 1004682 * 2
def baseEnd_1004682 : Nat := 343923180613695607169705

theorem tailTrace_1004682 : CollatzResearch.WordTrace tailWord_1004682 prefixEnd_1004682 343923180613695607169705 := by
  unfold tailWord_1004682
  simp only [CollatzResearch.WordTrace]
  refine ⟨9160940736554043717512075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24429175297477449913365533 9160940736554043717512075)
  ·
    refine ⟨13741411104831065576268113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9160940736554043717512075 13741411104831065576268113)
    ·
      refine ⟨10306058328623299182201085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13741411104831065576268113 10306058328623299182201085)
      ·
        refine ⟨3864771873233737193325407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10306058328623299182201085 3864771873233737193325407)
        ·
          refine ⟨5797157809850605789988111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3864771873233737193325407 5797157809850605789988111)
          ·
            refine ⟨8695736714775908684982167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5797157809850605789988111 8695736714775908684982167)
            ·
              refine ⟨13043605072163863027473251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8695736714775908684982167 13043605072163863027473251)
              ·
                refine ⟨19565407608245794541209877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13043605072163863027473251 19565407608245794541209877)
                ·
                  refine ⟨917128481636521619119213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19565407608245794541209877 917128481636521619119213)
                  ·
                    refine ⟨343923180613695607169705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 917128481636521619119213 343923180613695607169705)
                    ·
                      rfl

theorem cell22_1004682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_1004682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004682 prefixEnd_1004682 := by exact prefixLift 1004682
  have htrace : WordTrace (prefixWord ++ tailWord_1004682) baseStart_1004682 baseEnd_1004682 := by
    simpa [prefixWord, tailWord_1004682, baseEnd_1004682] using wordTrace_append hprefix tailTrace_1004682
  have hstable : (prefixWord ++ tailWord_1004682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004682).length < 2 ^ (prefixWord ++ tailWord_1004682).sum := by decide
  have hdescent : baseEnd_1004682 < baseStart_1004682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004695 : List Nat := [1, 1, 3, 3, 3, 1, 10]
def baseStart_1004695 : Nat := 118140960795 + 1004695 * 2 ^ 59
def prefixEnd_1004695 : Nat := 4983230072969 + 3 ^ 40 * 1004695 * 2
def baseEnd_1004695 : Nat := 12738060399235848392395

theorem tailTrace_1004695 : CollatzResearch.WordTrace tailWord_1004695 prefixEnd_1004695 12738060399235848392395 := by
  unfold tailWord_1004695
  simp only [CollatzResearch.WordTrace]
  refine ⟨36644237095169078090271539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24429491396779385393514359 36644237095169078090271539)
  ·
    refine ⟨54966355642753617135407309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36644237095169078090271539 54966355642753617135407309)
    ·
      refine ⟨20612383366032606425777741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54966355642753617135407309 20612383366032606425777741)
      ·
        refine ⟨7729643762262227409666653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20612383366032606425777741 7729643762262227409666653)
        ·
          refine ⟨2898616410848335278624995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7729643762262227409666653 2898616410848335278624995)
          ·
            refine ⟨4347924616272502917937493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2898616410848335278624995 4347924616272502917937493)
            ·
              refine ⟨12738060399235848392395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4347924616272502917937493 12738060399235848392395)
              ·
                rfl

theorem cell22_1004695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 10].length) (baseStart_1004695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004695 prefixEnd_1004695 := by exact prefixLift 1004695
  have htrace : WordTrace (prefixWord ++ tailWord_1004695) baseStart_1004695 baseEnd_1004695 := by
    simpa [prefixWord, tailWord_1004695, baseEnd_1004695] using wordTrace_append hprefix tailTrace_1004695
  have hstable : (prefixWord ++ tailWord_1004695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004695).length < 2 ^ (prefixWord ++ tailWord_1004695).sum := by decide
  have hdescent : baseEnd_1004695 < baseStart_1004695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004727 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 5, 3]
def baseStart_1004727 : Nat := 118140960795 + 1004727 * 2 ^ 59
def prefixEnd_1004727 : Nat := 4983230072969 + 3 ^ 40 * 1004727 * 2
def baseEnd_1004727 : Nat := 343938585033330489794567

theorem tailTrace_1004727 : CollatzResearch.WordTrace tailWord_1004727 prefixEnd_1004727 343938585033330489794567 := by
  unfold tailWord_1004727
  simp only [CollatzResearch.WordTrace]
  refine ⟨36645404231053147555436435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24430269487368765036957623 36645404231053147555436435)
  ·
    refine ⟨54968106346579721333154653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36645404231053147555436435 54968106346579721333154653)
    ·
      refine ⟨20613039879967395499932995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54968106346579721333154653 20613039879967395499932995)
      ·
        refine ⟨30919559819951093249899493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20613039879967395499932995 30919559819951093249899493)
        ·
          refine ⟨5797417466240829984356155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30919559819951093249899493 5797417466240829984356155)
          ·
            refine ⟨8696126199361244976534233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5797417466240829984356155 8696126199361244976534233)
            ·
              refine ⟨6522094649520933732400675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8696126199361244976534233 6522094649520933732400675)
              ·
                refine ⟨9783141974281400598601013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6522094649520933732400675 9783141974281400598601013)
                ·
                  refine ⟨917169560088881306118845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9783141974281400598601013 917169560088881306118845)
                  ·
                    refine ⟨343938585033330489794567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 917169560088881306118845 343938585033330489794567)
                    ·
                      rfl

theorem cell22_1004727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_1004727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004727 prefixEnd_1004727 := by exact prefixLift 1004727
  have htrace : WordTrace (prefixWord ++ tailWord_1004727) baseStart_1004727 baseEnd_1004727 := by
    simpa [prefixWord, tailWord_1004727, baseEnd_1004727] using wordTrace_append hprefix tailTrace_1004727
  have hstable : (prefixWord ++ tailWord_1004727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004727).length < 2 ^ (prefixWord ++ tailWord_1004727).sum := by decide
  have hdescent : baseEnd_1004727 < baseStart_1004727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004755 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 4, 5]
def baseStart_1004755 : Nat := 118140960795 + 1004755 * 2 ^ 59
def prefixEnd_1004755 : Nat := 4983230072969 + 3 ^ 40 * 1004755 * 2
def baseEnd_1004755 : Nat := 343948170005547750094481

theorem tailTrace_1004755 : CollatzResearch.WordTrace tailWord_1004755 prefixEnd_1004755 343948170005547750094481 := by
  unfold tailWord_1004755
  simp only [CollatzResearch.WordTrace]
  refine ⟨36646425474951708337455719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24430950316634472224970479 36646425474951708337455719)
  ·
    refine ⟨54969638212427562506183579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36646425474951708337455719 54969638212427562506183579)
    ·
      refine ⟨82454457318641343759275369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54969638212427562506183579 82454457318641343759275369)
      ·
        refine ⟨61840842988981007819456527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82454457318641343759275369 61840842988981007819456527)
        ·
          refine ⟨92761264483471511729184791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61840842988981007819456527 92761264483471511729184791)
          ·
            refine ⟨139141896725207267593777187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92761264483471511729184791 139141896725207267593777187)
            ·
              refine ⟨208712845087810901390665781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139141896725207267593777187 208712845087810901390665781)
              ·
                refine ⟨19566829226982272005374917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208712845087810901390665781 19566829226982272005374917)
                ·
                  refine ⟨3668780480059176001007797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19566829226982272005374917 3668780480059176001007797)
                  ·
                    refine ⟨343948170005547750094481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3668780480059176001007797 343948170005547750094481)
                    ·
                      rfl

theorem cell22_1004755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 5].length) (baseStart_1004755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004755 prefixEnd_1004755 := by exact prefixLift 1004755
  have htrace : WordTrace (prefixWord ++ tailWord_1004755) baseStart_1004755 baseEnd_1004755 := by
    simpa [prefixWord, tailWord_1004755, baseEnd_1004755] using wordTrace_append hprefix tailTrace_1004755
  have hstable : (prefixWord ++ tailWord_1004755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004755).length < 2 ^ (prefixWord ++ tailWord_1004755).sum := by decide
  have hdescent : baseEnd_1004755 < baseStart_1004755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004787 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 3, 4]
def baseStart_1004787 : Nat := 118140960795 + 1004787 * 2 ^ 59
def prefixEnd_1004787 : Nat := 4983230072969 + 3 ^ 40 * 1004787 * 2
def baseEnd_1004787 : Nat := 343959124259510333294383

theorem tailTrace_1004787 : CollatzResearch.WordTrace tailWord_1004787 prefixEnd_1004787 343959124259510333294383 := by
  unfold tailWord_1004787
  simp only [CollatzResearch.WordTrace]
  refine ⟨36647592610835777802620615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24431728407223851868413743 36647592610835777802620615)
  ·
    refine ⟨54971388916253666703930923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36647592610835777802620615 54971388916253666703930923)
    ·
      refine ⟨82457083374380500055896385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54971388916253666703930923 82457083374380500055896385)
      ·
        refine ⟨61842812530785375041922289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82457083374380500055896385 61842812530785375041922289)
        ·
          refine ⟨46382109398089031281441717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61842812530785375041922289 46382109398089031281441717)
          ·
            refine ⟨4348322756070846682635161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46382109398089031281441717 4348322756070846682635161)
            ·
              refine ⟨3261242067053135011976371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4348322756070846682635161 3261242067053135011976371)
              ·
                refine ⟨4891863100579702517964557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3261242067053135011976371 4891863100579702517964557)
                ·
                  refine ⟨1834448662717388444236709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4891863100579702517964557 1834448662717388444236709)
                  ·
                    refine ⟨343959124259510333294383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1834448662717388444236709 343959124259510333294383)
                    ·
                      rfl

theorem cell22_1004787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 4].length) (baseStart_1004787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004787 prefixEnd_1004787 := by exact prefixLift 1004787
  have htrace : WordTrace (prefixWord ++ tailWord_1004787) baseStart_1004787 baseEnd_1004787 := by
    simpa [prefixWord, tailWord_1004787, baseEnd_1004787] using wordTrace_append hprefix tailTrace_1004787
  have hstable : (prefixWord ++ tailWord_1004787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004787).length < 2 ^ (prefixWord ++ tailWord_1004787).sum := by decide
  have hdescent : baseEnd_1004787 < baseStart_1004787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004870 : List Nat := [6, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_1004870 : Nat := 118140960795 + 1004870 * 2 ^ 59
def prefixEnd_1004870 : Nat := 4983230072969 + 3 ^ 40 * 1004870 * 2
def baseEnd_1004870 : Nat := 114662512285241927823043

theorem tailTrace_1004870 : CollatzResearch.WordTrace tailWord_1004870 prefixEnd_1004870 114662512285241927823043 := by
  unfold tailWord_1004870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1145331870922971343059127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24433746579690055318594709 1145331870922971343059127)
  ·
    refine ⟨1717997806384457014588691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1145331870922971343059127 1717997806384457014588691)
    ·
      refine ⟨2576996709576685521883037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1717997806384457014588691 2576996709576685521883037)
      ·
        refine ⟨966373766091257070706139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2576996709576685521883037 966373766091257070706139)
        ·
          refine ⟨1449560649136885606059209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966373766091257070706139 1449560649136885606059209)
          ·
            refine ⟨1087170486852664204544407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1449560649136885606059209 1087170486852664204544407)
            ·
              refine ⟨1630755730278996306816611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1087170486852664204544407 1630755730278996306816611)
              ·
                refine ⟨2446133595418494460224917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1630755730278996306816611 2446133595418494460224917)
                ·
                  refine ⟨114662512285241927823043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2446133595418494460224917 114662512285241927823043)
                  ·
                    rfl

theorem cell22_1004870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_1004870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004870 prefixEnd_1004870 := by exact prefixLift 1004870
  have htrace : WordTrace (prefixWord ++ tailWord_1004870) baseStart_1004870 baseEnd_1004870 := by
    simpa [prefixWord, tailWord_1004870, baseEnd_1004870] using wordTrace_append hprefix tailTrace_1004870
  have hstable : (prefixWord ++ tailWord_1004870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004870).length < 2 ^ (prefixWord ++ tailWord_1004870).sum := by decide
  have hdescent : baseEnd_1004870 < baseStart_1004870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004954 : List Nat := [3, 1, 1, 4, 1, 1, 3, 2, 6]
def baseStart_1004954 : Nat := 118140960795 + 1004954 * 2 ^ 59
def prefixEnd_1004954 : Nat := 4983230072969 + 3 ^ 40 * 1004954 * 2
def baseEnd_1004954 : Nat := 114672097257459188122957

theorem tailTrace_1004954 : CollatzResearch.WordTrace tailWord_1004954 prefixEnd_1004954 114672097257459188122957 := by
  unfold tailWord_1004954
  simp only [CollatzResearch.WordTrace]
  refine ⟨9163420900307691330987479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24435789067487176882633277 9163420900307691330987479)
  ·
    refine ⟨13745131350461536996481219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9163420900307691330987479 13745131350461536996481219)
    ·
      refine ⟨20617697025692305494721829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13745131350461536996481219 20617697025692305494721829)
      ·
        refine ⟨3865818192317307280260343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20617697025692305494721829 3865818192317307280260343)
        ·
          refine ⟨5798727288475960920390515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3865818192317307280260343 5798727288475960920390515)
          ·
            refine ⟨8698090932713941380585773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5798727288475960920390515 8698090932713941380585773)
            ·
              refine ⟨3261784099767728017719665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8698090932713941380585773 3261784099767728017719665)
              ·
                refine ⟨2446338074825796013289749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3261784099767728017719665 2446338074825796013289749)
                ·
                  refine ⟨114672097257459188122957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2446338074825796013289749 114672097257459188122957)
                  ·
                    rfl

theorem cell22_1004954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_1004954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004954 prefixEnd_1004954 := by exact prefixLift 1004954
  have htrace : WordTrace (prefixWord ++ tailWord_1004954) baseStart_1004954 baseEnd_1004954 := by
    simpa [prefixWord, tailWord_1004954, baseEnd_1004954] using wordTrace_append hprefix tailTrace_1004954
  have hstable : (prefixWord ++ tailWord_1004954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004954).length < 2 ^ (prefixWord ++ tailWord_1004954).sum := by decide
  have hdescent : baseEnd_1004954 < baseStart_1004954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004973 : List Nat := [1, 5, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_1004973 : Nat := 118140960795 + 1004973 * 2 ^ 59
def prefixEnd_1004973 : Nat := 4983230072969 + 3 ^ 40 * 1004973 * 2
def baseEnd_1004973 : Nat := 344022795860667848143813

theorem tailTrace_1004973 : CollatzResearch.WordTrace tailWord_1004973 prefixEnd_1004973 344022795860667848143813 := by
  unfold tailWord_1004973
  simp only [CollatzResearch.WordTrace]
  refine ⟨36654376588161931568891573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24436251058774621045927715 36654376588161931568891573)
  ·
    refine ⟨3436347805140181084583585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36654376588161931568891573 3436347805140181084583585)
    ·
      refine ⟨2577260853855135813437689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3436347805140181084583585 2577260853855135813437689)
      ·
        refine ⟨1932945640391351860078267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2577260853855135813437689 1932945640391351860078267)
        ·
          refine ⟨2899418460587027790117401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1932945640391351860078267 2899418460587027790117401)
          ·
            refine ⟨2174563845440270842588051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2899418460587027790117401 2174563845440270842588051)
            ·
              refine ⟨3261845768160406263882077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174563845440270842588051 3261845768160406263882077)
              ·
                refine ⟨1223192163060152348955779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3261845768160406263882077 1223192163060152348955779)
                ·
                  refine ⟨1834788244590228523433669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223192163060152348955779 1834788244590228523433669)
                  ·
                    refine ⟨344022795860667848143813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1834788244590228523433669 344022795860667848143813)
                    ·
                      rfl

theorem cell22_1004973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_1004973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004973 prefixEnd_1004973 := by exact prefixLift 1004973
  have htrace : WordTrace (prefixWord ++ tailWord_1004973) baseStart_1004973 baseEnd_1004973 := by
    simpa [prefixWord, tailWord_1004973, baseEnd_1004973] using wordTrace_append hprefix tailTrace_1004973
  have hstable : (prefixWord ++ tailWord_1004973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004973).length < 2 ^ (prefixWord ++ tailWord_1004973).sum := by decide
  have hdescent : baseEnd_1004973 < baseStart_1004973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004984 : List Nat := [2, 1, 2, 1, 2, 2, 2, 4, 2, 4]
def baseStart_1004984 : Nat := 118140960795 + 1004984 * 2 ^ 59
def prefixEnd_1004984 : Nat := 4983230072969 + 3 ^ 40 * 1004984 * 2
def baseEnd_1004984 : Nat := 344026561385467486118779

theorem tailTrace_1004984 : CollatzResearch.WordTrace tailWord_1004984 prefixEnd_1004984 344026561385467486118779 := by
  unfold tailWord_1004984
  simp only [CollatzResearch.WordTrace]
  refine ⟨18327388895561040223771003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24436518527414720298361337 18327388895561040223771003)
  ·
    refine ⟨27491083343341560335656505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18327388895561040223771003 27491083343341560335656505)
    ·
      refine ⟨20618312507506170251742379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27491083343341560335656505 20618312507506170251742379)
      ·
        refine ⟨30927468761259255377613569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20618312507506170251742379 30927468761259255377613569)
        ·
          refine ⟨23195601570944441533210177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30927468761259255377613569 23195601570944441533210177)
          ·
            refine ⟨17396701178208331149907633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23195601570944441533210177 17396701178208331149907633)
            ·
              refine ⟨13047525883656248362430725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17396701178208331149907633 13047525883656248362430725)
              ·
                refine ⟨2446411103185546567955761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13047525883656248362430725 2446411103185546567955761)
                ·
                  refine ⟨1834808327389159925966821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2446411103185546567955761 1834808327389159925966821)
                  ·
                    refine ⟨344026561385467486118779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1834808327389159925966821 344026561385467486118779)
                    ·
                      rfl

theorem cell22_1004984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_1004984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004984 prefixEnd_1004984 := by exact prefixLift 1004984
  have htrace : WordTrace (prefixWord ++ tailWord_1004984) baseStart_1004984 baseEnd_1004984 := by
    simpa [prefixWord, tailWord_1004984, baseEnd_1004984] using wordTrace_append hprefix tailTrace_1004984
  have hstable : (prefixWord ++ tailWord_1004984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004984).length < 2 ^ (prefixWord ++ tailWord_1004984).sum := by decide
  have hdescent : baseEnd_1004984 < baseStart_1004984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004994 : List Nat := [3, 5, 2, 1, 1, 1, 3, 1, 5]
def baseStart_1004994 : Nat := 118140960795 + 1004994 * 2 ^ 59
def prefixEnd_1004994 : Nat := 4983230072969 + 3 ^ 40 * 1004994 * 2
def baseEnd_1004994 : Nat := 114676661529943597789583

theorem tailTrace_1004994 : CollatzResearch.WordTrace tailWord_1004994 prefixEnd_1004994 114676661529943597789583 := by
  unfold tailWord_1004994
  simp only [CollatzResearch.WordTrace]
  refine ⟨9163785630271463038851509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24436761680723901436937357 9163785630271463038851509)
  ·
    refine ⟨859104902837949659892329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9163785630271463038851509 859104902837949659892329)
    ·
      refine ⟨644328677128462244919247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 859104902837949659892329 644328677128462244919247)
      ·
        refine ⟨966493015692693367378871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644328677128462244919247 966493015692693367378871)
        ·
          refine ⟨1449739523539040051068307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966493015692693367378871 1449739523539040051068307)
          ·
            refine ⟨2174609285308560076602461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1449739523539040051068307 2174609285308560076602461)
            ·
              refine ⟨815478481990710028725923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2174609285308560076602461 815478481990710028725923)
              ·
                refine ⟨1223217722986065043088885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815478481990710028725923 1223217722986065043088885)
                ·
                  refine ⟨114676661529943597789583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1223217722986065043088885 114676661529943597789583)
                  ·
                    rfl

theorem cell22_1004994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_1004994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004994 prefixEnd_1004994 := by exact prefixLift 1004994
  have htrace : WordTrace (prefixWord ++ tailWord_1004994) baseStart_1004994 baseEnd_1004994 := by
    simpa [prefixWord, tailWord_1004994, baseEnd_1004994] using wordTrace_append hprefix tailTrace_1004994
  have hstable : (prefixWord ++ tailWord_1004994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004994).length < 2 ^ (prefixWord ++ tailWord_1004994).sum := by decide
  have hdescent : baseEnd_1004994 < baseStart_1004994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005048 : List Nat := [2, 1, 2, 1, 1, 7, 1, 1, 3, 3]
def baseStart_1005048 : Nat := 118140960795 + 1005048 * 2 ^ 59
def prefixEnd_1005048 : Nat := 4983230072969 + 3 ^ 40 * 1005048 * 2
def baseEnd_1005048 : Nat := 344048469893392652518583

theorem tailTrace_1005048 : CollatzResearch.WordTrace tailWord_1005048 prefixEnd_1005048 344048469893392652518583 := by
  unfold tailWord_1005048
  simp only [CollatzResearch.WordTrace]
  refine ⟨18328556031445109688935899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24438074708593479585247865 18328556031445109688935899)
  ·
    refine ⟨27492834047167664533403849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18328556031445109688935899 27492834047167664533403849)
    ·
      refine ⟨20619625535375748400052887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27492834047167664533403849 20619625535375748400052887)
      ·
        refine ⟨30929438303063622600079331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20619625535375748400052887 30929438303063622600079331)
        ·
          refine ⟨46394157454595433900118997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30929438303063622600079331 46394157454595433900118997)
          ·
            refine ⟨1087363065342080482034039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 46394157454595433900118997 1087363065342080482034039)
            ·
              refine ⟨1631044598013120723051059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1087363065342080482034039 1631044598013120723051059)
              ·
                refine ⟨2446566897019681084576589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1631044598013120723051059 2446566897019681084576589)
                ·
                  refine ⟨917462586382380406716221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2446566897019681084576589 917462586382380406716221)
                  ·
                    refine ⟨344048469893392652518583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 917462586382380406716221 344048469893392652518583)
                    ·
                      rfl

theorem cell22_1005048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_1005048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005048 prefixEnd_1005048 := by exact prefixLift 1005048
  have htrace : WordTrace (prefixWord ++ tailWord_1005048) baseStart_1005048 baseEnd_1005048 := by
    simpa [prefixWord, tailWord_1005048, baseEnd_1005048] using wordTrace_append hprefix tailTrace_1005048
  have hstable : (prefixWord ++ tailWord_1005048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005048).length < 2 ^ (prefixWord ++ tailWord_1005048).sum := by decide
  have hdescent : baseEnd_1005048 < baseStart_1005048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005054 : List Nat := [4, 2, 2, 3, 1, 2, 2, 1, 2, 3]
def baseStart_1005054 : Nat := 118140960795 + 1005054 * 2 ^ 59
def prefixEnd_1005054 : Nat := 4983230072969 + 3 ^ 40 * 1005054 * 2
def baseEnd_1005054 : Nat := 344050523816010636868565

theorem tailTrace_1005054 : CollatzResearch.WordTrace tailWord_1005054 prefixEnd_1005054 344050523816010636868565 := by
  unfold tailWord_1005054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4582166362608560300323777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24438220600578988268393477 4582166362608560300323777)
  ·
    refine ⟨3436624771956420225242833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4582166362608560300323777 3436624771956420225242833)
    ·
      refine ⟨2577468578967315168932125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3436624771956420225242833 2577468578967315168932125)
      ·
        refine ⟨966550717112743188349547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2577468578967315168932125 966550717112743188349547)
        ·
          refine ⟨1449826075669114782524321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966550717112743188349547 1449826075669114782524321)
          ·
            refine ⟨1087369556751836086893241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1449826075669114782524321 1087369556751836086893241)
            ·
              refine ⟨815527167563877065169931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1087369556751836086893241 815527167563877065169931)
              ·
                refine ⟨1223290751345815597754897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815527167563877065169931 1223290751345815597754897)
                ·
                  refine ⟨917468063509361698316173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1223290751345815597754897 917468063509361698316173)
                  ·
                    refine ⟨344050523816010636868565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 917468063509361698316173 344050523816010636868565)
                    ·
                      rfl

theorem cell22_1005054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_1005054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005054 prefixEnd_1005054 := by exact prefixLift 1005054
  have htrace : WordTrace (prefixWord ++ tailWord_1005054) baseStart_1005054 baseEnd_1005054 := by
    simpa [prefixWord, tailWord_1005054, baseEnd_1005054] using wordTrace_append hprefix tailTrace_1005054
  have hstable : (prefixWord ++ tailWord_1005054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005054).length < 2 ^ (prefixWord ++ tailWord_1005054).sum := by decide
  have hdescent : baseEnd_1005054 < baseStart_1005054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005104 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 5, 5]
def baseStart_1005104 : Nat := 118140960795 + 1005104 * 2 ^ 59
def prefixEnd_1005104 : Nat := 4983230072969 + 3 ^ 40 * 1005104 * 2
def baseEnd_1005104 : Nat := 344067639837827173118411

theorem tailTrace_1005104 : CollatzResearch.WordTrace tailWord_1005104 prefixEnd_1005104 344067639837827173118411 := by
  unfold tailWord_1005104
  simp only [CollatzResearch.WordTrace]
  refine ⟨18329577275343670470955183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24439436367124893961273577 18329577275343670470955183)
  ·
    refine ⟨27494365913015505706432775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18329577275343670470955183 27494365913015505706432775)
    ·
      refine ⟨41241548869523258559649163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27494365913015505706432775 41241548869523258559649163)
      ·
        refine ⟨61862323304284887839473745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41241548869523258559649163 61862323304284887839473745)
        ·
          refine ⟨46396742478213665879605309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61862323304284887839473745 46396742478213665879605309)
          ·
            refine ⟨17398778429330124704851991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46396742478213665879605309 17398778429330124704851991)
            ·
              refine ⟨26098167643995187057277987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17398778429330124704851991 26098167643995187057277987)
              ·
                refine ⟨39147251465992780585916981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26098167643995187057277987 39147251465992780585916981)
                ·
                  refine ⟨3670054824936823179929717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39147251465992780585916981 3670054824936823179929717)
                  ·
                    refine ⟨344067639837827173118411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3670054824936823179929717 344067639837827173118411)
                    ·
                      rfl

theorem cell22_1005104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_1005104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005104 prefixEnd_1005104 := by exact prefixLift 1005104
  have htrace : WordTrace (prefixWord ++ tailWord_1005104) baseStart_1005104 baseEnd_1005104 := by
    simpa [prefixWord, tailWord_1005104, baseEnd_1005104] using wordTrace_append hprefix tailTrace_1005104
  have hstable : (prefixWord ++ tailWord_1005104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005104).length < 2 ^ (prefixWord ++ tailWord_1005104).sum := by decide
  have hdescent : baseEnd_1005104 < baseStart_1005104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005155 : List Nat := [1, 1, 1, 5, 1, 5, 1, 2, 2, 3]
def baseStart_1005155 : Nat := 118140960795 + 1005155 * 2 ^ 59
def prefixEnd_1005155 : Nat := 4983230072969 + 3 ^ 40 * 1005155 * 2
def baseEnd_1005155 : Nat := 344085098180080040093255

theorem tailTrace_1005155 : CollatzResearch.WordTrace tailWord_1005155 prefixEnd_1005155 344085098180080040093255 := by
  unfold tailWord_1005155
  simp only [CollatzResearch.WordTrace]
  refine ⟨36661014673502576652016919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24440676449001717768011279 36661014673502576652016919)
  ·
    refine ⟨54991522010253864978025379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36661014673502576652016919 54991522010253864978025379)
    ·
      refine ⟨82487283015380797467038069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54991522010253864978025379 82487283015380797467038069)
      ·
        refine ⟨7733182782691949762534819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82487283015380797467038069 7733182782691949762534819)
        ·
          refine ⟨11599774174037924643802229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7733182782691949762534819 11599774174037924643802229)
          ·
            refine ⟨1087478828816055435356459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11599774174037924643802229 1087478828816055435356459)
            ·
              refine ⟨1631218243224083153034689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1087478828816055435356459 1631218243224083153034689)
              ·
                refine ⟨1223413682418062364776017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1631218243224083153034689 1223413682418062364776017)
                ·
                  refine ⟨917560261813546773582013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1223413682418062364776017 917560261813546773582013)
                  ·
                    refine ⟨344085098180080040093255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 917560261813546773582013 344085098180080040093255)
                    ·
                      rfl

theorem cell22_1005155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 3].length) (baseStart_1005155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005155 prefixEnd_1005155 := by exact prefixLift 1005155
  have htrace : WordTrace (prefixWord ++ tailWord_1005155) baseStart_1005155 baseEnd_1005155 := by
    simpa [prefixWord, tailWord_1005155, baseEnd_1005155] using wordTrace_append hprefix tailTrace_1005155
  have hstable : (prefixWord ++ tailWord_1005155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005155).length < 2 ^ (prefixWord ++ tailWord_1005155).sum := by decide
  have hdescent : baseEnd_1005155 < baseStart_1005155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005241 : List Nat := [1, 2, 1, 4, 1, 1, 2, 4, 6]
def baseStart_1005241 : Nat := 118140960795 + 1005241 * 2 ^ 59
def prefixEnd_1005241 : Nat := 4983230072969 + 3 ^ 40 * 1005241 * 2
def baseEnd_1005241 : Nat := 114704845912534827480997

theorem tailTrace_1005241 : CollatzResearch.WordTrace tailWord_1005241 prefixEnd_1005241 114704845912534827480997 := by
  unfold tailWord_1005241
  simp only [CollatzResearch.WordTrace]
  refine ⟨36664151351191013339647577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24442767567460675559765051 36664151351191013339647577)
  ·
    refine ⟨27498113513393260004735683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36664151351191013339647577 27498113513393260004735683)
    ·
      refine ⟨41247170270089890007103525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27498113513393260004735683 41247170270089890007103525)
      ·
        refine ⟨7733844425641854376331911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41247170270089890007103525 7733844425641854376331911)
        ·
          refine ⟨11600766638462781564497867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7733844425641854376331911 11600766638462781564497867)
          ·
            refine ⟨17401149957694172346746801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11600766638462781564497867 17401149957694172346746801)
            ·
              refine ⟨13050862468270629260060101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17401149957694172346746801 13050862468270629260060101)
              ·
                refine ⟨2447036712800742986261269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13050862468270629260060101 2447036712800742986261269)
                ·
                  refine ⟨114704845912534827480997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2447036712800742986261269 114704845912534827480997)
                  ·
                    rfl

theorem cell22_1005241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 6].length) (baseStart_1005241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005241 prefixEnd_1005241 := by exact prefixLift 1005241
  have htrace : WordTrace (prefixWord ++ tailWord_1005241) baseStart_1005241 baseEnd_1005241 := by
    simpa [prefixWord, tailWord_1005241, baseEnd_1005241] using wordTrace_append hprefix tailTrace_1005241
  have hstable : (prefixWord ++ tailWord_1005241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005241).length < 2 ^ (prefixWord ++ tailWord_1005241).sum := by decide
  have hdescent : baseEnd_1005241 < baseStart_1005241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005290 : List Nat := [3, 1, 3, 1, 1, 1, 4, 3, 2, 3]
def baseStart_1005290 : Nat := 118140960795 + 1005290 * 2 ^ 59
def prefixEnd_1005290 : Nat := 4983230072969 + 3 ^ 40 * 1005290 * 2
def baseEnd_1005290 : Nat := 344131311438984687967841

theorem tailTrace_1005290 : CollatzResearch.WordTrace tailWord_1005290 prefixEnd_1005290 344131311438984687967841 := by
  unfold tailWord_1005290
  simp only [CollatzResearch.WordTrace]
  refine ⟨9166484632003373677045331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24443959018675663138787549 9166484632003373677045331)
  ·
    refine ⟨13749726948005060515567997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9166484632003373677045331 13749726948005060515567997)
    ·
      refine ⟨5156147605501897693337999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13749726948005060515567997 5156147605501897693337999)
      ·
        refine ⟨7734221408252846540006999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5156147605501897693337999 7734221408252846540006999)
        ·
          refine ⟨11601332112379269810010499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7734221408252846540006999 11601332112379269810010499)
          ·
            refine ⟨17401998168568904715015749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11601332112379269810010499 17401998168568904715015749)
            ·
              refine ⟨3262874656606669634065453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17401998168568904715015749 3262874656606669634065453)
              ·
                refine ⟨1223577996227501112774545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3262874656606669634065453 1223577996227501112774545)
                ·
                  refine ⟨917683497170625834580909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1223577996227501112774545 917683497170625834580909)
                  ·
                    refine ⟨344131311438984687967841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 917683497170625834580909 344131311438984687967841)
                    ·
                      rfl

theorem cell22_1005290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_1005290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005290 prefixEnd_1005290 := by exact prefixLift 1005290
  have htrace : WordTrace (prefixWord ++ tailWord_1005290) baseStart_1005290 baseEnd_1005290 := by
    simpa [prefixWord, tailWord_1005290, baseEnd_1005290] using wordTrace_append hprefix tailTrace_1005290
  have hstable : (prefixWord ++ tailWord_1005290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005290).length < 2 ^ (prefixWord ++ tailWord_1005290).sum := by decide
  have hdescent : baseEnd_1005290 < baseStart_1005290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005335 : List Nat := [1, 1, 3, 4, 2, 1, 1, 3, 3, 3]
def baseStart_1005335 : Nat := 118140960795 + 1005335 * 2 ^ 59
def prefixEnd_1005335 : Nat := 4983230072969 + 3 ^ 40 * 1005335 * 2
def baseEnd_1005335 : Nat := 344146715858619570592703

theorem tailTrace_1005335 : CollatzResearch.WordTrace tailWord_1005335 prefixEnd_1005335 344146715858619570592703 := by
  unfold tailWord_1005335
  simp only [CollatzResearch.WordTrace]
  refine ⟨36667579812850467393569459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24445053208566978262379639 36667579812850467393569459)
  ·
    refine ⟨55001369719275701090354189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36667579812850467393569459 55001369719275701090354189)
    ·
      refine ⟨20625513644728387908882821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55001369719275701090354189 20625513644728387908882821)
      ·
        refine ⟨3867283808386572732915529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20625513644728387908882821 3867283808386572732915529)
        ·
          refine ⟨2900462856289929549686647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3867283808386572732915529 2900462856289929549686647)
          ·
            refine ⟨4350694284434894324529971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900462856289929549686647 4350694284434894324529971)
            ·
              refine ⟨6526041426652341486794957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4350694284434894324529971 6526041426652341486794957)
              ·
                refine ⟨2447265534994628057548109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6526041426652341486794957 2447265534994628057548109)
                ·
                  refine ⟨917724575622985521580541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2447265534994628057548109 917724575622985521580541)
                  ·
                    refine ⟨344146715858619570592703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 917724575622985521580541 344146715858619570592703)
                    ·
                      rfl

theorem cell22_1005335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_1005335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005335 prefixEnd_1005335 := by exact prefixLift 1005335
  have htrace : WordTrace (prefixWord ++ tailWord_1005335) baseStart_1005335 baseEnd_1005335 := by
    simpa [prefixWord, tailWord_1005335, baseEnd_1005335] using wordTrace_append hprefix tailTrace_1005335
  have hstable : (prefixWord ++ tailWord_1005335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005335).length < 2 ^ (prefixWord ++ tailWord_1005335).sum := by decide
  have hdescent : baseEnd_1005335 < baseStart_1005335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005382 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_1005382 : Nat := 118140960795 + 1005382 * 2 ^ 59
def prefixEnd_1005382 : Nat := 4983230072969 + 3 ^ 40 * 1005382 * 2
def baseEnd_1005382 : Nat := 114720934973042371555853

theorem tailTrace_1005382 : CollatzResearch.WordTrace tailWord_1005382 prefixEnd_1005382 114720934973042371555853 := by
  unfold tailWord_1005382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1145915438865006075641575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24446196029120129613686933 1145915438865006075641575)
  ·
    refine ⟨1718873158297509113462363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1145915438865006075641575 1718873158297509113462363)
    ·
      refine ⟨2578309737446263670193545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1718873158297509113462363 2578309737446263670193545)
      ·
        refine ⟨1933732303084697752645159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2578309737446263670193545 1933732303084697752645159)
        ·
          refine ⟨2900598454627046628967739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1933732303084697752645159 2900598454627046628967739)
          ·
            refine ⟨4350897681940569943451609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900598454627046628967739 4350897681940569943451609)
            ·
              refine ⟨3263173261455427457588707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4350897681940569943451609 3263173261455427457588707)
              ·
                refine ⟨4894759892183141186383061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3263173261455427457588707 4894759892183141186383061)
                ·
                  refine ⟨114720934973042371555853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4894759892183141186383061 114720934973042371555853)
                  ·
                    rfl

theorem cell22_1005382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_1005382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005382 prefixEnd_1005382 := by exact prefixLift 1005382
  have htrace : WordTrace (prefixWord ++ tailWord_1005382) baseStart_1005382 baseEnd_1005382 := by
    simpa [prefixWord, tailWord_1005382, baseEnd_1005382] using wordTrace_append hprefix tailTrace_1005382
  have hstable : (prefixWord ++ tailWord_1005382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005382).length < 2 ^ (prefixWord ++ tailWord_1005382).sum := by decide
  have hdescent : baseEnd_1005382 < baseStart_1005382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005399 : List Nat := [1, 1, 3, 2, 6, 1, 2, 1, 5]
def baseStart_1005399 : Nat := 118140960795 + 1005399 * 2 ^ 59
def prefixEnd_1005399 : Nat := 4983230072969 + 3 ^ 40 * 1005399 * 2
def baseEnd_1005399 : Nat := 114722874788848245664169

theorem tailTrace_1005399 : CollatzResearch.WordTrace tailWord_1005399 prefixEnd_1005399 114722874788848245664169 := by
  unfold tailWord_1005399
  simp only [CollatzResearch.WordTrace]
  refine ⟨36669914084618606323899251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24446609389745737549266167 36669914084618606323899251)
  ·
    refine ⟨55004871126927909485848877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36669914084618606323899251 55004871126927909485848877)
    ·
      refine ⟨20626826672597966057193329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55004871126927909485848877 20626826672597966057193329)
      ·
        refine ⟨15470120004448474542894997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20626826672597966057193329 15470120004448474542894997)
        ·
          refine ⟨725161875208522244198203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15470120004448474542894997 725161875208522244198203)
          ·
            refine ⟨1087742812812783366297305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725161875208522244198203 1087742812812783366297305)
            ·
              refine ⟨815807109609587524722979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1087742812812783366297305 815807109609587524722979)
              ·
                refine ⟨1223710664414381287084469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815807109609587524722979 1223710664414381287084469)
                ·
                  refine ⟨114722874788848245664169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1223710664414381287084469 114722874788848245664169)
                  ·
                    rfl

theorem cell22_1005399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 5].length) (baseStart_1005399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005399 prefixEnd_1005399 := by exact prefixLift 1005399
  have htrace : WordTrace (prefixWord ++ tailWord_1005399) baseStart_1005399 baseEnd_1005399 := by
    simpa [prefixWord, tailWord_1005399, baseEnd_1005399] using wordTrace_append hprefix tailTrace_1005399
  have hstable : (prefixWord ++ tailWord_1005399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005399).length < 2 ^ (prefixWord ++ tailWord_1005399).sum := by decide
  have hdescent : baseEnd_1005399 < baseStart_1005399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005474 : List Nat := [3, 3, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_1005474 : Nat := 118140960795 + 1005474 * 2 ^ 59
def prefixEnd_1005474 : Nat := 4983230072969 + 3 ^ 40 * 1005474 * 2
def baseEnd_1005474 : Nat := 344194298399269541367277

theorem tailTrace_1005474 : CollatzResearch.WordTrace tailWord_1005474 prefixEnd_1005474 344194298399269541367277 := by
  unfold tailWord_1005474
  simp only [CollatzResearch.WordTrace]
  refine ⟨9168162389836723533219869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24448433039564596088586317 9168162389836723533219869)
  ·
    refine ⟨3438060896188771324957451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9168162389836723533219869 3438060896188771324957451)
    ·
      refine ⟨5157091344283156987436177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3438060896188771324957451 5157091344283156987436177)
      ·
        refine ⟨3867818508212367740577133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5157091344283156987436177 3867818508212367740577133)
        ·
          refine ⟨1450431940579637902716425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3867818508212367740577133 1450431940579637902716425)
          ·
            refine ⟨1087823955434728427037319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1450431940579637902716425 1087823955434728427037319)
            ·
              refine ⟨1631735933152092640555979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1087823955434728427037319 1631735933152092640555979)
              ·
                refine ⟨2447603899728138960833969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1631735933152092640555979 2447603899728138960833969)
                ·
                  refine ⟨1835702924796104220625477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2447603899728138960833969 1835702924796104220625477)
                  ·
                    refine ⟨344194298399269541367277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1835702924796104220625477 344194298399269541367277)
                    ·
                      rfl

theorem cell22_1005474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_1005474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005474 prefixEnd_1005474 := by exact prefixLift 1005474
  have htrace : WordTrace (prefixWord ++ tailWord_1005474) baseStart_1005474 baseEnd_1005474 := by
    simpa [prefixWord, tailWord_1005474, baseEnd_1005474] using wordTrace_append hprefix tailTrace_1005474
  have hstable : (prefixWord ++ tailWord_1005474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005474).length < 2 ^ (prefixWord ++ tailWord_1005474).sum := by decide
  have hdescent : baseEnd_1005474 < baseStart_1005474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005592 : List Nat := [2, 1, 2, 3, 2, 1, 4, 1, 2, 4]
def baseStart_1005592 : Nat := 118140960795 + 1005592 * 2 ^ 59
def prefixEnd_1005592 : Nat := 4983230072969 + 3 ^ 40 * 1005592 * 2
def baseEnd_1005592 : Nat := 344234692210756566916915

theorem tailTrace_1005592 : CollatzResearch.WordTrace tailWord_1005592 prefixEnd_1005592 344234692210756566916915 := by
  unfold tailWord_1005592
  simp only [CollatzResearch.WordTrace]
  refine ⟨18338476686459700142837515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24451302248612933523783353 18338476686459700142837515)
  ·
    refine ⟨27507715029689550214256273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18338476686459700142837515 27507715029689550214256273)
    ·
      refine ⟨20630786272267162660692205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27507715029689550214256273 20630786272267162660692205)
      ·
        refine ⟨7736544852100185997759577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20630786272267162660692205 7736544852100185997759577)
        ·
          refine ⟨5802408639075139498319683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7736544852100185997759577 5802408639075139498319683)
          ·
            refine ⟨8703612958612709247479525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5802408639075139498319683 8703612958612709247479525)
            ·
              refine ⟨1631927429739882983902411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8703612958612709247479525 1631927429739882983902411)
              ·
                refine ⟨2447891144609824475853617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1631927429739882983902411 2447891144609824475853617)
                ·
                  refine ⟨1835918358457368356890213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2447891144609824475853617 1835918358457368356890213)
                  ·
                    refine ⟨344234692210756566916915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1835918358457368356890213 344234692210756566916915)
                    ·
                      rfl

theorem cell22_1005592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_1005592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005592 prefixEnd_1005592 := by exact prefixLift 1005592
  have htrace : WordTrace (prefixWord ++ tailWord_1005592) baseStart_1005592 baseEnd_1005592 := by
    simpa [prefixWord, tailWord_1005592, baseEnd_1005592] using wordTrace_append hprefix tailTrace_1005592
  have hstable : (prefixWord ++ tailWord_1005592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005592).length < 2 ^ (prefixWord ++ tailWord_1005592).sum := by decide
  have hdescent : baseEnd_1005592 < baseStart_1005592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005607 : List Nat := [1, 1, 7, 1, 2, 10]
def baseStart_1005607 : Nat := 118140960795 + 1005607 * 2 ^ 59
def prefixEnd_1005607 : Nat := 4983230072969 + 3 ^ 40 * 1005607 * 2
def baseEnd_1005607 : Nat := 4249874407621006515949

theorem tailTrace_1005607 : CollatzResearch.WordTrace tailWord_1005607 prefixEnd_1005607 4249874407621006515949 := by
  unfold tailWord_1005607
  simp only [CollatzResearch.WordTrace]
  refine ⟨36677500467865057847471075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24451666978576705231647383 36677500467865057847471075)
  ·
    refine ⟨55016250701797586771206613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36677500467865057847471075 55016250701797586771206613)
    ·
      refine ⟨1289443375823380939950155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 55016250701797586771206613 1289443375823380939950155)
      ·
        refine ⟨1934165063735071409925233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1289443375823380939950155 1934165063735071409925233)
        ·
          refine ⟨1450623797801303557443925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1934165063735071409925233 1450623797801303557443925)
          ·
            refine ⟨4249874407621006515949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1450623797801303557443925 4249874407621006515949)
            ·
              rfl

theorem cell22_1005607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 10].length) (baseStart_1005607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005607 prefixEnd_1005607 := by exact prefixLift 1005607
  have htrace : WordTrace (prefixWord ++ tailWord_1005607) baseStart_1005607 baseEnd_1005607 := by
    simpa [prefixWord, tailWord_1005607, baseEnd_1005607] using wordTrace_append hprefix tailTrace_1005607
  have hstable : (prefixWord ++ tailWord_1005607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005607).length < 2 ^ (prefixWord ++ tailWord_1005607).sum := by decide
  have hdescent : baseEnd_1005607 < baseStart_1005607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005624 : List Nat := [2, 1, 2, 1, 7, 1, 1, 7]
def baseStart_1005624 : Nat := 118140960795 + 1005624 * 2 ^ 59
def prefixEnd_1005624 : Nat := 4983230072969 + 3 ^ 40 * 1005624 * 2
def baseEnd_1005624 : Nat := 38249516273857683346313

theorem tailTrace_1005624 : CollatzResearch.WordTrace tailWord_1005624 prefixEnd_1005624 38249516273857683346313 := by
  unfold tailWord_1005624
  simp only [CollatzResearch.WordTrace]
  refine ⟨18339060254401734875419963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24452080339202313167226617 18339060254401734875419963)
  ·
    refine ⟨27508590381602602313129945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18339060254401734875419963 27508590381602602313129945)
    ·
      refine ⟨20631442786201951734847459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27508590381602602313129945 20631442786201951734847459)
      ·
        refine ⟨30947164179302927602271189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20631442786201951734847459 30947164179302927602271189)
        ·
          refine ⟨725324160452412365678231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 30947164179302927602271189 725324160452412365678231)
          ·
            refine ⟨1087986240678618548517347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725324160452412365678231 1087986240678618548517347)
            ·
              refine ⟨1631979361017927822776021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1087986240678618548517347 1631979361017927822776021)
              ·
                refine ⟨38249516273857683346313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1631979361017927822776021 38249516273857683346313)
                ·
                  rfl

theorem cell22_1005624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 7].length) (baseStart_1005624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005624 prefixEnd_1005624 := by exact prefixLift 1005624
  have htrace : WordTrace (prefixWord ++ tailWord_1005624) baseStart_1005624 baseEnd_1005624 := by
    simpa [prefixWord, tailWord_1005624, baseEnd_1005624] using wordTrace_append hprefix tailTrace_1005624
  have hstable : (prefixWord ++ tailWord_1005624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005624).length < 2 ^ (prefixWord ++ tailWord_1005624).sum := by decide
  have hdescent : baseEnd_1005624 < baseStart_1005624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005656 : List Nat := [2, 1, 2, 2, 1, 5, 2, 3, 1, 3]
def baseStart_1005656 : Nat := 118140960795 + 1005656 * 2 ^ 59
def prefixEnd_1005656 : Nat := 4983230072969 + 3 ^ 40 * 1005656 * 2
def baseEnd_1005656 : Nat := 344256600718681733316719

theorem tailTrace_1005656 : CollatzResearch.WordTrace tailWord_1005656 prefixEnd_1005656 344256600718681733316719 := by
  unfold tailWord_1005656
  simp only [CollatzResearch.WordTrace]
  refine ⟨18339643822343769608002411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24452858429791692810669881 18339643822343769608002411)
  ·
    refine ⟨27509465733515654412003617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18339643822343769608002411 27509465733515654412003617)
    ·
      refine ⟨20632099300136740809002713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27509465733515654412003617 20632099300136740809002713)
      ·
        refine ⟨15474074475102555606752035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20632099300136740809002713 15474074475102555606752035)
        ·
          refine ⟨23211111712653833410128053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15474074475102555606752035 23211111712653833410128053)
          ·
            refine ⟨2176041723061296882199505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23211111712653833410128053 2176041723061296882199505)
            ·
              refine ⟨1632031292295972661649629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2176041723061296882199505 1632031292295972661649629)
              ·
                refine ⟨612011734610989748118611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1632031292295972661649629 612011734610989748118611)
                ·
                  refine ⟨918017601916484622177917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 612011734610989748118611 918017601916484622177917)
                  ·
                    refine ⟨344256600718681733316719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 918017601916484622177917 344256600718681733316719)
                    ·
                      rfl

theorem cell22_1005656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 1, 3].length) (baseStart_1005656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005656 prefixEnd_1005656 := by exact prefixLift 1005656
  have htrace : WordTrace (prefixWord ++ tailWord_1005656) baseStart_1005656 baseEnd_1005656 := by
    simpa [prefixWord, tailWord_1005656, baseEnd_1005656] using wordTrace_append hprefix tailTrace_1005656
  have hstable : (prefixWord ++ tailWord_1005656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005656).length < 2 ^ (prefixWord ++ tailWord_1005656).sum := by decide
  have hdescent : baseEnd_1005656 < baseStart_1005656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005662 : List Nat := [4, 4, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_1005662 : Nat := 118140960795 + 1005662 * 2 ^ 59
def prefixEnd_1005662 : Nat := 4983230072969 + 3 ^ 40 * 1005662 * 2
def baseEnd_1005662 : Nat := 344258654641299717666701

theorem tailTrace_1005662 : CollatzResearch.WordTrace tailWord_1005662 prefixEnd_1005662 344258654641299717666701 := by
  unfold tailWord_1005662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4584938310333225280090405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24453004321777201493815493 4584938310333225280090405)
  ·
    refine ⟨859675933187479740016951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4584938310333225280090405 859675933187479740016951)
    ·
      refine ⟨1289513899781219610025427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 859675933187479740016951 1289513899781219610025427)
      ·
        refine ⟨1934270849671829415038141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1289513899781219610025427 1934270849671829415038141)
        ·
          refine ⟨725351568626936030639303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1934270849671829415038141 725351568626936030639303)
          ·
            refine ⟨1088027352940404045958955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725351568626936030639303 1088027352940404045958955)
            ·
              refine ⟨1632041029410606068938433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088027352940404045958955 1632041029410606068938433)
              ·
                refine ⟨1224030772057954551703825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1632041029410606068938433 1224030772057954551703825)
                ·
                  refine ⟨918023079043465913777869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1224030772057954551703825 918023079043465913777869)
                  ·
                    refine ⟨344258654641299717666701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 918023079043465913777869 344258654641299717666701)
                    ·
                      rfl

theorem cell22_1005662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_1005662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005662 prefixEnd_1005662 := by exact prefixLift 1005662
  have htrace : WordTrace (prefixWord ++ tailWord_1005662) baseStart_1005662 baseEnd_1005662 := by
    simpa [prefixWord, tailWord_1005662, baseEnd_1005662] using wordTrace_append hprefix tailTrace_1005662
  have hstable : (prefixWord ++ tailWord_1005662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005662).length < 2 ^ (prefixWord ++ tailWord_1005662).sum := by decide
  have hdescent : baseEnd_1005662 < baseStart_1005662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005669 : List Nat := [1, 3, 1, 3, 2, 4, 1, 2, 5]
def baseStart_1005669 : Nat := 118140960795 + 1005669 * 2 ^ 59
def prefixEnd_1005669 : Nat := 4983230072969 + 3 ^ 40 * 1005669 * 2
def baseEnd_1005669 : Nat := 114753683628118010913893

theorem tailTrace_1005669 : CollatzResearch.WordTrace tailWord_1005669 prefixEnd_1005669 114753683628118010913893 := by
  unfold tailWord_1005669
  simp only [CollatzResearch.WordTrace]
  refine ⟨36679761793640442436228061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24453174529093628290818707 36679761793640442436228061)
  ·
    refine ⟨13754910672615165913585523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36679761793640442436228061 13754910672615165913585523)
    ·
      refine ⟨20632366008922748870378285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13754910672615165913585523 20632366008922748870378285)
      ·
        refine ⟨7737137253346030826391857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20632366008922748870378285 7737137253346030826391857)
        ·
          refine ⟨5802852940009523119793893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7737137253346030826391857 5802852940009523119793893)
          ·
            refine ⟨1088034926251785584961355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5802852940009523119793893 1088034926251785584961355)
            ·
              refine ⟨1632052389377678377442033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088034926251785584961355 1632052389377678377442033)
              ·
                refine ⟨1224039292033258783081525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1632052389377678377442033 1224039292033258783081525)
                ·
                  refine ⟨114753683628118010913893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1224039292033258783081525 114753683628118010913893)
                  ·
                    rfl

theorem cell22_1005669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_1005669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005669 prefixEnd_1005669 := by exact prefixLift 1005669
  have htrace : WordTrace (prefixWord ++ tailWord_1005669) baseStart_1005669 baseEnd_1005669 := by
    simpa [prefixWord, tailWord_1005669, baseEnd_1005669] using wordTrace_append hprefix tailTrace_1005669
  have hstable : (prefixWord ++ tailWord_1005669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005669).length < 2 ^ (prefixWord ++ tailWord_1005669).sum := by decide
  have hdescent : baseEnd_1005669 < baseStart_1005669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005686 : List Nat := [5, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_1005686 : Nat := 118140960795 + 1005686 * 2 ^ 59
def prefixEnd_1005686 : Nat := 4983230072969 + 3 ^ 40 * 1005686 * 2
def baseEnd_1005686 : Nat := 114755623443923885022209

theorem tailTrace_1005686 : CollatzResearch.WordTrace tailWord_1005686 prefixEnd_1005686 114755623443923885022209 := by
  unfold tailWord_1005686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2292523864661178396224807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24453587889719236226397941 2292523864661178396224807)
  ·
    refine ⟨3438785796991767594337211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2292523864661178396224807 3438785796991767594337211)
    ·
      refine ⟨5158178695487651391505817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3438785796991767594337211 5158178695487651391505817)
      ·
        refine ⟨3868634021615738543629363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5158178695487651391505817 3868634021615738543629363)
        ·
          refine ⟨5802951032423607815444045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3868634021615738543629363 5802951032423607815444045)
          ·
            refine ⟨2176106637158852930791517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5802951032423607815444045 2176106637158852930791517)
            ·
              refine ⟨816039988934569849046819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2176106637158852930791517 816039988934569849046819)
              ·
                refine ⟨1224059983401854773570229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 816039988934569849046819 1224059983401854773570229)
                ·
                  refine ⟨114755623443923885022209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1224059983401854773570229 114755623443923885022209)
                  ·
                    rfl

theorem cell22_1005686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_1005686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005686 prefixEnd_1005686 := by exact prefixLift 1005686
  have htrace : WordTrace (prefixWord ++ tailWord_1005686) baseStart_1005686 baseEnd_1005686 := by
    simpa [prefixWord, tailWord_1005686, baseEnd_1005686] using wordTrace_append hprefix tailTrace_1005686
  have hstable : (prefixWord ++ tailWord_1005686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005686).length < 2 ^ (prefixWord ++ tailWord_1005686).sum := by decide
  have hdescent : baseEnd_1005686 < baseStart_1005686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005699 : List Nat := [1, 1, 1, 3, 3, 4, 2, 2, 1, 4]
def baseStart_1005699 : Nat := 118140960795 + 1005699 * 2 ^ 59
def prefixEnd_1005699 : Nat := 4983230072969 + 3 ^ 40 * 1005699 * 2
def baseEnd_1005699 : Nat := 344271320497443954491587

theorem tailTrace_1005699 : CollatzResearch.WordTrace tailWord_1005699 prefixEnd_1005699 344271320497443954491587 := by
  unfold tailWord_1005699
  simp only [CollatzResearch.WordTrace]
  refine ⟨36680855983531757559820151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24453903989021171706546767 36680855983531757559820151)
  ·
    refine ⟨55021283975297636339730227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36680855983531757559820151 55021283975297636339730227)
    ·
      refine ⟨82531925962946454509595341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55021283975297636339730227 82531925962946454509595341)
      ·
        refine ⟨30949472236104920441098253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82531925962946454509595341 30949472236104920441098253)
        ·
          refine ⟨11606052088539345165411845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30949472236104920441098253 11606052088539345165411845)
          ·
            refine ⟨2176134766601127218514721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11606052088539345165411845 2176134766601127218514721)
            ·
              refine ⟨1632101074950845413886041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2176134766601127218514721 1632101074950845413886041)
              ·
                refine ⟨1224075806213134060414531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1632101074950845413886041 1224075806213134060414531)
                ·
                  refine ⟨1836113709319701090621797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1224075806213134060414531 1836113709319701090621797)
                  ·
                    refine ⟨344271320497443954491587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1836113709319701090621797 344271320497443954491587)
                    ·
                      rfl

theorem cell22_1005699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 4].length) (baseStart_1005699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005699 prefixEnd_1005699 := by exact prefixLift 1005699
  have htrace : WordTrace (prefixWord ++ tailWord_1005699) baseStart_1005699 baseEnd_1005699 := by
    simpa [prefixWord, tailWord_1005699, baseEnd_1005699] using wordTrace_append hprefix tailTrace_1005699
  have hstable : (prefixWord ++ tailWord_1005699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005699).length < 2 ^ (prefixWord ++ tailWord_1005699).sum := by decide
  have hdescent : baseEnd_1005699 < baseStart_1005699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005712 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 6, 3]
def baseStart_1005712 : Nat := 118140960795 + 1005712 * 2 ^ 59
def prefixEnd_1005712 : Nat := 4983230072969 + 3 ^ 40 * 1005712 * 2
def baseEnd_1005712 : Nat := 344275770663116253916547

theorem tailTrace_1005712 : CollatzResearch.WordTrace tailWord_1005712 prefixEnd_1005712 344275770663116253916547 := by
  unfold tailWord_1005712
  simp only [CollatzResearch.WordTrace]
  refine ⟨18340665066242330390021695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24454220088323107186695593 18340665066242330390021695)
  ·
    refine ⟨27510997599363495585032543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18340665066242330390021695 27510997599363495585032543)
    ·
      refine ⟨41266496399045243377548815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27510997599363495585032543 41266496399045243377548815)
      ·
        refine ⟨61899744598567865066323223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41266496399045243377548815 61899744598567865066323223)
        ·
          refine ⟨92849616897851797599484835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61899744598567865066323223 92849616897851797599484835)
          ·
            refine ⟨139274425346777696399227253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92849616897851797599484835 139274425346777696399227253)
            ·
              refine ⟨13056977376260409037427555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139274425346777696399227253 13056977376260409037427555)
              ·
                refine ⟨19585466064390613556141333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13056977376260409037427555 19585466064390613556141333)
                ·
                  refine ⟨918068721768310010444125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19585466064390613556141333 918068721768310010444125)
                  ·
                    refine ⟨344275770663116253916547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 918068721768310010444125 344275770663116253916547)
                    ·
                      rfl

theorem cell22_1005712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 6, 3].length) (baseStart_1005712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005712 prefixEnd_1005712 := by exact prefixLift 1005712
  have htrace : WordTrace (prefixWord ++ tailWord_1005712) baseStart_1005712 baseEnd_1005712 := by
    simpa [prefixWord, tailWord_1005712, baseEnd_1005712] using wordTrace_append hprefix tailTrace_1005712
  have hstable : (prefixWord ++ tailWord_1005712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005712).length < 2 ^ (prefixWord ++ tailWord_1005712).sum := by decide
  have hdescent : baseEnd_1005712 < baseStart_1005712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005729 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 4, 3]
def baseStart_1005729 : Nat := 118140960795 + 1005729 * 2 ^ 59
def prefixEnd_1005729 : Nat := 4983230072969 + 3 ^ 40 * 1005729 * 2
def baseEnd_1005729 : Nat := 344281590110533876241495

theorem tailTrace_1005729 : CollatzResearch.WordTrace tailWord_1005729 prefixEnd_1005729 344281590110533876241495 := by
  unfold tailWord_1005729
  simp only [CollatzResearch.WordTrace]
  refine ⟨36681950173423072683412241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24454633448948715122274827 36681950173423072683412241)
  ·
    refine ⟨27511462630067304512559181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36681950173423072683412241 27511462630067304512559181)
    ·
      refine ⟨10316798486275239192209693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27511462630067304512559181 10316798486275239192209693)
      ·
        refine ⟨3868799432353214697078635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10316798486275239192209693 3868799432353214697078635)
        ·
          refine ⟨5803199148529822045617953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3868799432353214697078635 5803199148529822045617953)
          ·
            refine ⟨4352399361397366534213465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5803199148529822045617953 4352399361397366534213465)
            ·
              refine ⟨3264299521048024900660099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4352399361397366534213465 3264299521048024900660099)
              ·
                refine ⟨4896449281572037350990149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3264299521048024900660099 4896449281572037350990149)
                ·
                  refine ⟨918084240294757003310653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4896449281572037350990149 918084240294757003310653)
                  ·
                    refine ⟨344281590110533876241495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 918084240294757003310653 344281590110533876241495)
                    ·
                      rfl

theorem cell22_1005729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_1005729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005729 prefixEnd_1005729 := by exact prefixLift 1005729
  have htrace : WordTrace (prefixWord ++ tailWord_1005729) baseStart_1005729 baseEnd_1005729 := by
    simpa [prefixWord, tailWord_1005729, baseEnd_1005729] using wordTrace_append hprefix tailTrace_1005729
  have hstable : (prefixWord ++ tailWord_1005729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005729).length < 2 ^ (prefixWord ++ tailWord_1005729).sum := by decide
  have hdescent : baseEnd_1005729 < baseStart_1005729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005787 : List Nat := [1, 1, 1, 1, 1, 1, 1, 10, 5]
def baseStart_1005787 : Nat := 118140960795 + 1005787 * 2 ^ 59
def prefixEnd_1005787 : Nat := 4983230072969 + 3 ^ 40 * 1005787 * 2
def baseEnd_1005787 : Nat := 114767148231947019430439

theorem tailTrace_1005787 : CollatzResearch.WordTrace tailWord_1005787 prefixEnd_1005787 114767148231947019430439 := by
  unfold tailWord_1005787
  simp only [CollatzResearch.WordTrace]
  refine ⟨36684065607212948589023615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24456043738141965726015743 36684065607212948589023615)
  ·
    refine ⟨55026098410819422883535423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36684065607212948589023615 55026098410819422883535423)
    ·
      refine ⟨82539147616229134325303135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55026098410819422883535423 82539147616229134325303135)
      ·
        refine ⟨123808721424343701487954703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82539147616229134325303135 123808721424343701487954703)
        ·
          refine ⟨185713082136515552231932055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123808721424343701487954703 185713082136515552231932055)
          ·
            refine ⟨278569623204773328347898083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185713082136515552231932055 278569623204773328347898083)
            ·
              refine ⟨417854434807159992521847125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278569623204773328347898083 417854434807159992521847125)
              ·
                refine ⟨1224182914474101540591349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 417854434807159992521847125 1224182914474101540591349)
                ·
                  refine ⟨114767148231947019430439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1224182914474101540591349 114767148231947019430439)
                  ·
                    rfl

theorem cell22_1005787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 5].length) (baseStart_1005787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005787 prefixEnd_1005787 := by exact prefixLift 1005787
  have htrace : WordTrace (prefixWord ++ tailWord_1005787) baseStart_1005787 baseEnd_1005787 := by
    simpa [prefixWord, tailWord_1005787, baseEnd_1005787] using wordTrace_append hprefix tailTrace_1005787
  have hstable : (prefixWord ++ tailWord_1005787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005787).length < 2 ^ (prefixWord ++ tailWord_1005787).sum := by decide
  have hdescent : baseEnd_1005787 < baseStart_1005787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005789 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1005789 : Nat := 118140960795 + 1005789 * 2 ^ 59
def prefixEnd_1005789 : Nat := 4983230072969 + 3 ^ 40 * 1005789 * 2
def baseEnd_1005789 : Nat := 344302129336713719741311

theorem tailTrace_1005789 : CollatzResearch.WordTrace tailWord_1005789 prefixEnd_1005789 344302129336713719741311 := by
  unfold tailWord_1005789
  simp only [CollatzResearch.WordTrace]
  refine ⟨36684138553205702930596421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24456092368803801953730947 36684138553205702930596421)
  ·
    refine ⟨6878275978726069299486829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36684138553205702930596421 6878275978726069299486829)
    ·
      refine ⟨2579353492022275987307561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6878275978726069299486829 2579353492022275987307561)
      ·
        refine ⟨1934515119016706990480671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2579353492022275987307561 1934515119016706990480671)
        ·
          refine ⟨2901772678525060485721007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1934515119016706990480671 2901772678525060485721007)
          ·
            refine ⟨4352659017787590728581511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2901772678525060485721007 4352659017787590728581511)
            ·
              refine ⟨6528988526681386092872267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4352659017787590728581511 6528988526681386092872267)
              ·
                refine ⟨9793482790022079139308401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6528988526681386092872267 9793482790022079139308401)
                ·
                  refine ⟨7345112092516559354481301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9793482790022079139308401 7345112092516559354481301)
                  ·
                    refine ⟨344302129336713719741311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7345112092516559354481301 344302129336713719741311)
                    ·
                      rfl

theorem cell22_1005789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1005789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005789 prefixEnd_1005789 := by exact prefixLift 1005789
  have htrace : WordTrace (prefixWord ++ tailWord_1005789) baseStart_1005789 baseEnd_1005789 := by
    simpa [prefixWord, tailWord_1005789, baseEnd_1005789] using wordTrace_append hprefix tailTrace_1005789
  have hstable : (prefixWord ++ tailWord_1005789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005789).length < 2 ^ (prefixWord ++ tailWord_1005789).sum := by decide
  have hdescent : baseEnd_1005789 < baseStart_1005789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005881 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 4, 3]
def baseStart_1005881 : Nat := 118140960795 + 1005881 * 2 ^ 59
def prefixEnd_1005881 : Nat := 4983230072969 + 3 ^ 40 * 1005881 * 2
def baseEnd_1005881 : Nat := 344333622816856146441029

theorem tailTrace_1005881 : CollatzResearch.WordTrace tailWord_1005881 prefixEnd_1005881 344333622816856146441029 := by
  unfold tailWord_1005881
  simp only [CollatzResearch.WordTrace]
  refine ⟨36687494068872402642945497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24458329379248268428630331 36687494068872402642945497)
  ·
    refine ⟨27515620551654301982209123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36687494068872402642945497 27515620551654301982209123)
    ·
      refine ⟨41273430827481452973313685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27515620551654301982209123 41273430827481452973313685)
      ·
        refine ⟨1934692070038193108124079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41273430827481452973313685 1934692070038193108124079)
        ·
          refine ⟨2902038105057289662186119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1934692070038193108124079 2902038105057289662186119)
          ·
            refine ⟨4353057157585934493279179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2902038105057289662186119 4353057157585934493279179)
            ·
              refine ⟨6529585736378901739918769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4353057157585934493279179 6529585736378901739918769)
              ·
                refine ⟨4897189302284176304939077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6529585736378901739918769 4897189302284176304939077)
                ·
                  refine ⟨918222994178283057176077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4897189302284176304939077 918222994178283057176077)
                  ·
                    refine ⟨344333622816856146441029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 918222994178283057176077 344333622816856146441029)
                    ·
                      rfl

theorem cell22_1005881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 3].length) (baseStart_1005881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005881 prefixEnd_1005881 := by exact prefixLift 1005881
  have htrace : WordTrace (prefixWord ++ tailWord_1005881) baseStart_1005881 baseEnd_1005881 := by
    simpa [prefixWord, tailWord_1005881, baseEnd_1005881] using wordTrace_append hprefix tailTrace_1005881
  have hstable : (prefixWord ++ tailWord_1005881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005881).length < 2 ^ (prefixWord ++ tailWord_1005881).sum := by decide
  have hdescent : baseEnd_1005881 < baseStart_1005881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005956 : List Nat := [2, 3, 2, 1, 1, 2, 4, 2, 5]
def baseStart_1005956 : Nat := 118140960795 + 1005956 * 2 ^ 59
def prefixEnd_1005956 : Nat := 4983230072969 + 3 ^ 40 * 1005956 * 2
def baseEnd_1005956 : Nat := 114786432283193650271933

theorem tailTrace_1005956 : CollatzResearch.WordTrace tailWord_1005956 prefixEnd_1005956 114786432283193650271933 := by
  unfold tailWord_1005956
  simp only [CollatzResearch.WordTrace]
  refine ⟨18345114771800345225962861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24460153029067126967950481 18345114771800345225962861)
  ·
    refine ⟨6879418039425129459736073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18345114771800345225962861 6879418039425129459736073)
    ·
      refine ⟨5159563529568847094802055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6879418039425129459736073 5159563529568847094802055)
      ·
        refine ⟨7739345294353270642203083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5159563529568847094802055 7739345294353270642203083)
        ·
          refine ⟨11609017941529905963304625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7739345294353270642203083 11609017941529905963304625)
          ·
            refine ⟨8706763456147429472478469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11609017941529905963304625 8706763456147429472478469)
            ·
              refine ⟨1632518148027643026089713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8706763456147429472478469 1632518148027643026089713)
              ·
                refine ⟨1224388611020732269567285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1632518148027643026089713 1224388611020732269567285)
                ·
                  refine ⟨114786432283193650271933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1224388611020732269567285 114786432283193650271933)
                  ·
                    rfl

theorem cell22_1005956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_1005956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005956 prefixEnd_1005956 := by exact prefixLift 1005956
  have htrace : WordTrace (prefixWord ++ tailWord_1005956) baseStart_1005956 baseEnd_1005956 := by
    simpa [prefixWord, tailWord_1005956, baseEnd_1005956] using wordTrace_append hprefix tailTrace_1005956
  have hstable : (prefixWord ++ tailWord_1005956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005956).length < 2 ^ (prefixWord ++ tailWord_1005956).sum := by decide
  have hdescent : baseEnd_1005956 < baseStart_1005956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005984 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 8]
def baseStart_1005984 : Nat := 118140960795 + 1005984 * 2 ^ 59
def prefixEnd_1005984 : Nat := 4983230072969 + 3 ^ 40 * 1005984 * 2
def baseEnd_1005984 : Nat := 114789627273932737038571

theorem tailTrace_1005984 : CollatzResearch.WordTrace tailWord_1005984 prefixEnd_1005984 114789627273932737038571 := by
  unfold tailWord_1005984
  simp only [CollatzResearch.WordTrace]
  refine ⟨18345625393749625616972503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24460833858332834155963337 18345625393749625616972503)
  ·
    refine ⟨27518438090624438425458755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18345625393749625616972503 27518438090624438425458755)
    ·
      refine ⟨41277657135936657638188133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27518438090624438425458755 41277657135936657638188133)
      ·
        refine ⟨7739560712988123307160275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41277657135936657638188133 7739560712988123307160275)
        ·
          refine ⟨11609341069482184960740413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7739560712988123307160275 11609341069482184960740413)
          ·
            refine ⟨4353502901055819360277655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11609341069482184960740413 4353502901055819360277655)
            ·
              refine ⟨6530254351583729040416483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4353502901055819360277655 6530254351583729040416483)
              ·
                refine ⟨9795381527375593560624725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6530254351583729040416483 9795381527375593560624725)
                ·
                  refine ⟨114789627273932737038571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9795381527375593560624725 114789627273932737038571)
                  ·
                    rfl

theorem cell22_1005984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 8].length) (baseStart_1005984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005984 prefixEnd_1005984 := by exact prefixLift 1005984
  have htrace : WordTrace (prefixWord ++ tailWord_1005984) baseStart_1005984 baseEnd_1005984 := by
    simpa [prefixWord, tailWord_1005984, baseEnd_1005984] using wordTrace_append hprefix tailTrace_1005984
  have hstable : (prefixWord ++ tailWord_1005984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005984).length < 2 ^ (prefixWord ++ tailWord_1005984).sum := by decide
  have hdescent : baseEnd_1005984 < baseStart_1005984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005986 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_1005986 : Nat := 118140960795 + 1005986 * 2 ^ 59
def prefixEnd_1005986 : Nat := 4983230072969 + 3 ^ 40 * 1005986 * 2
def baseEnd_1005986 : Nat := 344369566462670872565707

theorem tailTrace_1005986 : CollatzResearch.WordTrace tailWord_1005986 prefixEnd_1005986 344369566462670872565707 := by
  unfold tailWord_1005986
  simp only [CollatzResearch.WordTrace]
  refine ⟨9172830933373001393879453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24460882488994670383678541 9172830933373001393879453)
  ·
    refine ⟨3439811600014875522704795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9172830933373001393879453 3439811600014875522704795)
    ·
      refine ⟨5159717400022313284057193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3439811600014875522704795 5159717400022313284057193)
      ·
        refine ⟨3869788050016734963042895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5159717400022313284057193 3869788050016734963042895)
        ·
          refine ⟨5804682075025102444564343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3869788050016734963042895 5804682075025102444564343)
          ·
            refine ⟨8707023112537653666846515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5804682075025102444564343 8707023112537653666846515)
            ·
              refine ⟨13060534668806480500269773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8707023112537653666846515 13060534668806480500269773)
              ·
                refine ⟨4897700500802430187601165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13060534668806480500269773 4897700500802430187601165)
                ·
                  refine ⟨1836637687800911320350437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4897700500802430187601165 1836637687800911320350437)
                  ·
                    refine ⟨344369566462670872565707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1836637687800911320350437 344369566462670872565707)
                    ·
                      rfl

theorem cell22_1005986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_1005986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1005986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1005986 prefixEnd_1005986 := by exact prefixLift 1005986
  have htrace : WordTrace (prefixWord ++ tailWord_1005986) baseStart_1005986 baseEnd_1005986 := by
    simpa [prefixWord, tailWord_1005986, baseEnd_1005986] using wordTrace_append hprefix tailTrace_1005986
  have hstable : (prefixWord ++ tailWord_1005986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005986).length < 2 ^ (prefixWord ++ tailWord_1005986).sum := by decide
  have hdescent : baseEnd_1005986 < baseStart_1005986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006136 : List Nat := [2, 1, 2, 1, 4, 1, 2, 3, 6]
def baseStart_1006136 : Nat := 118140960795 + 1006136 * 2 ^ 59
def prefixEnd_1006136 : Nat := 4983230072969 + 3 ^ 40 * 1006136 * 2
def baseEnd_1006136 : Nat := 114806971509373493771749

theorem tailTrace_1006136 : CollatzResearch.WordTrace tailWord_1006136 prefixEnd_1006136 114806971509373493771749 := by
  unfold tailWord_1006136
  simp only [CollatzResearch.WordTrace]
  refine ⟨18348397341474290596739131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24464529788632387462318841 18348397341474290596739131)
  ·
    refine ⟨27522596012211435895108697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18348397341474290596739131 27522596012211435895108697)
    ·
      refine ⟨20641947009158576921331523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27522596012211435895108697 20641947009158576921331523)
      ·
        refine ⟨30962920513737865381997285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20641947009158576921331523 30962920513737865381997285)
        ·
          refine ⟨5805547596325849759124491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30962920513737865381997285 5805547596325849759124491)
          ·
            refine ⟨8708321394488774638686737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5805547596325849759124491 8708321394488774638686737)
            ·
              refine ⟨6531241045866580979015053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8708321394488774638686737 6531241045866580979015053)
              ·
                refine ⟨2449215392199967867130645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6531241045866580979015053 2449215392199967867130645)
                ·
                  refine ⟨114806971509373493771749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2449215392199967867130645 114806971509373493771749)
                  ·
                    rfl

theorem cell22_1006136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 6].length) (baseStart_1006136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006136 prefixEnd_1006136 := by exact prefixLift 1006136
  have htrace : WordTrace (prefixWord ++ tailWord_1006136) baseStart_1006136 baseEnd_1006136 := by
    simpa [prefixWord, tailWord_1006136, baseEnd_1006136] using wordTrace_append hprefix tailTrace_1006136
  have hstable : (prefixWord ++ tailWord_1006136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006136).length < 2 ^ (prefixWord ++ tailWord_1006136).sum := by decide
  have hdescent : baseEnd_1006136 < baseStart_1006136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006211 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 2, 6]
def baseStart_1006211 : Nat := 118140960795 + 1006211 * 2 ^ 59
def prefixEnd_1006211 : Nat := 4983230072969 + 3 ^ 40 * 1006211 * 2
def baseEnd_1006211 : Nat := 344446588560845285690017

theorem tailTrace_1006211 : CollatzResearch.WordTrace tailWord_1006211 prefixEnd_1006211 344446588560845285690017 := by
  unfold tailWord_1006211
  simp only [CollatzResearch.WordTrace]
  refine ⟨36699530157676869002458487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24466353438451246001638991 36699530157676869002458487)
  ·
    refine ⟨55049295236515303503687731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36699530157676869002458487 55049295236515303503687731)
    ·
      refine ⟨82573942854772955255531597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55049295236515303503687731 82573942854772955255531597)
      ·
        refine ⟨30965228570539858220824349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82573942854772955255531597 30965228570539858220824349)
        ·
          refine ⟨11611960713952446832809131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30965228570539858220824349 11611960713952446832809131)
          ·
            refine ⟨17417941070928670249213697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11611960713952446832809131 17417941070928670249213697)
            ·
              refine ⟨13063455803196502686910273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17417941070928670249213697 13063455803196502686910273)
              ·
                refine ⟨9797591852397377015182705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13063455803196502686910273 9797591852397377015182705)
                ·
                  refine ⟨7348193889298032761387029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9797591852397377015182705 7348193889298032761387029)
                  ·
                    refine ⟨344446588560845285690017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7348193889298032761387029 344446588560845285690017)
                    ·
                      rfl

theorem cell22_1006211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 6].length) (baseStart_1006211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006211 prefixEnd_1006211 := by exact prefixLift 1006211
  have htrace : WordTrace (prefixWord ++ tailWord_1006211) baseStart_1006211 baseEnd_1006211 := by
    simpa [prefixWord, tailWord_1006211, baseEnd_1006211] using wordTrace_append hprefix tailTrace_1006211
  have hstable : (prefixWord ++ tailWord_1006211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006211).length < 2 ^ (prefixWord ++ tailWord_1006211).sum := by decide
  have hdescent : baseEnd_1006211 < baseStart_1006211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006256 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 2, 8]
def baseStart_1006256 : Nat := 118140960795 + 1006256 * 2 ^ 59
def prefixEnd_1006256 : Nat := 4983230072969 + 3 ^ 40 * 1006256 * 2
def baseEnd_1006256 : Nat := 344461992980480168314879

theorem tailTrace_1006256 : CollatzResearch.WordTrace tailWord_1006256 prefixEnd_1006256 344461992980480168314879 := by
  unfold tailWord_1006256
  simp only [CollatzResearch.WordTrace]
  refine ⟨18350585721256920843923311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24467447628342561125231081 18350585721256920843923311)
  ·
    refine ⟨27525878581885381265884967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18350585721256920843923311 27525878581885381265884967)
    ·
      refine ⟨41288817872828071898827451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27525878581885381265884967 41288817872828071898827451)
      ·
        refine ⟨61933226809242107848241177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41288817872828071898827451 61933226809242107848241177)
        ·
          refine ⟨46449920106931580886180883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61933226809242107848241177 46449920106931580886180883)
          ·
            refine ⟨69674880160397371329271325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46449920106931580886180883 69674880160397371329271325)
            ·
              refine ⟨26128080060149014248476747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69674880160397371329271325 26128080060149014248476747)
              ·
                refine ⟨39192120090223521372715121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26128080060149014248476747 39192120090223521372715121)
                ·
                  refine ⟨29394090067667641029536341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39192120090223521372715121 29394090067667641029536341)
                  ·
                    refine ⟨344461992980480168314879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29394090067667641029536341 344461992980480168314879)
                    ·
                      rfl

theorem cell22_1006256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_1006256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006256 prefixEnd_1006256 := by exact prefixLift 1006256
  have htrace : WordTrace (prefixWord ++ tailWord_1006256) baseStart_1006256 baseEnd_1006256 := by
    simpa [prefixWord, tailWord_1006256, baseEnd_1006256] using wordTrace_append hprefix tailTrace_1006256
  have hstable : (prefixWord ++ tailWord_1006256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006256).length < 2 ^ (prefixWord ++ tailWord_1006256).sum := by decide
  have hdescent : baseEnd_1006256 < baseStart_1006256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006320 : List Nat := [2, 1, 1, 1, 3, 1, 3, 5, 2, 3]
def baseStart_1006320 : Nat := 118140960795 + 1006320 * 2 ^ 59
def prefixEnd_1006320 : Nat := 4983230072969 + 3 ^ 40 * 1006320 * 2
def baseEnd_1006320 : Nat := 344483901488405334714683

theorem tailTrace_1006320 : CollatzResearch.WordTrace tailWord_1006320 prefixEnd_1006320 344483901488405334714683 := by
  unfold tailWord_1006320
  simp only [CollatzResearch.WordTrace]
  refine ⟨18351752857140990309088207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24469003809521320412117609 18351752857140990309088207)
  ·
    refine ⟨27527629285711485463632311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18351752857140990309088207 27527629285711485463632311)
    ·
      refine ⟨41291443928567228195448467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27527629285711485463632311 41291443928567228195448467)
      ·
        refine ⟨61937165892850842293172701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41291443928567228195448467 61937165892850842293172701)
        ·
          refine ⟨23226437209819065859939763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61937165892850842293172701 23226437209819065859939763)
          ·
            refine ⟨34839655814728598789909645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23226437209819065859939763 34839655814728598789909645)
            ·
              refine ⟨13064870930523224546216117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34839655814728598789909645 13064870930523224546216117)
              ·
                refine ⟨1224831649736552301207761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13064870930523224546216117 1224831649736552301207761)
                ·
                  refine ⟨918623737302414225905821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1224831649736552301207761 918623737302414225905821)
                  ·
                    refine ⟨344483901488405334714683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 918623737302414225905821 344483901488405334714683)
                    ·
                      rfl

theorem cell22_1006320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 2, 3].length) (baseStart_1006320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006320 prefixEnd_1006320 := by exact prefixLift 1006320
  have htrace : WordTrace (prefixWord ++ tailWord_1006320) baseStart_1006320 baseEnd_1006320 := by
    simpa [prefixWord, tailWord_1006320, baseEnd_1006320] using wordTrace_append hprefix tailTrace_1006320
  have hstable : (prefixWord ++ tailWord_1006320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006320).length < 2 ^ (prefixWord ++ tailWord_1006320).sum := by decide
  have hdescent : baseEnd_1006320 < baseStart_1006320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006354 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 4, 3]
def baseStart_1006354 : Nat := 118140960795 + 1006354 * 2 ^ 59
def prefixEnd_1006354 : Nat := 4983230072969 + 3 ^ 40 * 1006354 * 2
def baseEnd_1006354 : Nat := 344495540383240579364579

theorem tailTrace_1006354 : CollatzResearch.WordTrace tailWord_1006354 prefixEnd_1006354 344495540383240579364579 := by
  unfold tailWord_1006354
  simp only [CollatzResearch.WordTrace]
  refine ⟨9176186449039701106228529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24469830530772536283276077 9176186449039701106228529)
  ·
    refine ⟨6882139836779775829671397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9176186449039701106228529 6882139836779775829671397)
    ·
      refine ⟨1290401219396207968063387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6882139836779775829671397 1290401219396207968063387)
      ·
        refine ⟨1935601829094311952095081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1290401219396207968063387 1935601829094311952095081)
        ·
          refine ⟨1451701371820733964071311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1935601829094311952095081 1451701371820733964071311)
          ·
            refine ⟨2177552057731100946106967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1451701371820733964071311 2177552057731100946106967)
            ·
              refine ⟨3266328086596651419160451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2177552057731100946106967 3266328086596651419160451)
              ·
                refine ⟨4899492129894977128740677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3266328086596651419160451 4899492129894977128740677)
                ·
                  refine ⟨918654774355308211638877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4899492129894977128740677 918654774355308211638877)
                  ·
                    refine ⟨344495540383240579364579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 918654774355308211638877 344495540383240579364579)
                    ·
                      rfl

theorem cell22_1006354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_1006354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006354 prefixEnd_1006354 := by exact prefixLift 1006354
  have htrace : WordTrace (prefixWord ++ tailWord_1006354) baseStart_1006354 baseEnd_1006354 := by
    simpa [prefixWord, tailWord_1006354, baseEnd_1006354] using wordTrace_append hprefix tailTrace_1006354
  have hstable : (prefixWord ++ tailWord_1006354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006354).length < 2 ^ (prefixWord ++ tailWord_1006354).sum := by decide
  have hdescent : baseEnd_1006354 < baseStart_1006354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006399 : List Nat := [1, 1, 2, 2, 5, 1, 3, 3, 1, 3]
def baseStart_1006399 : Nat := 118140960795 + 1006399 * 2 ^ 59
def prefixEnd_1006399 : Nat := 4983230072969 + 3 ^ 40 * 1006399 * 2
def baseEnd_1006399 : Nat := 344510944802875461989441

theorem tailTrace_1006399 : CollatzResearch.WordTrace tailWord_1006399 prefixEnd_1006399 344510944802875461989441 := by
  unfold tailWord_1006399
  simp only [CollatzResearch.WordTrace]
  refine ⟨36706387080995777110302251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24470924720663851406868167 36706387080995777110302251)
  ·
    refine ⟨55059580621493665665453377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36706387080995777110302251 55059580621493665665453377)
    ·
      refine ⟨41294685466120249249090033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55059580621493665665453377 41294685466120249249090033)
      ·
        refine ⟨30971014099590186936817525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41294685466120249249090033 30971014099590186936817525)
        ·
          refine ⟨2903532571836580025326643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30971014099590186936817525 2903532571836580025326643)
          ·
            refine ⟨4355298857754870037989965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2903532571836580025326643 4355298857754870037989965)
            ·
              refine ⟨1633237071658076264246237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4355298857754870037989965 1633237071658076264246237)
              ·
                refine ⟨612463901871778599092339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1633237071658076264246237 612463901871778599092339)
                ·
                  refine ⟨918695852807667898638509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 612463901871778599092339 918695852807667898638509)
                  ·
                    refine ⟨344510944802875461989441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 918695852807667898638509 344510944802875461989441)
                    ·
                      rfl

theorem cell22_1006399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 1, 3].length) (baseStart_1006399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006399 prefixEnd_1006399 := by exact prefixLift 1006399
  have htrace : WordTrace (prefixWord ++ tailWord_1006399) baseStart_1006399 baseEnd_1006399 := by
    simpa [prefixWord, tailWord_1006399, baseEnd_1006399] using wordTrace_append hprefix tailTrace_1006399
  have hstable : (prefixWord ++ tailWord_1006399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006399).length < 2 ^ (prefixWord ++ tailWord_1006399).sum := by decide
  have hdescent : baseEnd_1006399 < baseStart_1006399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006455 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 6, 3]
def baseStart_1006455 : Nat := 118140960795 + 1006455 * 2 ^ 59
def prefixEnd_1006455 : Nat := 4983230072969 + 3 ^ 40 * 1006455 * 2
def baseEnd_1006455 : Nat := 344530114747309982589269

theorem tailTrace_1006455 : CollatzResearch.WordTrace tailWord_1006455 prefixEnd_1006455 344530114747309982589269 := by
  unfold tailWord_1006455
  simp only [CollatzResearch.WordTrace]
  refine ⟨36708429568792898674340819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24472286379195265782893879 36708429568792898674340819)
  ·
    refine ⟨55062644353189348011511229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36708429568792898674340819 55062644353189348011511229)
    ·
      refine ⟨20648491632446005504316711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55062644353189348011511229 20648491632446005504316711)
      ·
        refine ⟨30972737448669008256475067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20648491632446005504316711 30972737448669008256475067)
        ·
          refine ⟨46459106173003512384712601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30972737448669008256475067 46459106173003512384712601)
          ·
            refine ⟨34844329629752634288534451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46459106173003512384712601 34844329629752634288534451)
            ·
              refine ⟨52266494444628951432801677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34844329629752634288534451 52266494444628951432801677)
              ·
                refine ⟨19599935416735856787300629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52266494444628951432801677 19599935416735856787300629)
                ·
                  refine ⟨918746972659493286904717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19599935416735856787300629 918746972659493286904717)
                  ·
                    refine ⟨344530114747309982589269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 918746972659493286904717 344530114747309982589269)
                    ·
                      rfl

theorem cell22_1006455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_1006455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006455 prefixEnd_1006455 := by exact prefixLift 1006455
  have htrace : WordTrace (prefixWord ++ tailWord_1006455) baseStart_1006455 baseEnd_1006455 := by
    simpa [prefixWord, tailWord_1006455, baseEnd_1006455] using wordTrace_append hprefix tailTrace_1006455
  have hstable : (prefixWord ++ tailWord_1006455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006455).length < 2 ^ (prefixWord ++ tailWord_1006455).sum := by decide
  have hdescent : baseEnd_1006455 < baseStart_1006455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006474 : List Nat := [3, 1, 2, 4, 1, 2, 1, 4, 4]
def baseStart_1006474 : Nat := 118140960795 + 1006474 * 2 ^ 59
def prefixEnd_1006474 : Nat := 4983230072969 + 3 ^ 40 * 1006474 * 2
def baseEnd_1006474 : Nat := 114845539611866755454737

theorem tailTrace_1006474 : CollatzResearch.WordTrace tailWord_1006474 prefixEnd_1006474 114845539611866755454737 := by
  unfold tailWord_1006474
  simp only [CollatzResearch.WordTrace]
  refine ⟨9177280638931016229820619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24472748370482709946188317 9177280638931016229820619)
  ·
    refine ⟨13765920958396524344730929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9177280638931016229820619 13765920958396524344730929)
    ·
      refine ⟨10324440718797393258548197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13765920958396524344730929 10324440718797393258548197)
      ·
        refine ⟨1935832634774511235977787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10324440718797393258548197 1935832634774511235977787)
        ·
          refine ⟨2903748952161766853966681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1935832634774511235977787 2903748952161766853966681)
          ·
            refine ⟨2177811714121325140475011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2903748952161766853966681 2177811714121325140475011)
            ·
              refine ⟨3266717571181987710712517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2177811714121325140475011 3266717571181987710712517)
              ·
                refine ⟨612509544596622695758597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3266717571181987710712517 612509544596622695758597)
                ·
                  refine ⟨114845539611866755454737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 612509544596622695758597 114845539611866755454737)
                  ·
                    rfl

theorem cell22_1006474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 4].length) (baseStart_1006474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006474 prefixEnd_1006474 := by exact prefixLift 1006474
  have htrace : WordTrace (prefixWord ++ tailWord_1006474) baseStart_1006474 baseEnd_1006474 := by
    simpa [prefixWord, tailWord_1006474, baseEnd_1006474] using wordTrace_append hprefix tailTrace_1006474
  have hstable : (prefixWord ++ tailWord_1006474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006474).length < 2 ^ (prefixWord ++ tailWord_1006474).sum := by decide
  have hdescent : baseEnd_1006474 < baseStart_1006474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006485 : List Nat := [1, 3, 2, 1, 1, 4, 3, 7]
def baseStart_1006485 : Nat := 118140960795 + 1006485 * 2 ^ 59
def prefixEnd_1006485 : Nat := 4983230072969 + 3 ^ 40 * 1006485 * 2
def baseEnd_1006485 : Nat := 38282264928933322704353

theorem tailTrace_1006485 : CollatzResearch.WordTrace tailWord_1006485 prefixEnd_1006485 38282264928933322704353 := by
  unfold tailWord_1006485
  simp only [CollatzResearch.WordTrace]
  refine ⟨36709523758684213797932909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24473015839122809198621939 36709523758684213797932909)
  ·
    refine ⟨13766071409506580174224841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36709523758684213797932909 13766071409506580174224841)
    ·
      refine ⟨10324553557129935130668631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13766071409506580174224841 10324553557129935130668631)
      ·
        refine ⟨15486830335694902696002947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10324553557129935130668631 15486830335694902696002947)
        ·
          refine ⟨23230245503542354044004421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15486830335694902696002947 23230245503542354044004421)
          ·
            refine ⟨4355671031914191383250829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23230245503542354044004421 4355671031914191383250829)
            ·
              refine ⟨1633376636967821768719061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4355671031914191383250829 1633376636967821768719061)
              ·
                refine ⟨38282264928933322704353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1633376636967821768719061 38282264928933322704353)
                ·
                  rfl

theorem cell22_1006485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 7].length) (baseStart_1006485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006485 prefixEnd_1006485 := by exact prefixLift 1006485
  have htrace : WordTrace (prefixWord ++ tailWord_1006485) baseStart_1006485 baseEnd_1006485 := by
    simpa [prefixWord, tailWord_1006485, baseEnd_1006485] using wordTrace_append hprefix tailTrace_1006485
  have hstable : (prefixWord ++ tailWord_1006485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006485).length < 2 ^ (prefixWord ++ tailWord_1006485).sum := by decide
  have hdescent : baseEnd_1006485 < baseStart_1006485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006517 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 5, 3]
def baseStart_1006517 : Nat := 118140960795 + 1006517 * 2 ^ 59
def prefixEnd_1006517 : Nat := 4983230072969 + 3 ^ 40 * 1006517 * 2
def baseEnd_1006517 : Nat := 344551338614362487539079

theorem tailTrace_1006517 : CollatzResearch.WordTrace tailWord_1006517 prefixEnd_1006517 344551338614362487539079 := by
  unfold tailWord_1006517
  simp only [CollatzResearch.WordTrace]
  refine ⟨36710690894568283263097805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24473793929712188842065203 36710690894568283263097805)
  ·
    refine ⟨13766509085463106223661677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36710690894568283263097805 13766509085463106223661677)
    ·
      refine ⟨5162440907048664833873129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13766509085463106223661677 5162440907048664833873129)
      ·
        refine ⟨3871830680286498625404847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5162440907048664833873129 3871830680286498625404847)
        ·
          refine ⟨5807746020429747938107271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3871830680286498625404847 5807746020429747938107271)
          ·
            refine ⟨8711619030644621907160907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5807746020429747938107271 8711619030644621907160907)
            ·
              refine ⟨13067428545966932860741361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8711619030644621907160907 13067428545966932860741361)
              ·
                refine ⟨9800571409475199645556021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13067428545966932860741361 9800571409475199645556021)
                ·
                  refine ⟨918803569638299966770877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9800571409475199645556021 918803569638299966770877)
                  ·
                    refine ⟨344551338614362487539079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 918803569638299966770877 344551338614362487539079)
                    ·
                      rfl

theorem cell22_1006517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_1006517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006517 prefixEnd_1006517 := by exact prefixLift 1006517
  have htrace : WordTrace (prefixWord ++ tailWord_1006517) baseStart_1006517 baseEnd_1006517 := by
    simpa [prefixWord, tailWord_1006517, baseEnd_1006517] using wordTrace_append hprefix tailTrace_1006517
  have hstable : (prefixWord ++ tailWord_1006517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006517).length < 2 ^ (prefixWord ++ tailWord_1006517).sum := by decide
  have hdescent : baseEnd_1006517 < baseStart_1006517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006545 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 2, 5]
def baseStart_1006545 : Nat := 118140960795 + 1006545 * 2 ^ 59
def prefixEnd_1006545 : Nat := 4983230072969 + 3 ^ 40 * 1006545 * 2
def baseEnd_1006545 : Nat := 344560923586579747838993

theorem tailTrace_1006545 : CollatzResearch.WordTrace tailWord_1006545 prefixEnd_1006545 344560923586579747838993 := by
  unfold tailWord_1006545
  simp only [CollatzResearch.WordTrace]
  refine ⟨36711712138466844045117089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24474474758977896030078059 36711712138466844045117089)
  ·
    refine ⟨27533784103850133033837817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36711712138466844045117089 27533784103850133033837817)
    ·
      refine ⟨20650338077887599775378363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27533784103850133033837817 20650338077887599775378363)
      ·
        refine ⟨30975507116831399663067545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20650338077887599775378363 30975507116831399663067545)
        ·
          refine ⟨23231630337623549747300659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30975507116831399663067545 23231630337623549747300659)
          ·
            refine ⟨34847445506435324620950989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23231630337623549747300659 34847445506435324620950989)
            ·
              refine ⟨13067792064913246732856621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34847445506435324620950989 13067792064913246732856621)
              ·
                refine ⟨4900422024342467524821233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13067792064913246732856621 4900422024342467524821233)
                ·
                  refine ⟨3675316518256850643615925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4900422024342467524821233 3675316518256850643615925)
                  ·
                    refine ⟨344560923586579747838993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3675316518256850643615925 344560923586579747838993)
                    ·
                      rfl

theorem cell22_1006545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_1006545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006545 prefixEnd_1006545 := by exact prefixLift 1006545
  have htrace : WordTrace (prefixWord ++ tailWord_1006545) baseStart_1006545 baseEnd_1006545 := by
    simpa [prefixWord, tailWord_1006545, baseEnd_1006545] using wordTrace_append hprefix tailTrace_1006545
  have hstable : (prefixWord ++ tailWord_1006545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006545).length < 2 ^ (prefixWord ++ tailWord_1006545).sum := by decide
  have hdescent : baseEnd_1006545 < baseStart_1006545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006654 : List Nat := [4, 2, 1, 3, 1, 1, 3, 7]
def baseStart_1006654 : Nat := 118140960795 + 1006654 * 2 ^ 59
def prefixEnd_1006654 : Nat := 4983230072969 + 3 ^ 40 * 1006654 * 2
def baseEnd_1006654 : Nat := 38288692946015532984851

theorem tailTrace_1006654 : CollatzResearch.WordTrace tailWord_1006654 prefixEnd_1006654 38288692946015532984851 := by
  unfold tailWord_1006654
  simp only [CollatzResearch.WordTrace]
  refine ⟨4589460961883994457604377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24477125130047970440556677 4589460961883994457604377)
  ·
    refine ⟨3442095721412995843203283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4589460961883994457604377 3442095721412995843203283)
    ·
      refine ⟨5163143582119493764804925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3442095721412995843203283 5163143582119493764804925)
      ·
        refine ⟨1936178843294810161801847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5163143582119493764804925 1936178843294810161801847)
        ·
          refine ⟨2904268264942215242702771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1936178843294810161801847 2904268264942215242702771)
          ·
            refine ⟨4356402397413322864054157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2904268264942215242702771 4356402397413322864054157)
            ·
              refine ⟨1633650899029996074020309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4356402397413322864054157 1633650899029996074020309)
              ·
                refine ⟨38288692946015532984851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1633650899029996074020309 38288692946015532984851)
                ·
                  rfl

theorem cell22_1006654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_1006654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006654 prefixEnd_1006654 := by exact prefixLift 1006654
  have htrace : WordTrace (prefixWord ++ tailWord_1006654) baseStart_1006654 baseEnd_1006654 := by
    simpa [prefixWord, tailWord_1006654, baseEnd_1006654] using wordTrace_append hprefix tailTrace_1006654
  have hstable : (prefixWord ++ tailWord_1006654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006654).length < 2 ^ (prefixWord ++ tailWord_1006654).sum := by decide
  have hdescent : baseEnd_1006654 < baseStart_1006654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006697 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 2, 5]
def baseStart_1006697 : Nat := 118140960795 + 1006697 * 2 ^ 59
def prefixEnd_1006697 : Nat := 4983230072969 + 3 ^ 40 * 1006697 * 2
def baseEnd_1006697 : Nat := 344612956292902018038527

theorem tailTrace_1006697 : CollatzResearch.WordTrace tailWord_1006697 prefixEnd_1006697 344612956292902018038527 := by
  unfold tailWord_1006697
  simp only [CollatzResearch.WordTrace]
  refine ⟨36717256033916174004650345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24478170689277449336433563 36717256033916174004650345)
  ·
    refine ⟨27537942025437130503487759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36717256033916174004650345 27537942025437130503487759)
    ·
      refine ⟨41306913038155695755231639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27537942025437130503487759 41306913038155695755231639)
      ·
        refine ⟨61960369557233543632847459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41306913038155695755231639 61960369557233543632847459)
        ·
          refine ⟨92940554335850315449271189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61960369557233543632847459 92940554335850315449271189)
          ·
            refine ⟨4356588484492983536684587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92940554335850315449271189 4356588484492983536684587)
            ·
              refine ⟨6534882726739475305026881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4356588484492983536684587 6534882726739475305026881)
              ·
                refine ⟨4901162045054606478770161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6534882726739475305026881 4901162045054606478770161)
                ·
                  refine ⟨3675871533790954859077621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4901162045054606478770161 3675871533790954859077621)
                  ·
                    refine ⟨344612956292902018038527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3675871533790954859077621 344612956292902018038527)
                    ·
                      rfl

theorem cell22_1006697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_1006697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006697 prefixEnd_1006697 := by exact prefixLift 1006697
  have htrace : WordTrace (prefixWord ++ tailWord_1006697) baseStart_1006697 baseEnd_1006697 := by
    simpa [prefixWord, tailWord_1006697, baseEnd_1006697] using wordTrace_append hprefix tailTrace_1006697
  have hstable : (prefixWord ++ tailWord_1006697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006697).length < 2 ^ (prefixWord ++ tailWord_1006697).sum := by decide
  have hdescent : baseEnd_1006697 < baseStart_1006697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006712 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 5, 4]
def baseStart_1006712 : Nat := 118140960795 + 1006712 * 2 ^ 59
def prefixEnd_1006712 : Nat := 4983230072969 + 3 ^ 40 * 1006712 * 2
def baseEnd_1006712 : Nat := 344618091099446978913481

theorem tailTrace_1006712 : CollatzResearch.WordTrace tailWord_1006712 prefixEnd_1006712 344618091099446978913481 := by
  unfold tailWord_1006712
  simp only [CollatzResearch.WordTrace]
  refine ⟨18358901564430915783223195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24478535419241221044297593 18358901564430915783223195)
  ·
    refine ⟨27538352346646373674834793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18358901564430915783223195 27538352346646373674834793)
    ·
      refine ⟨20653764259984780256126095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27538352346646373674834793 20653764259984780256126095)
      ·
        refine ⟨30980646389977170384189143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20653764259984780256126095 30980646389977170384189143)
        ·
          refine ⟨46470969584965755576283715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30980646389977170384189143 46470969584965755576283715)
          ·
            refine ⟨69706454377448633364425573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46470969584965755576283715 69706454377448633364425573)
            ·
              refine ⟨13069960195771618755829795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69706454377448633364425573 13069960195771618755829795)
              ·
                refine ⟨19604940293657428133744693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13069960195771618755829795 19604940293657428133744693)
                ·
                  refine ⟨1837963152530383887538565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19604940293657428133744693 1837963152530383887538565)
                  ·
                    refine ⟨344618091099446978913481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1837963152530383887538565 344618091099446978913481)
                    ·
                      rfl

theorem cell22_1006712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_1006712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006712 prefixEnd_1006712 := by exact prefixLift 1006712
  have htrace : WordTrace (prefixWord ++ tailWord_1006712) baseStart_1006712 baseEnd_1006712 := by
    simpa [prefixWord, tailWord_1006712, baseEnd_1006712] using wordTrace_append hprefix tailTrace_1006712
  have hstable : (prefixWord ++ tailWord_1006712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006712).length < 2 ^ (prefixWord ++ tailWord_1006712).sum := by decide
  have hdescent : baseEnd_1006712 < baseStart_1006712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006729 : List Nat := [1, 2, 1, 1, 4, 3, 1, 4, 1, 4]
def baseStart_1006729 : Nat := 118140960795 + 1006729 * 2 ^ 59
def prefixEnd_1006729 : Nat := 4983230072969 + 3 ^ 40 * 1006729 * 2
def baseEnd_1006729 : Nat := 344623910546864601238429

theorem tailTrace_1006729 : CollatzResearch.WordTrace tailWord_1006729 prefixEnd_1006729 344623910546864601238429 := by
  unfold tailWord_1006729
  simp only [CollatzResearch.WordTrace]
  refine ⟨36718423169800243469815241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24478948779866828979876827 36718423169800243469815241)
  ·
    refine ⟨27538817377350182602361431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36718423169800243469815241 27538817377350182602361431)
    ·
      refine ⟨41308226066025273903542147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27538817377350182602361431 41308226066025273903542147)
      ·
        refine ⟨61962339099037910855313221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41308226066025273903542147 61962339099037910855313221)
        ·
          refine ⟨11617938581069608285371229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61962339099037910855313221 11617938581069608285371229)
          ·
            refine ⟨4356726967901103107014211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11617938581069608285371229 4356726967901103107014211)
            ·
              refine ⟨6535090451851654660521317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4356726967901103107014211 6535090451851654660521317)
              ·
                refine ⟨1225329459722185248847747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6535090451851654660521317 1225329459722185248847747)
                ·
                  refine ⟨1837994189583277873271621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225329459722185248847747 1837994189583277873271621)
                  ·
                    refine ⟨344623910546864601238429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1837994189583277873271621 344623910546864601238429)
                    ·
                      rfl

theorem cell22_1006729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 4].length) (baseStart_1006729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006729 prefixEnd_1006729 := by exact prefixLift 1006729
  have htrace : WordTrace (prefixWord ++ tailWord_1006729) baseStart_1006729 baseEnd_1006729 := by
    simpa [prefixWord, tailWord_1006729, baseEnd_1006729] using wordTrace_append hprefix tailTrace_1006729
  have hstable : (prefixWord ++ tailWord_1006729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006729).length < 2 ^ (prefixWord ++ tailWord_1006729).sum := by decide
  have hdescent : baseEnd_1006729 < baseStart_1006729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006746 : List Nat := [3, 1, 1, 5, 1, 1, 2, 3, 1, 4]
def baseStart_1006746 : Nat := 118140960795 + 1006746 * 2 ^ 59
def prefixEnd_1006746 : Nat := 4983230072969 + 3 ^ 40 * 1006746 * 2
def baseEnd_1006746 : Nat := 344629729994282223563377

theorem tailTrace_1006746 : CollatzResearch.WordTrace tailWord_1006746 prefixEnd_1006746 344629729994282223563377 := by
  unfold tailWord_1006746
  simp only [CollatzResearch.WordTrace]
  refine ⟨9179760802684663843296023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24479362140492436915456061 9179760802684663843296023)
  ·
    refine ⟨13769641204026995764944035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9179760802684663843296023 13769641204026995764944035)
    ·
      refine ⟨20654461806040493647416053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13769641204026995764944035 20654461806040493647416053)
      ·
        refine ⟨1936355794316296279445255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20654461806040493647416053 1936355794316296279445255)
        ·
          refine ⟨2904533691474444419167883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1936355794316296279445255 2904533691474444419167883)
          ·
            refine ⟨4356800537211666628751825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2904533691474444419167883 4356800537211666628751825)
            ·
              refine ⟨3267600402908749971563869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4356800537211666628751825 3267600402908749971563869)
              ·
                refine ⟨1225350151090781239336451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3267600402908749971563869 1225350151090781239336451)
                ·
                  refine ⟨1838025226636171859004677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225350151090781239336451 1838025226636171859004677)
                  ·
                    refine ⟨344629729994282223563377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1838025226636171859004677 344629729994282223563377)
                    ·
                      rfl

theorem cell22_1006746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_1006746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006746 prefixEnd_1006746 := by exact prefixLift 1006746
  have htrace : WordTrace (prefixWord ++ tailWord_1006746) baseStart_1006746 baseEnd_1006746 := by
    simpa [prefixWord, tailWord_1006746, baseEnd_1006746] using wordTrace_append hprefix tailTrace_1006746
  have hstable : (prefixWord ++ tailWord_1006746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006746).length < 2 ^ (prefixWord ++ tailWord_1006746).sum := by decide
  have hdescent : baseEnd_1006746 < baseStart_1006746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006797 : List Nat := [1, 6, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_1006797 : Nat := 118140960795 + 1006797 * 2 ^ 59
def prefixEnd_1006797 : Nat := 4983230072969 + 3 ^ 40 * 1006797 * 2
def baseEnd_1006797 : Nat := 344647188336535090538221

theorem tailTrace_1006797 : CollatzResearch.WordTrace tailWord_1006797 prefixEnd_1006797 344647188336535090538221 := by
  unfold tailWord_1006797
  simp only [CollatzResearch.WordTrace]
  refine ⟨36720903333553891083290645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24480602222369260722193763 36720903333553891083290645)
  ·
    refine ⟨1721292343760338644529249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36720903333553891083290645 1721292343760338644529249)
    ·
      refine ⟨1290969257820253983396937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1721292343760338644529249 1290969257820253983396937)
      ·
        refine ⟨968226943365190487547703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1290969257820253983396937 968226943365190487547703)
        ·
          refine ⟨1452340415047785731321555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968226943365190487547703 1452340415047785731321555)
          ·
            refine ⟨2178510622571678596982333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452340415047785731321555 2178510622571678596982333)
            ·
              refine ⟨816941483464379473868375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2178510622571678596982333 816941483464379473868375)
              ·
                refine ⟨1225412225196569210802563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 816941483464379473868375 1225412225196569210802563)
                ·
                  refine ⟨1838118337794853816203845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225412225196569210802563 1838118337794853816203845)
                  ·
                    refine ⟨344647188336535090538221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1838118337794853816203845 344647188336535090538221)
                    ·
                      rfl

theorem cell22_1006797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_1006797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006797 prefixEnd_1006797 := by exact prefixLift 1006797
  have htrace : WordTrace (prefixWord ++ tailWord_1006797) baseStart_1006797 baseEnd_1006797 := by
    simpa [prefixWord, tailWord_1006797, baseEnd_1006797] using wordTrace_append hprefix tailTrace_1006797
  have hstable : (prefixWord ++ tailWord_1006797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006797).length < 2 ^ (prefixWord ++ tailWord_1006797).sum := by decide
  have hdescent : baseEnd_1006797 < baseStart_1006797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006806 : List Nat := [5, 2, 1, 2, 2, 10]
def baseStart_1006806 : Nat := 118140960795 + 1006806 * 2 ^ 59
def prefixEnd_1006806 : Nat := 4983230072969 + 3 ^ 40 * 1006806 * 2
def baseEnd_1006806 : Nat := 4254941595314346506953

theorem tailTrace_1006806 : CollatzResearch.WordTrace tailWord_1006806 prefixEnd_1006806 4254941595314346506953 := by
  unfold tailWord_1006806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2295076974407580351273017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24480821060347523746912181 2295076974407580351273017)
  ·
    refine ⟨1721307730805685263454763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2295076974407580351273017 1721307730805685263454763)
    ·
      refine ⟨2581961596208527895182145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1721307730805685263454763 2581961596208527895182145)
      ·
        refine ⟨1936471197156395921386609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2581961596208527895182145 1936471197156395921386609)
        ·
          refine ⟨1452353397867296941039957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1936471197156395921386609 1452353397867296941039957)
          ·
            refine ⟨4254941595314346506953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1452353397867296941039957 4254941595314346506953)
            ·
              rfl

theorem cell22_1006806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 10].length) (baseStart_1006806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006806 prefixEnd_1006806 := by exact prefixLift 1006806
  have htrace : WordTrace (prefixWord ++ tailWord_1006806) baseStart_1006806 baseEnd_1006806 := by
    simpa [prefixWord, tailWord_1006806, baseEnd_1006806] using wordTrace_append hprefix tailTrace_1006806
  have hstable : (prefixWord ++ tailWord_1006806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006806).length < 2 ^ (prefixWord ++ tailWord_1006806).sum := by decide
  have hdescent : baseEnd_1006806 < baseStart_1006806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006823 : List Nat := [1, 1, 5, 3, 3, 1, 1, 7]
def baseStart_1006823 : Nat := 118140960795 + 1006823 * 2 ^ 59
def prefixEnd_1006823 : Nat := 4983230072969 + 3 ^ 40 * 1006823 * 2
def baseEnd_1006823 : Nat := 38295120963097743265349

theorem tailTrace_1006823 : CollatzResearch.WordTrace tailWord_1006823 prefixEnd_1006823 38295120963097743265349 := by
  unfold tailWord_1006823
  simp only [CollatzResearch.WordTrace]
  refine ⟨36721851631459697523737123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24481234420973131682491415 36721851631459697523737123)
  ·
    refine ⟨55082777447189546285605685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36721851631459697523737123 55082777447189546285605685)
    ·
      refine ⟨5164010385674019964275533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55082777447189546285605685 5164010385674019964275533)
      ·
        refine ⟨1936503894627757486603325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5164010385674019964275533 1936503894627757486603325)
        ·
          refine ⟨726188960485409057476247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1936503894627757486603325 726188960485409057476247)
          ·
            refine ⟨1089283440728113586214371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726188960485409057476247 1089283440728113586214371)
            ·
              refine ⟨1633925161092170379321557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089283440728113586214371 1633925161092170379321557)
              ·
                refine ⟨38295120963097743265349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1633925161092170379321557 38295120963097743265349)
                ·
                  rfl

theorem cell22_1006823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 7].length) (baseStart_1006823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006823 prefixEnd_1006823 := by exact prefixLift 1006823
  have htrace : WordTrace (prefixWord ++ tailWord_1006823) baseStart_1006823 baseEnd_1006823 := by
    simpa [prefixWord, tailWord_1006823, baseEnd_1006823] using wordTrace_append hprefix tailTrace_1006823
  have hstable : (prefixWord ++ tailWord_1006823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006823).length < 2 ^ (prefixWord ++ tailWord_1006823).sum := by decide
  have hdescent : baseEnd_1006823 < baseStart_1006823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006898 : List Nat := [3, 2, 1, 1, 4, 2, 2, 2, 1, 4]
def baseStart_1006898 : Nat := 118140960795 + 1006898 * 2 ^ 59
def prefixEnd_1006898 : Nat := 4983230072969 + 3 ^ 40 * 1006898 * 2
def baseEnd_1006898 : Nat := 344681762700604493762911

theorem tailTrace_1006898 : CollatzResearch.WordTrace tailWord_1006898 prefixEnd_1006898 344681762700604493762911 := by
  unfold tailWord_1006898
  simp only [CollatzResearch.WordTrace]
  refine ⟨9181146776546996333179337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24483058070791990221811565 9181146776546996333179337)
  ·
    refine ⟨6885860082410247249884503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9181146776546996333179337 6885860082410247249884503)
    ·
      refine ⟨10328790123615370874826755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6885860082410247249884503 10328790123615370874826755)
      ·
        refine ⟨15493185185423056312240133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10328790123615370874826755 15493185185423056312240133)
        ·
          refine ⟨2904972222266823058545025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15493185185423056312240133 2904972222266823058545025)
          ·
            refine ⟨2178729166700117293908769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2904972222266823058545025 2178729166700117293908769)
            ·
              refine ⟨1634046875025087970431577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2178729166700117293908769 1634046875025087970431577)
              ·
                refine ⟨1225535156268815977823683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1634046875025087970431577 1225535156268815977823683)
                ·
                  refine ⟨1838302734403223966735525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225535156268815977823683 1838302734403223966735525)
                  ·
                    refine ⟨344681762700604493762911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1838302734403223966735525 344681762700604493762911)
                    ·
                      rfl

theorem cell22_1006898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_1006898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006898 prefixEnd_1006898 := by exact prefixLift 1006898
  have htrace : WordTrace (prefixWord ++ tailWord_1006898) baseStart_1006898 baseEnd_1006898 := by
    simpa [prefixWord, tailWord_1006898, baseEnd_1006898] using wordTrace_append hprefix tailTrace_1006898
  have hstable : (prefixWord ++ tailWord_1006898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006898).length < 2 ^ (prefixWord ++ tailWord_1006898).sum := by decide
  have hdescent : baseEnd_1006898 < baseStart_1006898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006911 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 4, 3]
def baseStart_1006911 : Nat := 118140960795 + 1006911 * 2 ^ 59
def prefixEnd_1006911 : Nat := 4983230072969 + 3 ^ 40 * 1006911 * 2
def baseEnd_1006911 : Nat := 344686212866276793187871

theorem tailTrace_1006911 : CollatzResearch.WordTrace tailWord_1006911 prefixEnd_1006911 344686212866276793187871 := by
  unfold tailWord_1006911
  simp only [CollatzResearch.WordTrace]
  refine ⟨36725061255140888552940587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24483374170093925701960391 36725061255140888552940587)
  ·
    refine ⟨55087591882711332829410881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36725061255140888552940587 55087591882711332829410881)
    ·
      refine ⟨41315693912033499622058161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55087591882711332829410881 41315693912033499622058161)
      ·
        refine ⟨30986770434025124716543621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41315693912033499622058161 30986770434025124716543621)
        ·
          refine ⟨5810019456379710884351929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30986770434025124716543621 5810019456379710884351929)
          ·
            refine ⟨4357514592284783163263947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5810019456379710884351929 4357514592284783163263947)
            ·
              refine ⟨6536271888427174744895921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4357514592284783163263947 6536271888427174744895921)
              ·
                refine ⟨4902203916320381058671941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6536271888427174744895921 4902203916320381058671941)
                ·
                  refine ⟨919163234310071448500989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4902203916320381058671941 919163234310071448500989)
                  ·
                    refine ⟨344686212866276793187871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 919163234310071448500989 344686212866276793187871)
                    ·
                      rfl

theorem cell22_1006911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 3].length) (baseStart_1006911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006911 prefixEnd_1006911 := by exact prefixLift 1006911
  have htrace : WordTrace (prefixWord ++ tailWord_1006911) baseStart_1006911 baseEnd_1006911 := by
    simpa [prefixWord, tailWord_1006911, baseEnd_1006911] using wordTrace_append hprefix tailTrace_1006911
  have hstable : (prefixWord ++ tailWord_1006911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006911).length < 2 ^ (prefixWord ++ tailWord_1006911).sum := by decide
  have hdescent : baseEnd_1006911 < baseStart_1006911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006924 : List Nat := [2, 2, 1, 3, 2, 2, 10]
def baseStart_1006924 : Nat := 118140960795 + 1006924 * 2 ^ 59
def prefixEnd_1006924 : Nat := 4983230072969 + 3 ^ 40 * 1006924 * 2
def baseEnd_1006924 : Nat := 12766320853035151578253

theorem tailTrace_1006924 : CollatzResearch.WordTrace tailWord_1006924 prefixEnd_1006924 12766320853035151578253 := by
  unfold tailWord_1006924
  simp only [CollatzResearch.WordTrace]
  refine ⟨18362767702046895886581913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24483690269395861182109217 18362767702046895886581913)
  ·
    refine ⟨13772075776535171914936435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18362767702046895886581913 13772075776535171914936435)
    ·
      refine ⟨20658113664802757872404653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13772075776535171914936435 20658113664802757872404653)
      ·
        refine ⟨7746792624301034202151745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20658113664802757872404653 7746792624301034202151745)
        ·
          refine ⟨5810094468225775651613809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7746792624301034202151745 5810094468225775651613809)
          ·
            refine ⟨4357570851169331738710357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5810094468225775651613809 4357570851169331738710357)
            ·
              refine ⟨12766320853035151578253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4357570851169331738710357 12766320853035151578253)
              ·
                rfl

theorem cell22_1006924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 10].length) (baseStart_1006924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006924 prefixEnd_1006924 := by exact prefixLift 1006924
  have htrace : WordTrace (prefixWord ++ tailWord_1006924) baseStart_1006924 baseEnd_1006924 := by
    simpa [prefixWord, tailWord_1006924, baseEnd_1006924] using wordTrace_append hprefix tailTrace_1006924
  have hstable : (prefixWord ++ tailWord_1006924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006924).length < 2 ^ (prefixWord ++ tailWord_1006924).sum := by decide
  have hdescent : baseEnd_1006924 < baseStart_1006924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006926 : List Nat := [4, 1, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_1006926 : Nat := 118140960795 + 1006926 * 2 ^ 59
def prefixEnd_1006926 : Nat := 4983230072969 + 3 ^ 40 * 1006926 * 2
def baseEnd_1006926 : Nat := 344691347672821754062825

theorem tailTrace_1006926 : CollatzResearch.WordTrace tailWord_1006926 prefixEnd_1006926 344691347672821754062825 := by
  unfold tailWord_1006926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4590701043760818264342079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24483738900057697409824421 4590701043760818264342079)
  ·
    refine ⟨6886051565641227396513119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4590701043760818264342079 6886051565641227396513119)
    ·
      refine ⟨10329077348461841094769679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6886051565641227396513119 10329077348461841094769679)
      ·
        refine ⟨15493616022692761642154519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10329077348461841094769679 15493616022692761642154519)
        ·
          refine ⟨23240424034039142463231779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15493616022692761642154519 23240424034039142463231779)
          ·
            refine ⟨34860636051058713694847669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23240424034039142463231779 34860636051058713694847669)
            ·
              refine ⟨3268184629786754408891969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34860636051058713694847669 3268184629786754408891969)
              ·
                refine ⟨2451138472340065806668977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3268184629786754408891969 2451138472340065806668977)
                ·
                  refine ⟨1838353854255049355001733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2451138472340065806668977 1838353854255049355001733)
                  ·
                    refine ⟨344691347672821754062825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1838353854255049355001733 344691347672821754062825)
                    ·
                      rfl

theorem cell22_1006926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_1006926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006926 prefixEnd_1006926 := by exact prefixLift 1006926
  have htrace : WordTrace (prefixWord ++ tailWord_1006926) baseStart_1006926 baseEnd_1006926 := by
    simpa [prefixWord, tailWord_1006926, baseEnd_1006926] using wordTrace_append hprefix tailTrace_1006926
  have hstable : (prefixWord ++ tailWord_1006926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006926).length < 2 ^ (prefixWord ++ tailWord_1006926).sum := by decide
  have hdescent : baseEnd_1006926 < baseStart_1006926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006969 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 9]
def baseStart_1006969 : Nat := 118140960795 + 1006969 * 2 ^ 59
def prefixEnd_1006969 : Nat := 4983230072969 + 3 ^ 40 * 1006969 * 2
def baseEnd_1006969 : Nat := 114902022483861325079231

theorem tailTrace_1006969 : CollatzResearch.WordTrace tailWord_1006969 prefixEnd_1006969 114902022483861325079231 := by
  unfold tailWord_1006969
  simp only [CollatzResearch.WordTrace]
  refine ⟨36727176688930764458551961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24484784459287176305701307 36727176688930764458551961)
  ·
    refine ⟨27545382516698073343913971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36727176688930764458551961 27545382516698073343913971)
    ·
      refine ⟨41318073775047110015870957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27545382516698073343913971 41318073775047110015870957)
      ·
        refine ⟨15494277665642666255951609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41318073775047110015870957 15494277665642666255951609)
        ·
          refine ⟨11620708249231999691963707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15494277665642666255951609 11620708249231999691963707)
          ·
            refine ⟨17431062373847999537945561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11620708249231999691963707 17431062373847999537945561)
            ·
              refine ⟨13073296780385999653459171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17431062373847999537945561 13073296780385999653459171)
              ·
                refine ⟨19609945170578999480188757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13073296780385999653459171 19609945170578999480188757)
                ·
                  refine ⟨114902022483861325079231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19609945170578999480188757 114902022483861325079231)
                  ·
                    rfl

theorem cell22_1006969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 9].length) (baseStart_1006969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1006969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1006969 prefixEnd_1006969 := by exact prefixLift 1006969
  have htrace : WordTrace (prefixWord ++ tailWord_1006969) baseStart_1006969 baseEnd_1006969 := by
    simpa [prefixWord, tailWord_1006969, baseEnd_1006969] using wordTrace_append hprefix tailTrace_1006969
  have hstable : (prefixWord ++ tailWord_1006969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006969).length < 2 ^ (prefixWord ++ tailWord_1006969).sum := by decide
  have hdescent : baseEnd_1006969 < baseStart_1006969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007001 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 2, 5]
def baseStart_1007001 : Nat := 118140960795 + 1007001 * 2 ^ 59
def prefixEnd_1007001 : Nat := 4983230072969 + 3 ^ 40 * 1007001 * 2
def baseEnd_1007001 : Nat := 344717021705546558437595

theorem tailTrace_1007001 : CollatzResearch.WordTrace tailWord_1007001 prefixEnd_1007001 344717021705546558437595 := by
  unfold tailWord_1007001
  simp only [CollatzResearch.WordTrace]
  refine ⟨36728343824814833923716857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24485562549876555949144571 36728343824814833923716857)
  ·
    refine ⟨27546257868611125442787643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36728343824814833923716857 27546257868611125442787643)
    ·
      refine ⟨41319386802916688164181465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27546257868611125442787643 41319386802916688164181465)
      ·
        refine ⟨30989540102187516123136099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41319386802916688164181465 30989540102187516123136099)
        ·
          refine ⟨46484310153281274184704149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30989540102187516123136099 46484310153281274184704149)
          ·
            refine ⟨2178952038435059727408007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46484310153281274184704149 2178952038435059727408007)
            ·
              refine ⟨3268428057652589591112011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178952038435059727408007 3268428057652589591112011)
              ·
                refine ⟨4902642086478884386668017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3268428057652589591112011 4902642086478884386668017)
                ·
                  refine ⟨3676981564859163290001013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4902642086478884386668017 3676981564859163290001013)
                  ·
                    refine ⟨344717021705546558437595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3676981564859163290001013 344717021705546558437595)
                    ·
                      rfl

theorem cell22_1007001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 5].length) (baseStart_1007001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007001 prefixEnd_1007001 := by exact prefixLift 1007001
  have htrace : WordTrace (prefixWord ++ tailWord_1007001) baseStart_1007001 baseEnd_1007001 := by
    simpa [prefixWord, tailWord_1007001, baseEnd_1007001] using wordTrace_append hprefix tailTrace_1007001
  have hstable : (prefixWord ++ tailWord_1007001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007001).length < 2 ^ (prefixWord ++ tailWord_1007001).sum := by decide
  have hdescent : baseEnd_1007001 < baseStart_1007001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007048 : List Nat := [2, 1, 3, 1, 3, 1, 1, 6, 4]
def baseStart_1007048 : Nat := 118140960795 + 1007048 * 2 ^ 59
def prefixEnd_1007048 : Nat := 4983230072969 + 3 ^ 40 * 1007048 * 2
def baseEnd_1007048 : Nat := 114911036922018034170817

theorem tailTrace_1007048 : CollatzResearch.WordTrace tailWord_1007048 prefixEnd_1007048 114911036922018034170817 := by
  unfold tailWord_1007048
  simp only [CollatzResearch.WordTrace]
  refine ⟨18365029027822280475338899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24486705370429707300451865 18365029027822280475338899)
  ·
    refine ⟨27547543541733420713008349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18365029027822280475338899 27547543541733420713008349)
    ·
      refine ⟨10330328828150032767378131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27547543541733420713008349 10330328828150032767378131)
      ·
        refine ⟨15495493242225049151067197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10330328828150032767378131 15495493242225049151067197)
        ·
          refine ⟨5810809965834393431650199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15495493242225049151067197 5810809965834393431650199)
          ·
            refine ⟨8716214948751590147475299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5810809965834393431650199 8716214948751590147475299)
            ·
              refine ⟨13074322423127385221212949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8716214948751590147475299 13074322423127385221212949)
              ·
                refine ⟨612858863584096182244357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13074322423127385221212949 612858863584096182244357)
                ·
                  refine ⟨114911036922018034170817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 612858863584096182244357 114911036922018034170817)
                  ·
                    rfl

theorem cell22_1007048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 4].length) (baseStart_1007048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007048 prefixEnd_1007048 := by exact prefixLift 1007048
  have htrace : WordTrace (prefixWord ++ tailWord_1007048) baseStart_1007048 baseEnd_1007048 := by
    simpa [prefixWord, tailWord_1007048, baseEnd_1007048] using wordTrace_append hprefix tailTrace_1007048
  have hstable : (prefixWord ++ tailWord_1007048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007048).length < 2 ^ (prefixWord ++ tailWord_1007048).sum := by decide
  have hdescent : baseEnd_1007048 < baseStart_1007048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007061 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 3, 6]
def baseStart_1007061 : Nat := 118140960795 + 1007061 * 2 ^ 59
def prefixEnd_1007061 : Nat := 4983230072969 + 3 ^ 40 * 1007061 * 2
def baseEnd_1007061 : Nat := 344737560931726401937411

theorem tailTrace_1007061 : CollatzResearch.WordTrace tailWord_1007061 prefixEnd_1007061 344737560931726401937411 := by
  unfold tailWord_1007061
  simp only [CollatzResearch.WordTrace]
  refine ⟨36730532204597464170901037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24487021469731642780600691 36730532204597464170901037)
  ·
    refine ⟨13773949576724049064087889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36730532204597464170901037 13773949576724049064087889)
    ·
      refine ⟨10330462182543036798065917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13773949576724049064087889 10330462182543036798065917)
      ·
        refine ⟨3873923318453638799274719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10330462182543036798065917 3873923318453638799274719)
        ·
          refine ⟨5810884977680458198912079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3873923318453638799274719 5810884977680458198912079)
          ·
            refine ⟨8716327466520687298368119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5810884977680458198912079 8716327466520687298368119)
            ·
              refine ⟨13074491199781030947552179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8716327466520687298368119 13074491199781030947552179)
              ·
                refine ⟨19611736799671546421328269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13074491199781030947552179 19611736799671546421328269)
                ·
                  refine ⟨7354401299876829907998101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19611736799671546421328269 7354401299876829907998101)
                  ·
                    refine ⟨344737560931726401937411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7354401299876829907998101 344737560931726401937411)
                    ·
                      rfl

theorem cell22_1007061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_1007061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007061 prefixEnd_1007061 := by exact prefixLift 1007061
  have htrace : WordTrace (prefixWord ++ tailWord_1007061) baseStart_1007061 baseEnd_1007061 := by
    simpa [prefixWord, tailWord_1007061, baseEnd_1007061] using wordTrace_append hprefix tailTrace_1007061
  have hstable : (prefixWord ++ tailWord_1007061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007061).length < 2 ^ (prefixWord ++ tailWord_1007061).sum := by decide
  have hdescent : baseEnd_1007061 < baseStart_1007061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007063 : List Nat := [1, 1, 3, 2, 1, 1, 1, 7, 2, 3]
def baseStart_1007063 : Nat := 118140960795 + 1007063 * 2 ^ 59
def prefixEnd_1007063 : Nat := 4983230072969 + 3 ^ 40 * 1007063 * 2
def baseEnd_1007063 : Nat := 344738245572599063387405

theorem tailTrace_1007063 : CollatzResearch.WordTrace tailWord_1007063 prefixEnd_1007063 344738245572599063387405 := by
  unfold tailWord_1007063
  simp only [CollatzResearch.WordTrace]
  refine ⟨36730605150590218512473843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24487070100393479008315895 36730605150590218512473843)
  ·
    refine ⟨55095907725885327768710765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36730605150590218512473843 55095907725885327768710765)
    ·
      refine ⟨20660965397206997913266537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55095907725885327768710765 20660965397206997913266537)
      ·
        refine ⟨15495724047905248434949903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20660965397206997913266537 15495724047905248434949903)
        ·
          refine ⟨23243586071857872652424855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15495724047905248434949903 23243586071857872652424855)
          ·
            refine ⟨34865379107786808978637283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23243586071857872652424855 34865379107786808978637283)
            ·
              refine ⟨52298068661680213467955925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34865379107786808978637283 52298068661680213467955925)
              ·
                refine ⟨1225735984258130003155217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 52298068661680213467955925 1225735984258130003155217)
                ·
                  refine ⟨919301988193597502366413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1225735984258130003155217 919301988193597502366413)
                  ·
                    refine ⟨344738245572599063387405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 919301988193597502366413 344738245572599063387405)
                    ·
                      rfl

theorem cell22_1007063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_1007063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007063 prefixEnd_1007063 := by exact prefixLift 1007063
  have htrace : WordTrace (prefixWord ++ tailWord_1007063) baseStart_1007063 baseEnd_1007063 := by
    simpa [prefixWord, tailWord_1007063, baseEnd_1007063] using wordTrace_append hprefix tailTrace_1007063
  have hstable : (prefixWord ++ tailWord_1007063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007063).length < 2 ^ (prefixWord ++ tailWord_1007063).sum := by decide
  have hdescent : baseEnd_1007063 < baseStart_1007063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007082 : List Nat := [3, 1, 3, 1, 4, 2, 1, 3, 4]
def baseStart_1007082 : Nat := 118140960795 + 1007082 * 2 ^ 59
def prefixEnd_1007082 : Nat := 4983230072969 + 3 ^ 40 * 1007082 * 2
def baseEnd_1007082 : Nat := 114914916553629782387449

theorem tailTrace_1007082 : CollatzResearch.WordTrace tailWord_1007082 prefixEnd_1007082 114914916553629782387449 := by
  unfold tailWord_1007082
  simp only [CollatzResearch.WordTrace]
  refine ⟨9182824534380346189353875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24487532091680923171610333 9182824534380346189353875)
  ·
    refine ⟨13774236801570519284030813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9182824534380346189353875 13774236801570519284030813)
    ·
      refine ⟨5165338800588944731511555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13774236801570519284030813 5165338800588944731511555)
      ·
        refine ⟨7748008200883417097267333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5165338800588944731511555 7748008200883417097267333)
        ·
          refine ⟨1452751537665640705737625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7748008200883417097267333 1452751537665640705737625)
          ·
            refine ⟨1089563653249230529303219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1452751537665640705737625 1089563653249230529303219)
            ·
              refine ⟨1634345479873845793954829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089563653249230529303219 1634345479873845793954829)
              ·
                refine ⟨612879554952692172733061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1634345479873845793954829 612879554952692172733061)
                ·
                  refine ⟨114914916553629782387449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 612879554952692172733061 114914916553629782387449)
                  ·
                    rfl

theorem cell22_1007082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 4].length) (baseStart_1007082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007082 prefixEnd_1007082 := by exact prefixLift 1007082
  have htrace : WordTrace (prefixWord ++ tailWord_1007082) baseStart_1007082 baseEnd_1007082 := by
    simpa [prefixWord, tailWord_1007082, baseEnd_1007082] using wordTrace_append hprefix tailTrace_1007082
  have hstable : (prefixWord ++ tailWord_1007082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007082).length < 2 ^ (prefixWord ++ tailWord_1007082).sum := by decide
  have hdescent : baseEnd_1007082 < baseStart_1007082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007093 : List Nat := [1, 3, 5, 1, 1, 1, 10]
def baseStart_1007093 : Nat := 118140960795 + 1007093 * 2 ^ 59
def prefixEnd_1007093 : Nat := 4983230072969 + 3 ^ 40 * 1007093 * 2
def baseEnd_1007093 : Nat := 12768463525395888338419

theorem tailTrace_1007093 : CollatzResearch.WordTrace tailWord_1007093 prefixEnd_1007093 12768463525395888338419 := by
  unfold tailWord_1007093
  simp only [CollatzResearch.WordTrace]
  refine ⟨36731699340481533636065933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24487799560321022424043955 36731699340481533636065933)
  ·
    refine ⟨13774387252680575113524725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36731699340481533636065933 13774387252680575113524725)
    ·
      refine ⟨1291348804938803916892943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13774387252680575113524725 1291348804938803916892943)
      ·
        refine ⟨1937023207408205875339415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1291348804938803916892943 1937023207408205875339415)
        ·
          refine ⟨2905534811112308813009123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1937023207408205875339415 2905534811112308813009123)
          ·
            refine ⟨4358302216668463219513685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2905534811112308813009123 4358302216668463219513685)
            ·
              refine ⟨12768463525395888338419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4358302216668463219513685 12768463525395888338419)
              ·
                rfl

theorem cell22_1007093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 10].length) (baseStart_1007093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007093 prefixEnd_1007093 := by exact prefixLift 1007093
  have htrace : WordTrace (prefixWord ++ tailWord_1007093) baseStart_1007093 baseEnd_1007093 := by
    simpa [prefixWord, tailWord_1007093, baseEnd_1007093] using wordTrace_append hprefix tailTrace_1007093
  have hstable : (prefixWord ++ tailWord_1007093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007093).length < 2 ^ (prefixWord ++ tailWord_1007093).sum := by decide
  have hdescent : baseEnd_1007093 < baseStart_1007093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007159 : List Nat := [1, 1, 3, 1, 2, 6, 2, 2, 1, 3]
def baseStart_1007159 : Nat := 118140960795 + 1007159 * 2 ^ 59
def prefixEnd_1007159 : Nat := 4983230072969 + 3 ^ 40 * 1007159 * 2
def baseEnd_1007159 : Nat := 344771108334486812987111

theorem tailTrace_1007159 : CollatzResearch.WordTrace tailWord_1007159 prefixEnd_1007159 344771108334486812987111 := by
  unfold tailWord_1007159
  simp only [CollatzResearch.WordTrace]
  refine ⟨36734106558242426907968531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24489404372161617938645687 36734106558242426907968531)
  ·
    refine ⟨55101159837363640361952797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36734106558242426907968531 55101159837363640361952797)
    ·
      refine ⟨20662934939011365135732299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55101159837363640361952797 20662934939011365135732299)
      ·
        refine ⟨30994402408517047703598449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20662934939011365135732299 30994402408517047703598449)
        ·
          refine ⟨23245801806387785777698837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30994402408517047703598449 23245801806387785777698837)
          ·
            refine ⟨1089646959674427458329633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23245801806387785777698837 1089646959674427458329633)
            ·
              refine ⟨817235219755820593747225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1089646959674427458329633 817235219755820593747225)
              ·
                refine ⟨612926414816865445310419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 817235219755820593747225 612926414816865445310419)
                ·
                  refine ⟨919389622225298167965629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 612926414816865445310419 919389622225298167965629)
                  ·
                    refine ⟨344771108334486812987111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 919389622225298167965629 344771108334486812987111)
                    ·
                      rfl

theorem cell22_1007159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 1, 3].length) (baseStart_1007159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007159 prefixEnd_1007159 := by exact prefixLift 1007159
  have htrace : WordTrace (prefixWord ++ tailWord_1007159) baseStart_1007159 baseEnd_1007159 := by
    simpa [prefixWord, tailWord_1007159, baseEnd_1007159] using wordTrace_append hprefix tailTrace_1007159
  have hstable : (prefixWord ++ tailWord_1007159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007159).length < 2 ^ (prefixWord ++ tailWord_1007159).sum := by decide
  have hdescent : baseEnd_1007159 < baseStart_1007159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007232 : List Nat := [2, 1, 1, 2, 1, 4, 5, 1, 2, 3]
def baseStart_1007232 : Nat := 118140960795 + 1007232 * 2 ^ 59
def prefixEnd_1007232 : Nat := 4983230072969 + 3 ^ 40 * 1007232 * 2
def baseEnd_1007232 : Nat := 344796097726338955911887

theorem tailTrace_1007232 : CollatzResearch.WordTrace tailWord_1007232 prefixEnd_1007232 344796097726338955911887 := by
  unfold tailWord_1007232
  simp only [CollatzResearch.WordTrace]
  refine ⟨18368384543488980187687975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24491179391318640250250633 18368384543488980187687975)
  ·
    refine ⟨27552576815233470281531963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18368384543488980187687975 27552576815233470281531963)
    ·
      refine ⟨41328865222850205422297945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27552576815233470281531963 41328865222850205422297945)
      ·
        refine ⟨30996648917137654066723459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41328865222850205422297945 30996648917137654066723459)
        ·
          refine ⟨46494973375706481100085189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30996648917137654066723459 46494973375706481100085189)
          ·
            refine ⟨8717807507944965206265973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46494973375706481100085189 8717807507944965206265973)
            ·
              refine ⟨817294453869840488087435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8717807507944965206265973 817294453869840488087435)
              ·
                refine ⟨1225941680804760732131153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817294453869840488087435 1225941680804760732131153)
                ·
                  refine ⟨919456260603570549098365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1225941680804760732131153 919456260603570549098365)
                  ·
                    refine ⟨344796097726338955911887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 919456260603570549098365 344796097726338955911887)
                    ·
                      rfl

theorem cell22_1007232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 2, 3].length) (baseStart_1007232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007232 prefixEnd_1007232 := by exact prefixLift 1007232
  have htrace : WordTrace (prefixWord ++ tailWord_1007232) baseStart_1007232 baseEnd_1007232 := by
    simpa [prefixWord, tailWord_1007232, baseEnd_1007232] using wordTrace_append hprefix tailTrace_1007232
  have hstable : (prefixWord ++ tailWord_1007232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007232).length < 2 ^ (prefixWord ++ tailWord_1007232).sum := by decide
  have hdescent : baseEnd_1007232 < baseStart_1007232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007288 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 2, 5]
def baseStart_1007288 : Nat := 118140960795 + 1007288 * 2 ^ 59
def prefixEnd_1007288 : Nat := 4983230072969 + 3 ^ 40 * 1007288 * 2
def baseEnd_1007288 : Nat := 344815267670773476511715

theorem tailTrace_1007288 : CollatzResearch.WordTrace tailWord_1007288 prefixEnd_1007288 344815267670773476511715 := by
  unfold tailWord_1007288
  simp only [CollatzResearch.WordTrace]
  refine ⟨18369405787387540969707259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24492541049850054626276345 18369405787387540969707259)
  ·
    refine ⟨27554108681081311454560889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18369405787387540969707259 27554108681081311454560889)
    ·
      refine ⟨20665581510810983590920667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27554108681081311454560889 20665581510810983590920667)
      ·
        refine ⟨30998372266216475386381001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20665581510810983590920667 30998372266216475386381001)
        ·
          refine ⟨23248779199662356539785751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30998372266216475386381001 23248779199662356539785751)
          ·
            refine ⟨34873168799493534809678627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23248779199662356539785751 34873168799493534809678627)
            ·
              refine ⟨52309753199240302214517941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34873168799493534809678627 52309753199240302214517941)
              ·
                refine ⟨4904039362428778332611057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52309753199240302214517941 4904039362428778332611057)
                ·
                  refine ⟨3678029521821583749458293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4904039362428778332611057 3678029521821583749458293)
                  ·
                    refine ⟨344815267670773476511715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3678029521821583749458293 344815267670773476511715)
                    ·
                      rfl

theorem cell22_1007288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_1007288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007288 prefixEnd_1007288 := by exact prefixLift 1007288
  have htrace : WordTrace (prefixWord ++ tailWord_1007288) baseStart_1007288 baseEnd_1007288 := by
    simpa [prefixWord, tailWord_1007288, baseEnd_1007288] using wordTrace_append hprefix tailTrace_1007288
  have hstable : (prefixWord ++ tailWord_1007288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007288).length < 2 ^ (prefixWord ++ tailWord_1007288).sum := by decide
  have hdescent : baseEnd_1007288 < baseStart_1007288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007290 : List Nat := [3, 1, 1, 1, 2, 5, 1, 3, 5]
def baseStart_1007290 : Nat := 118140960795 + 1007290 * 2 ^ 59
def prefixEnd_1007290 : Nat := 4983230072969 + 3 ^ 40 * 1007290 * 2
def baseEnd_1007290 : Nat := 114938650770548712653903

theorem tailTrace_1007290 : CollatzResearch.WordTrace tailWord_1007290 prefixEnd_1007290 114938650770548712653903 := by
  unfold tailWord_1007290
  simp only [CollatzResearch.WordTrace]
  refine ⟨9184721130191959070246831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24492589680511890853991549 9184721130191959070246831)
  ·
    refine ⟨13777081695287938605370247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9184721130191959070246831 13777081695287938605370247)
    ·
      refine ⟨20665622542931907908055371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13777081695287938605370247 20665622542931907908055371)
      ·
        refine ⟨30998433814397861862083057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20665622542931907908055371 30998433814397861862083057)
        ·
          refine ⟨23248825360798396396562293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30998433814397861862083057 23248825360798396396562293)
          ·
            refine ⟨2179577377574849662177715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23248825360798396396562293 2179577377574849662177715)
            ·
              refine ⟨3269366066362274493266573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2179577377574849662177715 3269366066362274493266573)
              ·
                refine ⟨1226012274885852934974965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3269366066362274493266573 1226012274885852934974965)
                ·
                  refine ⟨114938650770548712653903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1226012274885852934974965 114938650770548712653903)
                  ·
                    rfl

theorem cell22_1007290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_1007290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007290 prefixEnd_1007290 := by exact prefixLift 1007290
  have htrace : WordTrace (prefixWord ++ tailWord_1007290) baseStart_1007290 baseEnd_1007290 := by
    simpa [prefixWord, tailWord_1007290, baseEnd_1007290] using wordTrace_append hprefix tailTrace_1007290
  have hstable : (prefixWord ++ tailWord_1007290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007290).length < 2 ^ (prefixWord ++ tailWord_1007290).sum := by decide
  have hdescent : baseEnd_1007290 < baseStart_1007290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007324 : List Nat := [2, 2, 5, 1, 2, 1, 2, 2, 5]
def baseStart_1007324 : Nat := 118140960795 + 1007324 * 2 ^ 59
def prefixEnd_1007324 : Nat := 4983230072969 + 3 ^ 40 * 1007324 * 2
def baseEnd_1007324 : Nat := 114942530402160460870535

theorem tailTrace_1007324 : CollatzResearch.WordTrace tailWord_1007324 prefixEnd_1007324 114942530402160460870535 := by
  unfold tailWord_1007324
  simp only [CollatzResearch.WordTrace]
  refine ⟨18370062301322330043862513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24493416401763106725150017 18370062301322330043862513)
  ·
    refine ⟨13777546725991747532896885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18370062301322330043862513 13777546725991747532896885)
    ·
      refine ⟨1291645005561726331209083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13777546725991747532896885 1291645005561726331209083)
      ·
        refine ⟨1937467508342589496813625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1291645005561726331209083 1937467508342589496813625)
        ·
          refine ⟨1453100631256942122610219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1937467508342589496813625 1453100631256942122610219)
          ·
            refine ⟨2179650946885413183915329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1453100631256942122610219 2179650946885413183915329)
            ·
              refine ⟨1634738210164059887936497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2179650946885413183915329 1634738210164059887936497)
              ·
                refine ⟨1226053657623044915952373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1634738210164059887936497 1226053657623044915952373)
                ·
                  refine ⟨114942530402160460870535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1226053657623044915952373 114942530402160460870535)
                  ·
                    rfl

theorem cell22_1007324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_1007324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007324 prefixEnd_1007324 := by exact prefixLift 1007324
  have htrace : WordTrace (prefixWord ++ tailWord_1007324) baseStart_1007324 baseEnd_1007324 := by
    simpa [prefixWord, tailWord_1007324, baseEnd_1007324] using wordTrace_append hprefix tailTrace_1007324
  have hstable : (prefixWord ++ tailWord_1007324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007324).length < 2 ^ (prefixWord ++ tailWord_1007324).sum := by decide
  have hdescent : baseEnd_1007324 < baseStart_1007324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007363 : List Nat := [1, 1, 1, 3, 2, 2, 2, 10]
def baseStart_1007363 : Nat := 118140960795 + 1007363 * 2 ^ 59
def prefixEnd_1007363 : Nat := 4983230072969 + 3 ^ 40 * 1007363 * 2
def baseEnd_1007363 : Nat := 38315660189277586765165

theorem tailTrace_1007363 : CollatzResearch.WordTrace tailWord_1007363 prefixEnd_1007363 38315660189277586765165 := by
  unfold tailWord_1007363
  simp only [CollatzResearch.WordTrace]
  refine ⟨36741547049503369748394743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24494364699668913165596495 36741547049503369748394743)
  ·
    refine ⟨55112320574255054622592115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36741547049503369748394743 55112320574255054622592115)
    ·
      refine ⟨82668480861382581933888173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55112320574255054622592115 82668480861382581933888173)
      ·
        refine ⟨31000680323018468225208065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82668480861382581933888173 31000680323018468225208065)
        ·
          refine ⟨23250510242263851168906049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31000680323018468225208065 23250510242263851168906049)
          ·
            refine ⟨17437882681697888376679537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23250510242263851168906049 17437882681697888376679537)
            ·
              refine ⟨13078412011273416282509653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17437882681697888376679537 13078412011273416282509653)
              ·
                refine ⟨38315660189277586765165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13078412011273416282509653 38315660189277586765165)
                ·
                  rfl

theorem cell22_1007363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 10].length) (baseStart_1007363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007363 prefixEnd_1007363 := by exact prefixLift 1007363
  have htrace : WordTrace (prefixWord ++ tailWord_1007363) baseStart_1007363 baseEnd_1007363 := by
    simpa [prefixWord, tailWord_1007363, baseEnd_1007363] using wordTrace_append hprefix tailTrace_1007363
  have hstable : (prefixWord ++ tailWord_1007363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007363).length < 2 ^ (prefixWord ++ tailWord_1007363).sum := by decide
  have hdescent : baseEnd_1007363 < baseStart_1007363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007414 : List Nat := [5, 1, 2, 2, 1, 1, 4, 6]
def baseStart_1007414 : Nat := 118140960795 + 1007414 * 2 ^ 59
def prefixEnd_1007414 : Nat := 4983230072969 + 3 ^ 40 * 1007414 * 2
def baseEnd_1007414 : Nat := 38317600005083460873481

theorem tailTrace_1007414 : CollatzResearch.WordTrace tailWord_1007414 prefixEnd_1007414 38317600005083460873481 := by
  unfold tailWord_1007414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2296462948269912841156331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24495604781545736972334197 2296462948269912841156331)
  ·
    refine ⟨3444694422404869261734497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2296462948269912841156331 3444694422404869261734497)
    ·
      refine ⟨2583520816803651946300873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3444694422404869261734497 2583520816803651946300873)
      ·
        refine ⟨1937640612602738959725655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2583520816803651946300873 1937640612602738959725655)
        ·
          refine ⟨2906460918904108439588483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1937640612602738959725655 2906460918904108439588483)
          ·
            refine ⟨4359691378356162659382725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2906460918904108439588483 4359691378356162659382725)
            ·
              refine ⟨817442133441780498634261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4359691378356162659382725 817442133441780498634261)
              ·
                refine ⟨38317600005083460873481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 817442133441780498634261 38317600005083460873481)
                ·
                  rfl

theorem cell22_1007414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_1007414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007414 prefixEnd_1007414 := by exact prefixLift 1007414
  have htrace : WordTrace (prefixWord ++ tailWord_1007414) baseStart_1007414 baseEnd_1007414 := by
    simpa [prefixWord, tailWord_1007414, baseEnd_1007414] using wordTrace_append hprefix tailTrace_1007414
  have hstable : (prefixWord ++ tailWord_1007414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007414).length < 2 ^ (prefixWord ++ tailWord_1007414).sum := by decide
  have hdescent : baseEnd_1007414 < baseStart_1007414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007487 : List Nat := [1, 1, 2, 2, 1, 1, 3, 7, 4]
def baseStart_1007487 : Nat := 118140960795 + 1007487 * 2 ^ 59
def prefixEnd_1007487 : Nat := 4983230072969 + 3 ^ 40 * 1007487 * 2
def baseEnd_1007487 : Nat := 114961129812534430262035

theorem tailTrace_1007487 : CollatzResearch.WordTrace tailWord_1007487 prefixEnd_1007487 114961129812534430262035 := by
  unfold tailWord_1007487
  simp only [CollatzResearch.WordTrace]
  refine ⟨36746069701054138925908715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24497379800702759283939143 36746069701054138925908715)
  ·
    refine ⟨55119104551581208388863073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36746069701054138925908715 55119104551581208388863073)
    ·
      refine ⟨41339328413685906291647305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55119104551581208388863073 41339328413685906291647305)
      ·
        refine ⟨31004496310264429718735479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41339328413685906291647305 31004496310264429718735479)
        ·
          refine ⟨46506744465396644578103219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31004496310264429718735479 46506744465396644578103219)
          ·
            refine ⟨69760116698094966867154829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46506744465396644578103219 69760116698094966867154829)
            ·
              refine ⟨26160043761785612575183061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69760116698094966867154829 26160043761785612575183061)
              ·
                refine ⟨613126025666850294730853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26160043761785612575183061 613126025666850294730853)
                ·
                  refine ⟨114961129812534430262035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 613126025666850294730853 114961129812534430262035)
                  ·
                    rfl

theorem cell22_1007487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 4].length) (baseStart_1007487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007487 prefixEnd_1007487 := by exact prefixLift 1007487
  have htrace : WordTrace (prefixWord ++ tailWord_1007487) baseStart_1007487 baseEnd_1007487 := by
    simpa [prefixWord, tailWord_1007487, baseEnd_1007487] using wordTrace_append hprefix tailTrace_1007487
  have hstable : (prefixWord ++ tailWord_1007487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007487).length < 2 ^ (prefixWord ++ tailWord_1007487).sum := by decide
  have hdescent : baseEnd_1007487 < baseStart_1007487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007500 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 3, 6]
def baseStart_1007500 : Nat := 118140960795 + 1007500 * 2 ^ 59
def prefixEnd_1007500 : Nat := 4983230072969 + 3 ^ 40 * 1007500 * 2
def baseEnd_1007500 : Nat := 344887839603275590211065

theorem tailTrace_1007500 : CollatzResearch.WordTrace tailWord_1007500 prefixEnd_1007500 344887839603275590211065 := by
  unfold tailWord_1007500
  simp only [CollatzResearch.WordTrace]
  refine ⟨18373271925003521073065977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24497695900004694764087969 18373271925003521073065977)
  ·
    refine ⟨13779953943752640804799483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18373271925003521073065977 13779953943752640804799483)
    ·
      refine ⟨20669930915628961207199225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13779953943752640804799483 20669930915628961207199225)
      ·
        refine ⟨15502448186721720905399419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20669930915628961207199225 15502448186721720905399419)
        ·
          refine ⟨23253672280082581358099129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15502448186721720905399419 23253672280082581358099129)
          ·
            refine ⟨17440254210061936018574347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23253672280082581358099129 17440254210061936018574347)
            ·
              refine ⟨26160381315092904027861521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17440254210061936018574347 26160381315092904027861521)
              ·
                refine ⟨19620285986319678020896141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26160381315092904027861521 19620285986319678020896141)
                ·
                  refine ⟨7357607244869879257836053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19620285986319678020896141 7357607244869879257836053)
                  ·
                    refine ⟨344887839603275590211065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7357607244869879257836053 344887839603275590211065)
                    ·
                      rfl

theorem cell22_1007500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_1007500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007500 prefixEnd_1007500 := by exact prefixLift 1007500
  have htrace : WordTrace (prefixWord ++ tailWord_1007500) baseStart_1007500 baseEnd_1007500 := by
    simpa [prefixWord, tailWord_1007500, baseEnd_1007500] using wordTrace_append hprefix tailTrace_1007500
  have hstable : (prefixWord ++ tailWord_1007500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007500).length < 2 ^ (prefixWord ++ tailWord_1007500).sum := by decide
  have hdescent : baseEnd_1007500 < baseStart_1007500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007519 : List Nat := [1, 1, 2, 5, 3, 1, 2, 1, 1, 5]
def baseStart_1007519 : Nat := 118140960795 + 1007519 * 2 ^ 59
def prefixEnd_1007519 : Nat := 4983230072969 + 3 ^ 40 * 1007519 * 2
def baseEnd_1007519 : Nat := 344894343691565873986007

theorem tailTrace_1007519 : CollatzResearch.WordTrace tailWord_1007519 prefixEnd_1007519 344894343691565873986007 := by
  unfold tailWord_1007519
  simp only [CollatzResearch.WordTrace]
  refine ⟨36747236836938208391073611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24498157891292138927382407 36747236836938208391073611)
  ·
    refine ⟨55120855255407312586610417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36747236836938208391073611 55120855255407312586610417)
    ·
      refine ⟨41340641441555484439957813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55120855255407312586610417 41340641441555484439957813)
      ·
        refine ⟨3875685135145826666246045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41340641441555484439957813 3875685135145826666246045)
        ·
          refine ⟨1453381925679684999842267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3875685135145826666246045 1453381925679684999842267)
          ·
            refine ⟨2180072888519527499763401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1453381925679684999842267 2180072888519527499763401)
            ·
              refine ⟨1635054666389645624822551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2180072888519527499763401 1635054666389645624822551)
              ·
                refine ⟨2452581999584468437233827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1635054666389645624822551 2452581999584468437233827)
                ·
                  refine ⟨3678872999376702655850741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2452581999584468437233827 3678872999376702655850741)
                  ·
                    refine ⟨344894343691565873986007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3678872999376702655850741 344894343691565873986007)
                    ·
                      rfl

theorem cell22_1007519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 5].length) (baseStart_1007519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007519 prefixEnd_1007519 := by exact prefixLift 1007519
  have htrace : WordTrace (prefixWord ++ tailWord_1007519) baseStart_1007519 baseEnd_1007519 := by
    simpa [prefixWord, tailWord_1007519, baseEnd_1007519] using wordTrace_append hprefix tailTrace_1007519
  have hstable : (prefixWord ++ tailWord_1007519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007519).length < 2 ^ (prefixWord ++ tailWord_1007519).sum := by decide
  have hdescent : baseEnd_1007519 < baseStart_1007519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007540 : List Nat := [2, 5, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_1007540 : Nat := 118140960795 + 1007540 * 2 ^ 59
def prefixEnd_1007540 : Nat := 4983230072969 + 3 ^ 40 * 1007540 * 2
def baseEnd_1007540 : Nat := 344901532420728819210943

theorem tailTrace_1007540 : CollatzResearch.WordTrace tailWord_1007540 prefixEnd_1007540 344901532420728819210943 := by
  unfold tailWord_1007540
  simp only [CollatzResearch.WordTrace]
  refine ⟨18374001384931064488794037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24498668513241419318392049 18374001384931064488794037)
  ·
    refine ⟨1722562629837287295824441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18374001384931064488794037 1722562629837287295824441)
    ·
      refine ⟨1291921972377965471868331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1722562629837287295824441 1291921972377965471868331)
      ·
        refine ⟨1937882958566948207802497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1291921972377965471868331 1937882958566948207802497)
        ·
          refine ⟨1453412218925211155851873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1937882958566948207802497 1453412218925211155851873)
          ·
            refine ⟨1090059164193908366888905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1453412218925211155851873 1090059164193908366888905)
            ·
              refine ⟨817544373145431275166679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1090059164193908366888905 817544373145431275166679)
              ·
                refine ⟨1226316559718146912750019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817544373145431275166679 1226316559718146912750019)
                ·
                  refine ⟨1839474839577220369125029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1226316559718146912750019 1839474839577220369125029)
                  ·
                    refine ⟨344901532420728819210943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1839474839577220369125029 344901532420728819210943)
                    ·
                      rfl

theorem cell22_1007540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_1007540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007540 prefixEnd_1007540 := by exact prefixLift 1007540
  have htrace : WordTrace (prefixWord ++ tailWord_1007540) baseStart_1007540 baseEnd_1007540 := by
    simpa [prefixWord, tailWord_1007540, baseEnd_1007540] using wordTrace_append hprefix tailTrace_1007540
  have hstable : (prefixWord ++ tailWord_1007540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007540).length < 2 ^ (prefixWord ++ tailWord_1007540).sum := by decide
  have hdescent : baseEnd_1007540 < baseStart_1007540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007564 : List Nat := [2, 2, 1, 4, 1, 2, 1, 3, 3, 3]
def baseStart_1007564 : Nat := 118140960795 + 1007564 * 2 ^ 59
def prefixEnd_1007564 : Nat := 4983230072969 + 3 ^ 40 * 1007564 * 2
def baseEnd_1007564 : Nat := 344909748111200756610869

theorem tailTrace_1007564 : CollatzResearch.WordTrace tailWord_1007564 prefixEnd_1007564 344909748111200756610869 := by
  unfold tailWord_1007564
  simp only [CollatzResearch.WordTrace]
  refine ⟨18374439060887590538230873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24499252081183454050974497 18374439060887590538230873)
  ·
    refine ⟨13780829295665692903673155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18374439060887590538230873 13780829295665692903673155)
    ·
      refine ⟨20671243943498539355509733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13780829295665692903673155 20671243943498539355509733)
      ·
        refine ⟨3875858239405976129158075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20671243943498539355509733 3875858239405976129158075)
        ·
          refine ⟨5813787359108964193737113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3875858239405976129158075 5813787359108964193737113)
          ·
            refine ⟨4360340519331723145302835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5813787359108964193737113 4360340519331723145302835)
            ·
              refine ⟨6540510778997584717954253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4360340519331723145302835 6540510778997584717954253)
              ·
                refine ⟨2452691542124094269232845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6540510778997584717954253 2452691542124094269232845)
                ·
                  refine ⟨919759328296535350962317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2452691542124094269232845 919759328296535350962317)
                  ·
                    refine ⟨344909748111200756610869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 919759328296535350962317 344909748111200756610869)
                    ·
                      rfl

theorem cell22_1007564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_1007564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007564 prefixEnd_1007564 := by exact prefixLift 1007564
  have htrace : WordTrace (prefixWord ++ tailWord_1007564) baseStart_1007564 baseEnd_1007564 := by
    simpa [prefixWord, tailWord_1007564, baseEnd_1007564] using wordTrace_append hprefix tailTrace_1007564
  have hstable : (prefixWord ++ tailWord_1007564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007564).length < 2 ^ (prefixWord ++ tailWord_1007564).sum := by decide
  have hdescent : baseEnd_1007564 < baseStart_1007564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007598 : List Nat := [4, 1, 2, 1, 3, 1, 3, 3, 1, 3]
def baseStart_1007598 : Nat := 118140960795 + 1007598 * 2 ^ 59
def prefixEnd_1007598 : Nat := 4983230072969 + 3 ^ 40 * 1007598 * 2
def baseEnd_1007598 : Nat := 344921387006036001260765

theorem tailTrace_1007598 : CollatzResearch.WordTrace tailWord_1007598 prefixEnd_1007598 344921387006036001260765 := by
  unfold tailWord_1007598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4593764775456500610399931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24500078802434669922132965 4593764775456500610399931)
  ·
    refine ⟨6890647163184750915599897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4593764775456500610399931 6890647163184750915599897)
    ·
      refine ⟨5167985372388563186699923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6890647163184750915599897 5167985372388563186699923)
      ·
        refine ⟨7751978058582844780049885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5167985372388563186699923 7751978058582844780049885)
        ·
          refine ⟨2906991771968566792518707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7751978058582844780049885 2906991771968566792518707)
          ·
            refine ⟨4360487657952850188778061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2906991771968566792518707 4360487657952850188778061)
            ·
              refine ⟨1635182871732318820791773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4360487657952850188778061 1635182871732318820791773)
              ·
                refine ⟨613193576899619557796915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1635182871732318820791773 613193576899619557796915)
                ·
                  refine ⟨919790365349429336695373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 613193576899619557796915 919790365349429336695373)
                  ·
                    refine ⟨344921387006036001260765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 919790365349429336695373 344921387006036001260765)
                    ·
                      rfl

theorem cell22_1007598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_1007598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007598 prefixEnd_1007598 := by exact prefixLift 1007598
  have htrace : WordTrace (prefixWord ++ tailWord_1007598) baseStart_1007598 baseEnd_1007598 := by
    simpa [prefixWord, tailWord_1007598, baseEnd_1007598] using wordTrace_append hprefix tailTrace_1007598
  have hstable : (prefixWord ++ tailWord_1007598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007598).length < 2 ^ (prefixWord ++ tailWord_1007598).sum := by decide
  have hdescent : baseEnd_1007598 < baseStart_1007598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007658 : List Nat := [3, 1, 4, 1, 2, 2, 3, 1, 1, 4]
def baseStart_1007658 : Nat := 118140960795 + 1007658 * 2 ^ 59
def prefixEnd_1007658 : Nat := 4983230072969 + 3 ^ 40 * 1007658 * 2
def baseEnd_1007658 : Nat := 344941926232215844760581

theorem tailTrace_1007658 : CollatzResearch.WordTrace tailWord_1007658 prefixEnd_1007658 344941926232215844760581 := by
  unfold tailWord_1007658
  simp only [CollatzResearch.WordTrace]
  refine ⟨9188076645858658782595907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24501537722289756753589085 9188076645858658782595907)
  ·
    refine ⟨13782114968787988173893861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9188076645858658782595907 13782114968787988173893861)
    ·
      refine ⟨2584146556647747782605099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13782114968787988173893861 2584146556647747782605099)
      ·
        refine ⟨3876219834971621673907649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2584146556647747782605099 3876219834971621673907649)
        ·
          refine ⟨2907164876228716255430737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3876219834971621673907649 2907164876228716255430737)
          ·
            refine ⟨2180373657171537191573053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2907164876228716255430737 2180373657171537191573053)
            ·
              refine ⟨817640121439326446839895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2180373657171537191573053 817640121439326446839895)
              ·
                refine ⟨1226460182158989670259843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817640121439326446839895 1226460182158989670259843)
                ·
                  refine ⟨1839690273238484505389765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1226460182158989670259843 1839690273238484505389765)
                  ·
                    refine ⟨344941926232215844760581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1839690273238484505389765 344941926232215844760581)
                    ·
                      rfl

theorem cell22_1007658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_1007658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007658 prefixEnd_1007658 := by exact prefixLift 1007658
  have htrace : WordTrace (prefixWord ++ tailWord_1007658) baseStart_1007658 baseEnd_1007658 := by
    simpa [prefixWord, tailWord_1007658, baseEnd_1007658] using wordTrace_append hprefix tailTrace_1007658
  have hstable : (prefixWord ++ tailWord_1007658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007658).length < 2 ^ (prefixWord ++ tailWord_1007658).sum := by decide
  have hdescent : baseEnd_1007658 < baseStart_1007658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007669 : List Nat := [1, 3, 3, 1, 1, 1, 4, 2, 2, 4]
def baseStart_1007669 : Nat := 118140960795 + 1007669 * 2 ^ 59
def prefixEnd_1007669 : Nat := 4983230072969 + 3 ^ 40 * 1007669 * 2
def baseEnd_1007669 : Nat := 344945691757015482735547

theorem tailTrace_1007669 : CollatzResearch.WordTrace tailWord_1007669 prefixEnd_1007669 344945691757015482735547 := by
  unfold tailWord_1007669
  simp only [CollatzResearch.WordTrace]
  refine ⟨36752707786394784009034061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24501805190929856006022707 36752707786394784009034061)
  ·
    refine ⟨13782265419898044003387773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36752707786394784009034061 13782265419898044003387773)
    ·
      refine ⟨5168349532461766501270415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13782265419898044003387773 5168349532461766501270415)
      ·
        refine ⟨7752524298692649751905623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5168349532461766501270415 7752524298692649751905623)
        ·
          refine ⟨11628786448038974627858435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7752524298692649751905623 11628786448038974627858435)
          ·
            refine ⟨17443179672058461941787653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11628786448038974627858435 17443179672058461941787653)
            ·
              refine ⟨3270596188510961614085185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17443179672058461941787653 3270596188510961614085185)
              ·
                refine ⟨2452947141383221210563889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3270596188510961614085185 2452947141383221210563889)
                ·
                  refine ⟨1839710356037415907922917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2452947141383221210563889 1839710356037415907922917)
                  ·
                    refine ⟨344945691757015482735547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1839710356037415907922917 344945691757015482735547)
                    ·
                      rfl

theorem cell22_1007669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_1007669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007669 prefixEnd_1007669 := by exact prefixLift 1007669
  have htrace : WordTrace (prefixWord ++ tailWord_1007669) baseStart_1007669 baseEnd_1007669 := by
    simpa [prefixWord, tailWord_1007669, baseEnd_1007669] using wordTrace_append hprefix tailTrace_1007669
  have hstable : (prefixWord ++ tailWord_1007669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007669).length < 2 ^ (prefixWord ++ tailWord_1007669).sum := by decide
  have hdescent : baseEnd_1007669 < baseStart_1007669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007686 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_1007686 : Nat := 118140960795 + 1007686 * 2 ^ 59
def prefixEnd_1007686 : Nat := 4983230072969 + 3 ^ 40 * 1007686 * 2
def baseEnd_1007686 : Nat := 344951511204433105060495

theorem tailTrace_1007686 : CollatzResearch.WordTrace tailWord_1007686 prefixEnd_1007686 344951511204433105060495 := by
  unfold tailWord_1007686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1148541494604162372262591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24502218551555463941601941 1148541494604162372262591)
  ·
    refine ⟨1722812241906243558393887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1148541494604162372262591 1722812241906243558393887)
    ·
      refine ⟨2584218362859365337590831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1722812241906243558393887 2584218362859365337590831)
      ·
        refine ⟨3876327544289048006386247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2584218362859365337590831 3876327544289048006386247)
        ·
          refine ⟨5814491316433572009579371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3876327544289048006386247 5814491316433572009579371)
          ·
            refine ⟨8721736974650358014369057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5814491316433572009579371 8721736974650358014369057)
            ·
              refine ⟨6541302730987768510776793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8721736974650358014369057 6541302730987768510776793)
              ·
                refine ⟨4905977048240826383082595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6541302730987768510776793 4905977048240826383082595)
                ·
                  refine ⟨7358965572361239574623893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4905977048240826383082595 7358965572361239574623893)
                  ·
                    refine ⟨344951511204433105060495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7358965572361239574623893 344951511204433105060495)
                    ·
                      rfl

theorem cell22_1007686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_1007686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007686 prefixEnd_1007686 := by exact prefixLift 1007686
  have htrace : WordTrace (prefixWord ++ tailWord_1007686) baseStart_1007686 baseEnd_1007686 := by
    simpa [prefixWord, tailWord_1007686, baseEnd_1007686] using wordTrace_append hprefix tailTrace_1007686
  have hstable : (prefixWord ++ tailWord_1007686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007686).length < 2 ^ (prefixWord ++ tailWord_1007686).sum := by decide
  have hdescent : baseEnd_1007686 < baseStart_1007686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007697 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 4, 6]
def baseStart_1007697 : Nat := 118140960795 + 1007697 * 2 ^ 59
def prefixEnd_1007697 : Nat := 4983230072969 + 3 ^ 40 * 1007697 * 2
def baseEnd_1007697 : Nat := 344955276729232743035461

theorem tailTrace_1007697 : CollatzResearch.WordTrace tailWord_1007697 prefixEnd_1007697 344955276729232743035461 := by
  unfold tailWord_1007697
  simp only [CollatzResearch.WordTrace]
  refine ⟨36753729030293344791053345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24502486020195563194035563 36753729030293344791053345)
  ·
    refine ⟨27565296772720008593290009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36753729030293344791053345 27565296772720008593290009)
    ·
      refine ⟨20673972579540006444967507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27565296772720008593290009 20673972579540006444967507)
      ·
        refine ⟨31010958869310009667451261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20673972579540006444967507 31010958869310009667451261)
        ·
          refine ⟨11629109575991253625294223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31010958869310009667451261 11629109575991253625294223)
          ·
            refine ⟨17443664363986880437941335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11629109575991253625294223 17443664363986880437941335)
            ·
              refine ⟨26165496545980320656912003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17443664363986880437941335 26165496545980320656912003)
              ·
                refine ⟨39248244818970480985368005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26165496545980320656912003 39248244818970480985368005)
                ·
                  refine ⟨7359045903556965184756501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39248244818970480985368005 7359045903556965184756501)
                  ·
                    refine ⟨344955276729232743035461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7359045903556965184756501 344955276729232743035461)
                    ·
                      rfl

theorem cell22_1007697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_1007697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007697 prefixEnd_1007697 := by exact prefixLift 1007697
  have htrace : WordTrace (prefixWord ++ tailWord_1007697) baseStart_1007697 baseEnd_1007697 := by
    simpa [prefixWord, tailWord_1007697, baseEnd_1007697] using wordTrace_append hprefix tailTrace_1007697
  have hstable : (prefixWord ++ tailWord_1007697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007697).length < 2 ^ (prefixWord ++ tailWord_1007697).sum := by decide
  have hdescent : baseEnd_1007697 < baseStart_1007697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007767 : List Nat := [1, 1, 3, 3, 5, 1, 1, 3, 1, 3]
def baseStart_1007767 : Nat := 118140960795 + 1007767 * 2 ^ 59
def prefixEnd_1007767 : Nat := 4983230072969 + 3 ^ 40 * 1007767 * 2
def baseEnd_1007767 : Nat := 344979239159775893785247

theorem tailTrace_1007767 : CollatzResearch.WordTrace tailWord_1007767 prefixEnd_1007767 344979239159775893785247 := by
  unfold tailWord_1007767
  simp only [CollatzResearch.WordTrace]
  refine ⟨36756282140039746746101555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24504188093359831164067703 36756282140039746746101555)
  ·
    refine ⟨55134423210059620119152333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36756282140039746746101555 55134423210059620119152333)
    ·
      refine ⟨20675408703772357544682125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55134423210059620119152333 20675408703772357544682125)
      ·
        refine ⟨7753278263914634079255797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20675408703772357544682125 7753278263914634079255797)
        ·
          refine ⟨726869837241996944930231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7753278263914634079255797 726869837241996944930231)
          ·
            refine ⟨1090304755862995417395347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726869837241996944930231 1090304755862995417395347)
            ·
              refine ⟨1635457133794493126093021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090304755862995417395347 1635457133794493126093021)
              ·
                refine ⟨613296425172934922284883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1635457133794493126093021 613296425172934922284883)
                ·
                  refine ⟨919944637759402383427325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 613296425172934922284883 919944637759402383427325)
                  ·
                    refine ⟨344979239159775893785247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 919944637759402383427325 344979239159775893785247)
                    ·
                      rfl

theorem cell22_1007767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 1, 3].length) (baseStart_1007767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007767 prefixEnd_1007767 := by exact prefixLift 1007767
  have htrace : WordTrace (prefixWord ++ tailWord_1007767) baseStart_1007767 baseEnd_1007767 := by
    simpa [prefixWord, tailWord_1007767, baseEnd_1007767] using wordTrace_append hprefix tailTrace_1007767
  have hstable : (prefixWord ++ tailWord_1007767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007767).length < 2 ^ (prefixWord ++ tailWord_1007767).sum := by decide
  have hdescent : baseEnd_1007767 < baseStart_1007767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007776 : List Nat := [2, 1, 1, 4, 2, 2, 2, 3, 1, 4]
def baseStart_1007776 : Nat := 118140960795 + 1007776 * 2 ^ 59
def prefixEnd_1007776 : Nat := 4983230072969 + 3 ^ 40 * 1007776 * 2
def baseEnd_1007776 : Nat := 344982320043702870310219

theorem tailTrace_1007776 : CollatzResearch.WordTrace tailWord_1007776 prefixEnd_1007776 344982320043702870310219 := by
  unfold tailWord_1007776
  simp only [CollatzResearch.WordTrace]
  refine ⟨18378305198503570641589591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24504406931338094188786121 18378305198503570641589591)
  ·
    refine ⟨27567457797755355962384387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18378305198503570641589591 27567457797755355962384387)
    ·
      refine ⟨41351186696633033943576581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27567457797755355962384387 41351186696633033943576581)
      ·
        refine ⟨7753347505618693864420609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41351186696633033943576581 7753347505618693864420609)
        ·
          refine ⟨5815010629214020398315457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7753347505618693864420609 5815010629214020398315457)
          ·
            refine ⟨4361257971910515298736593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5815010629214020398315457 4361257971910515298736593)
            ·
              refine ⟨3270943478932886474052445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4361257971910515298736593 3270943478932886474052445)
              ·
                refine ⟨1226603804599832427769667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3270943478932886474052445 1226603804599832427769667)
                ·
                  refine ⟨1839905706899748641654501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1226603804599832427769667 1839905706899748641654501)
                  ·
                    refine ⟨344982320043702870310219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1839905706899748641654501 344982320043702870310219)
                    ·
                      rfl

theorem cell22_1007776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 1, 4].length) (baseStart_1007776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007776 prefixEnd_1007776 := by exact prefixLift 1007776
  have htrace : WordTrace (prefixWord ++ tailWord_1007776) baseStart_1007776 baseEnd_1007776 := by
    simpa [prefixWord, tailWord_1007776, baseEnd_1007776] using wordTrace_append hprefix tailTrace_1007776
  have hstable : (prefixWord ++ tailWord_1007776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007776).length < 2 ^ (prefixWord ++ tailWord_1007776).sum := by decide
  have hdescent : baseEnd_1007776 < baseStart_1007776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007797 : List Nat := [1, 3, 3, 4, 2, 1, 2, 1, 5]
def baseStart_1007797 : Nat := 118140960795 + 1007797 * 2 ^ 59
def prefixEnd_1007797 : Nat := 4983230072969 + 3 ^ 40 * 1007797 * 2
def baseEnd_1007797 : Nat := 114996502924288605178385

theorem tailTrace_1007797 : CollatzResearch.WordTrace tailWord_1007797 prefixEnd_1007797 114996502924288605178385 := by
  unfold tailWord_1007797
  simp only [CollatzResearch.WordTrace]
  refine ⟨36757376329931061869693645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24504917553287374579795763 36757376329931061869693645)
  ·
    refine ⟨13784016123724148201135117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36757376329931061869693645 13784016123724148201135117)
    ·
      refine ⟨5169006046396555575425669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13784016123724148201135117 5169006046396555575425669)
      ·
        refine ⟨969188633699354170392313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5169006046396555575425669 969188633699354170392313)
        ·
          refine ⟨726891475274515627794235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 969188633699354170392313 726891475274515627794235)
          ·
            refine ⟨1090337212911773441691353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726891475274515627794235 1090337212911773441691353)
            ·
              refine ⟨817752909683830081268515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1090337212911773441691353 817752909683830081268515)
              ·
                refine ⟨1226629364525745121902773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817752909683830081268515 1226629364525745121902773)
                ·
                  refine ⟨114996502924288605178385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1226629364525745121902773 114996502924288605178385)
                  ·
                    rfl

theorem cell22_1007797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 5].length) (baseStart_1007797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007797 prefixEnd_1007797 := by exact prefixLift 1007797
  have htrace : WordTrace (prefixWord ++ tailWord_1007797) baseStart_1007797 baseEnd_1007797 := by
    simpa [prefixWord, tailWord_1007797, baseEnd_1007797] using wordTrace_append hprefix tailTrace_1007797
  have hstable : (prefixWord ++ tailWord_1007797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007797).length < 2 ^ (prefixWord ++ tailWord_1007797).sum := by decide
  have hdescent : baseEnd_1007797 < baseStart_1007797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007810 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1007810 : Nat := 118140960795 + 1007810 * 2 ^ 59
def prefixEnd_1007810 : Nat := 4983230072969 + 3 ^ 40 * 1007810 * 2
def baseEnd_1007810 : Nat := 344993958938538114960115

theorem tailTrace_1007810 : CollatzResearch.WordTrace tailWord_1007810 prefixEnd_1007810 344993958938538114960115 := by
  unfold tailWord_1007810
  simp only [CollatzResearch.WordTrace]
  refine ⟨9189462619720991272479221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24505233652589310059944589 9189462619720991272479221)
  ·
    refine ⟨861512120598842931794927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9189462619720991272479221 861512120598842931794927)
    ·
      refine ⟨1292268180898264397692391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 861512120598842931794927 1292268180898264397692391)
      ·
        refine ⟨1938402271347396596538587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1292268180898264397692391 1938402271347396596538587)
        ·
          refine ⟨2907603407021094894807881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1938402271347396596538587 2907603407021094894807881)
          ·
            refine ⟨2180702555265821171105911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2907603407021094894807881 2180702555265821171105911)
            ·
              refine ⟨3271053832898731756658867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2180702555265821171105911 3271053832898731756658867)
              ·
                refine ⟨4906580749348097634988301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3271053832898731756658867 4906580749348097634988301)
                ·
                  refine ⟨1839967781005536613120613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4906580749348097634988301 1839967781005536613120613)
                  ·
                    refine ⟨344993958938538114960115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1839967781005536613120613 344993958938538114960115)
                    ·
                      rfl

theorem cell22_1007810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1007810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007810 prefixEnd_1007810 := by exact prefixLift 1007810
  have htrace : WordTrace (prefixWord ++ tailWord_1007810) baseStart_1007810 baseEnd_1007810 := by
    simpa [prefixWord, tailWord_1007810, baseEnd_1007810] using wordTrace_append hprefix tailTrace_1007810
  have hstable : (prefixWord ++ tailWord_1007810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007810).length < 2 ^ (prefixWord ++ tailWord_1007810).sum := by decide
  have hdescent : baseEnd_1007810 < baseStart_1007810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007836 : List Nat := [2, 2, 5, 2, 11]
def baseStart_1007836 : Nat := 118140960795 + 1007836 * 2 ^ 59
def prefixEnd_1007836 : Nat := 4983230072969 + 3 ^ 40 * 1007836 * 2
def baseEnd_1007836 : Nat := 1419764852962480303745

theorem tailTrace_1007836 : CollatzResearch.WordTrace tailWord_1007836 prefixEnd_1007836 1419764852962480303745 := by
  unfold tailWord_1007836
  simp only [CollatzResearch.WordTrace]
  refine ⟨18379399388394885765181681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24505865851193181020242241 18379399388394885765181681)
  ·
    refine ⟨13784549541296164323886261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18379399388394885765181681 13784549541296164323886261)
    ·
      refine ⟨1292301519496515405364337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13784549541296164323886261 1292301519496515405364337)
      ·
        refine ⟨969226139622386554023253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1292301519496515405364337 969226139622386554023253)
        ·
          refine ⟨1419764852962480303745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 969226139622386554023253 1419764852962480303745)
          ·
            rfl

theorem cell22_1007836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 11].length) (baseStart_1007836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007836 prefixEnd_1007836 := by exact prefixLift 1007836
  have htrace : WordTrace (prefixWord ++ tailWord_1007836) baseStart_1007836 baseEnd_1007836 := by
    simpa [prefixWord, tailWord_1007836, baseEnd_1007836] using wordTrace_append hprefix tailTrace_1007836
  have hstable : (prefixWord ++ tailWord_1007836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007836).length < 2 ^ (prefixWord ++ tailWord_1007836).sum := by decide
  have hdescent : baseEnd_1007836 < baseStart_1007836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007851 : List Nat := [1, 1, 1, 1, 2, 5, 2, 3, 3, 3]
def baseStart_1007851 : Nat := 118140960795 + 1007851 * 2 ^ 59
def prefixEnd_1007851 : Nat := 4983230072969 + 3 ^ 40 * 1007851 * 2
def baseEnd_1007851 : Nat := 345007994076427674684989

theorem tailTrace_1007851 : CollatzResearch.WordTrace tailWord_1007851 prefixEnd_1007851 345007994076427674684989 := by
  unfold tailWord_1007851
  simp only [CollatzResearch.WordTrace]
  refine ⟨36759345871735429092159407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24506230581156952728106271 36759345871735429092159407)
  ·
    refine ⟨55139018807603143638239111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36759345871735429092159407 55139018807603143638239111)
    ·
      refine ⟨82708528211404715457358667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55139018807603143638239111 82708528211404715457358667)
      ·
        refine ⟨124062792317107073186038001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82708528211404715457358667 124062792317107073186038001)
        ·
          refine ⟨93047094237830304889528501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124062792317107073186038001 93047094237830304889528501)
          ·
            refine ⟨8723165084796591083393297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93047094237830304889528501 8723165084796591083393297)
            ·
              refine ⟨6542373813597443312544973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8723165084796591083393297 6542373813597443312544973)
              ·
                refine ⟨2453390180099041242204365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6542373813597443312544973 2453390180099041242204365)
                ·
                  refine ⟨920021317537140465826637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2453390180099041242204365 920021317537140465826637)
                  ·
                    refine ⟨345007994076427674684989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 920021317537140465826637 345007994076427674684989)
                    ·
                      rfl

theorem cell22_1007851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 3].length) (baseStart_1007851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007851 prefixEnd_1007851 := by exact prefixLift 1007851
  have htrace : WordTrace (prefixWord ++ tailWord_1007851) baseStart_1007851 baseEnd_1007851 := by
    simpa [prefixWord, tailWord_1007851, baseEnd_1007851] using wordTrace_append hprefix tailTrace_1007851
  have hstable : (prefixWord ++ tailWord_1007851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007851).length < 2 ^ (prefixWord ++ tailWord_1007851).sum := by decide
  have hdescent : baseEnd_1007851 < baseStart_1007851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007853 : List Nat := [1, 5, 1, 2, 3, 2, 1, 7]
def baseStart_1007853 : Nat := 118140960795 + 1007853 * 2 ^ 59
def prefixEnd_1007853 : Nat := 4983230072969 + 3 ^ 40 * 1007853 * 2
def baseEnd_1007853 : Nat := 38334297635255592903887

theorem tailTrace_1007853 : CollatzResearch.WordTrace tailWord_1007853 prefixEnd_1007853 38334297635255592903887 := by
  unfold tailWord_1007853
  simp only [CollatzResearch.WordTrace]
  refine ⟨36759418817728183433732213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24506279211818788955821475 36759418817728183433732213)
  ·
    refine ⟨3446195514162017196912395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36759418817728183433732213 3446195514162017196912395)
    ·
      refine ⟨5169293271243025795368593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3446195514162017196912395 5169293271243025795368593)
      ·
        refine ⟨3876969953432269346526445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5169293271243025795368593 3876969953432269346526445)
        ·
          refine ⟨1453863732537101004947417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3876969953432269346526445 1453863732537101004947417)
          ·
            refine ⟨1090397799402825753710563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1453863732537101004947417 1090397799402825753710563)
            ·
              refine ⟨1635596699104238630565845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090397799402825753710563 1635596699104238630565845)
              ·
                refine ⟨38334297635255592903887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1635596699104238630565845 38334297635255592903887)
                ·
                  rfl

theorem cell22_1007853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 7].length) (baseStart_1007853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007853 prefixEnd_1007853 := by exact prefixLift 1007853
  have htrace : WordTrace (prefixWord ++ tailWord_1007853) baseStart_1007853 baseEnd_1007853 := by
    simpa [prefixWord, tailWord_1007853, baseEnd_1007853] using wordTrace_append hprefix tailTrace_1007853
  have hstable : (prefixWord ++ tailWord_1007853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007853).length < 2 ^ (prefixWord ++ tailWord_1007853).sum := by decide
  have hdescent : baseEnd_1007853 < baseStart_1007853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007868 : List Nat := [2, 2, 2, 1, 4, 2, 1, 2, 3, 3]
def baseStart_1007868 : Nat := 118140960795 + 1007868 * 2 ^ 59
def prefixEnd_1007868 : Nat := 4983230072969 + 3 ^ 40 * 1007868 * 2
def baseEnd_1007868 : Nat := 345013813523845297009937

theorem tailTrace_1007868 : CollatzResearch.WordTrace tailWord_1007868 prefixEnd_1007868 345013813523845297009937 := by
  unfold tailWord_1007868
  simp only [CollatzResearch.WordTrace]
  refine ⟨18379982956336920497764129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24506643941782560663685505 18379982956336920497764129)
  ·
    refine ⟨13784987217252690373323097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18379982956336920497764129 13784987217252690373323097)
    ·
      refine ⟨10338740412939517779992323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13784987217252690373323097 10338740412939517779992323)
      ·
        refine ⟨15508110619409276669988485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10338740412939517779992323 15508110619409276669988485)
        ·
          refine ⟨2907770741139239375622841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15508110619409276669988485 2907770741139239375622841)
          ·
            refine ⟨2180828055854429531717131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2907770741139239375622841 2180828055854429531717131)
            ·
              refine ⟨3271242083781644297575697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2180828055854429531717131 3271242083781644297575697)
              ·
                refine ⟨2453431562836233223181773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3271242083781644297575697 2453431562836233223181773)
                ·
                  refine ⟨920036836063587458693165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2453431562836233223181773 920036836063587458693165)
                  ·
                    refine ⟨345013813523845297009937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 920036836063587458693165 345013813523845297009937)
                    ·
                      rfl

theorem cell22_1007868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_1007868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007868 prefixEnd_1007868 := by exact prefixLift 1007868
  have htrace : WordTrace (prefixWord ++ tailWord_1007868) baseStart_1007868 baseEnd_1007868 := by
    simpa [prefixWord, tailWord_1007868, baseEnd_1007868] using wordTrace_append hprefix tailTrace_1007868
  have hstable : (prefixWord ++ tailWord_1007868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007868).length < 2 ^ (prefixWord ++ tailWord_1007868).sum := by decide
  have hdescent : baseEnd_1007868 < baseStart_1007868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007902 : List Nat := [4, 3, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_1007902 : Nat := 118140960795 + 1007902 * 2 ^ 59
def prefixEnd_1007902 : Nat := 4983230072969 + 3 ^ 40 * 1007902 * 2
def baseEnd_1007902 : Nat := 345025452418680541659833

theorem tailTrace_1007902 : CollatzResearch.WordTrace tailWord_1007902 prefixEnd_1007902 345025452418680541659833 := by
  unfold tailWord_1007902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4595150749318833100283245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24507470663033776534843973 4595150749318833100283245)
  ·
    refine ⟨1723181530994562412606217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4595150749318833100283245 1723181530994562412606217)
    ·
      refine ⟨1292386148245921809454663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1723181530994562412606217 1292386148245921809454663)
      ·
        refine ⟨1938579222368882714181995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1292386148245921809454663 1938579222368882714181995)
        ·
          refine ⟨2907868833553324071272993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1938579222368882714181995 2907868833553324071272993)
          ·
            refine ⟨2180901625164993053454745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2907868833553324071272993 2180901625164993053454745)
            ·
              refine ⟨1635676218873744790091059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2180901625164993053454745 1635676218873744790091059)
              ·
                refine ⟨2453514328310617185136589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1635676218873744790091059 2453514328310617185136589)
                ·
                  refine ⟨920067873116481444426221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2453514328310617185136589 920067873116481444426221)
                  ·
                    refine ⟨345025452418680541659833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 920067873116481444426221 345025452418680541659833)
                    ·
                      rfl

theorem cell22_1007902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_1007902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007902 prefixEnd_1007902 := by exact prefixLift 1007902
  have htrace : WordTrace (prefixWord ++ tailWord_1007902) baseStart_1007902 baseEnd_1007902 := by
    simpa [prefixWord, tailWord_1007902, baseEnd_1007902] using wordTrace_append hprefix tailTrace_1007902
  have hstable : (prefixWord ++ tailWord_1007902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007902).length < 2 ^ (prefixWord ++ tailWord_1007902).sum := by decide
  have hdescent : baseEnd_1007902 < baseStart_1007902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007971 : List Nat := [1, 1, 1, 5, 2, 1, 4, 7]
def baseStart_1007971 : Nat := 118140960795 + 1007971 * 2 ^ 59
def prefixEnd_1007971 : Nat := 4983230072969 + 3 ^ 40 * 1007971 * 2
def baseEnd_1007971 : Nat := 38338785836531929076069

theorem tailTrace_1007971 : CollatzResearch.WordTrace tailWord_1007971 prefixEnd_1007971 38338785836531929076069 := by
  unfold tailWord_1007971
  simp only [CollatzResearch.WordTrace]
  refine ⟨36763722631300689586527767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24509148420867126391018511 36763722631300689586527767)
  ·
    refine ⟨55145583946951034379791651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36763722631300689586527767 55145583946951034379791651)
    ·
      refine ⟨82718375920426551569687477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55145583946951034379791651 82718375920426551569687477)
      ·
        refine ⟨7754847742539989209658201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82718375920426551569687477 7754847742539989209658201)
        ·
          refine ⟨5816135806904991907243651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7754847742539989209658201 5816135806904991907243651)
          ·
            refine ⟨8724203710357487860865477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5816135806904991907243651 8724203710357487860865477)
            ·
              refine ⟨1635788195692028973912277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8724203710357487860865477 1635788195692028973912277)
              ·
                refine ⟨38338785836531929076069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1635788195692028973912277 38338785836531929076069)
                ·
                  rfl

theorem cell22_1007971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 7].length) (baseStart_1007971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007971 prefixEnd_1007971 := by exact prefixLift 1007971
  have htrace : WordTrace (prefixWord ++ tailWord_1007971) baseStart_1007971 baseEnd_1007971 := by
    simpa [prefixWord, tailWord_1007971, baseEnd_1007971] using wordTrace_append hprefix tailTrace_1007971
  have hstable : (prefixWord ++ tailWord_1007971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007971).length < 2 ^ (prefixWord ++ tailWord_1007971).sum := by decide
  have hdescent : baseEnd_1007971 < baseStart_1007971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007975 : List Nat := [1, 1, 5, 1, 3, 2, 1, 3, 2, 3]
def baseStart_1007975 : Nat := 118140960795 + 1007975 * 2 ^ 59
def prefixEnd_1007975 : Nat := 4983230072969 + 3 ^ 40 * 1007975 * 2
def baseEnd_1007975 : Nat := 345050441810532684584609

theorem tailTrace_1007975 : CollatzResearch.WordTrace tailWord_1007975 prefixEnd_1007975 345050441810532684584609 := by
  unfold tailWord_1007975
  simp only [CollatzResearch.WordTrace]
  refine ⟨36763868523286198269673379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24509245682190798846448919 36763868523286198269673379)
  ·
    refine ⟨55145802784929297404510069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36763868523286198269673379 55145802784929297404510069)
    ·
      refine ⟨5169919011087121631672819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55145802784929297404510069 5169919011087121631672819)
      ·
        refine ⟨7754878516630682447509229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5169919011087121631672819 7754878516630682447509229)
        ·
          refine ⟨2908079443736505917815961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7754878516630682447509229 2908079443736505917815961)
          ·
            refine ⟨2181059582802379438361971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2908079443736505917815961 2181059582802379438361971)
            ·
              refine ⟨3271589374203569157542957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2181059582802379438361971 3271589374203569157542957)
              ·
                refine ⟨1226846015326338434078609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3271589374203569157542957 1226846015326338434078609)
                ·
                  refine ⟨920134511494753825558957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1226846015326338434078609 920134511494753825558957)
                  ·
                    refine ⟨345050441810532684584609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 920134511494753825558957 345050441810532684584609)
                    ·
                      rfl

theorem cell22_1007975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_1007975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1007975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1007975 prefixEnd_1007975 := by exact prefixLift 1007975
  have htrace : WordTrace (prefixWord ++ tailWord_1007975) baseStart_1007975 baseEnd_1007975 := by
    simpa [prefixWord, tailWord_1007975, baseEnd_1007975] using wordTrace_append hprefix tailTrace_1007975
  have hstable : (prefixWord ++ tailWord_1007975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007975).length < 2 ^ (prefixWord ++ tailWord_1007975).sum := by decide
  have hdescent : baseEnd_1007975 < baseStart_1007975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008108 : List Nat := [2, 2, 1, 1, 2, 1, 4, 3, 2, 4]
def baseStart_1008108 : Nat := 118140960795 + 1008108 * 2 ^ 59
def prefixEnd_1008108 : Nat := 4983230072969 + 3 ^ 40 * 1008108 * 2
def baseEnd_1008108 : Nat := 345095970428564671009201

theorem tailTrace_1008108 : CollatzResearch.WordTrace tailWord_1008108 prefixEnd_1008108 345095970428564671009201 := by
  unfold tailWord_1008108
  simp only [CollatzResearch.WordTrace]
  refine ⟨18384359715902180992132489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24512479621202907989509985 18384359715902180992132489)
  ·
    refine ⟨13788269786926635744099367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18384359715902180992132489 13788269786926635744099367)
    ·
      refine ⟨20682404680389953616149051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13788269786926635744099367 20682404680389953616149051)
      ·
        refine ⟨31023607020584930424223577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20682404680389953616149051 31023607020584930424223577)
        ·
          refine ⟨23267705265438697818167683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31023607020584930424223577 23267705265438697818167683)
          ·
            refine ⟨34901557898158046727251525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23267705265438697818167683 34901557898158046727251525)
            ·
              refine ⟨6544042105904633761359661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34901557898158046727251525 6544042105904633761359661)
              ·
                refine ⟨2454015789714237660509873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6544042105904633761359661 2454015789714237660509873)
                ·
                  refine ⟨1840511842285678245382405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2454015789714237660509873 1840511842285678245382405)
                  ·
                    refine ⟨345095970428564671009201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1840511842285678245382405 345095970428564671009201)
                    ·
                      rfl

theorem cell22_1008108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_1008108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008108 prefixEnd_1008108 := by exact prefixLift 1008108
  have htrace : WordTrace (prefixWord ++ tailWord_1008108) baseStart_1008108 baseEnd_1008108 := by
    simpa [prefixWord, tailWord_1008108, baseEnd_1008108] using wordTrace_append hprefix tailTrace_1008108
  have hstable : (prefixWord ++ tailWord_1008108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008108).length < 2 ^ (prefixWord ++ tailWord_1008108).sum := by decide
  have hdescent : baseEnd_1008108 < baseStart_1008108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008110 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 4, 3]
def baseStart_1008110 : Nat := 118140960795 + 1008110 * 2 ^ 59
def prefixEnd_1008110 : Nat := 4983230072969 + 3 ^ 40 * 1008110 * 2
def baseEnd_1008110 : Nat := 345096655069437332459195

theorem tailTrace_1008110 : CollatzResearch.WordTrace tailWord_1008110 prefixEnd_1008110 345096655069437332459195 := by
  unfold tailWord_1008110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4596099047224639540729723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24512528251864744217225189 4596099047224639540729723)
  ·
    refine ⟨6894148570836959311094585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4596099047224639540729723 6894148570836959311094585)
    ·
      refine ⟨5170611428127719483320939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6894148570836959311094585 5170611428127719483320939)
      ·
        refine ⟨7755917142191579224981409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5170611428127719483320939 7755917142191579224981409)
        ·
          refine ⟨5816937856643684418736057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7755917142191579224981409 5816937856643684418736057)
          ·
            refine ⟨4362703392482763314052043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5816937856643684418736057 4362703392482763314052043)
            ·
              refine ⟨6544055088724144971078065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4362703392482763314052043 6544055088724144971078065)
              ·
                refine ⟨4908041316543108728308549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6544055088724144971078065 4908041316543108728308549)
                ·
                  refine ⟨920257746851832886557853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4908041316543108728308549 920257746851832886557853)
                  ·
                    refine ⟨345096655069437332459195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 920257746851832886557853 345096655069437332459195)
                    ·
                      rfl

theorem cell22_1008110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_1008110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008110 prefixEnd_1008110 := by exact prefixLift 1008110
  have htrace : WordTrace (prefixWord ++ tailWord_1008110) baseStart_1008110 baseEnd_1008110 := by
    simpa [prefixWord, tailWord_1008110, baseEnd_1008110] using wordTrace_append hprefix tailTrace_1008110
  have hstable : (prefixWord ++ tailWord_1008110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008110).length < 2 ^ (prefixWord ++ tailWord_1008110).sum := by decide
  have hdescent : baseEnd_1008110 < baseStart_1008110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008183 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 2, 5]
def baseStart_1008183 : Nat := 118140960795 + 1008183 * 2 ^ 59
def prefixEnd_1008183 : Nat := 4983230072969 + 3 ^ 40 * 1008183 * 2
def baseEnd_1008183 : Nat := 345121644461289475383971

theorem tailTrace_1008183 : CollatzResearch.WordTrace tailWord_1008183 prefixEnd_1008183 345121644461289475383971 := by
  unfold tailWord_1008183
  simp only [CollatzResearch.WordTrace]
  refine ⟨36771454906532649793245203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24514303271021766528830135 36771454906532649793245203)
  ·
    refine ⟨55157182359798974689867805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36771454906532649793245203 55157182359798974689867805)
    ·
      refine ⟨20683943384924615508700427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55157182359798974689867805 20683943384924615508700427)
      ·
        refine ⟨31025915077386923263050641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20683943384924615508700427 31025915077386923263050641)
        ·
          refine ⟨23269436308040192447287981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31025915077386923263050641 23269436308040192447287981)
          ·
            refine ⟨8726038615515072167732993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23269436308040192447287981 8726038615515072167732993)
            ·
              refine ⟨6544528961636304125799745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8726038615515072167732993 6544528961636304125799745)
              ·
                refine ⟨4908396721227228094349809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6544528961636304125799745 4908396721227228094349809)
                ·
                  refine ⟨3681297540920421070762357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4908396721227228094349809 3681297540920421070762357)
                  ·
                    refine ⟨345121644461289475383971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3681297540920421070762357 345121644461289475383971)
                    ·
                      rfl

theorem cell22_1008183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_1008183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008183 prefixEnd_1008183 := by exact prefixLift 1008183
  have htrace : WordTrace (prefixWord ++ tailWord_1008183) baseStart_1008183 baseEnd_1008183 := by
    simpa [prefixWord, tailWord_1008183, baseEnd_1008183] using wordTrace_append hprefix tailTrace_1008183
  have hstable : (prefixWord ++ tailWord_1008183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008183).length < 2 ^ (prefixWord ++ tailWord_1008183).sum := by decide
  have hdescent : baseEnd_1008183 < baseStart_1008183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008185 : List Nat := [1, 2, 1, 5, 1, 1, 4, 2, 5]
def baseStart_1008185 : Nat := 118140960795 + 1008185 * 2 ^ 59
def prefixEnd_1008185 : Nat := 4983230072969 + 3 ^ 40 * 1008185 * 2
def baseEnd_1008185 : Nat := 115040776367387378944655

theorem tailTrace_1008185 : CollatzResearch.WordTrace tailWord_1008185 prefixEnd_1008185 115040776367387378944655 := by
  unfold tailWord_1008185
  simp only [CollatzResearch.WordTrace]
  refine ⟨36771527852525404134818009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24514351901683602756545339 36771527852525404134818009)
  ·
    refine ⟨27578645889394053101113507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36771527852525404134818009 27578645889394053101113507)
    ·
      refine ⟨41367968834091079651670261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27578645889394053101113507 41367968834091079651670261)
      ·
        refine ⟨3878247078196038717344087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41367968834091079651670261 3878247078196038717344087)
        ·
          refine ⟨5817370617294058076016131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3878247078196038717344087 5817370617294058076016131)
          ·
            refine ⟨8726055925941087114024197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5817370617294058076016131 8726055925941087114024197)
            ·
              refine ⟨1636135486113953833879537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8726055925941087114024197 1636135486113953833879537)
              ·
                refine ⟨1227101614585465375409653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636135486113953833879537 1227101614585465375409653)
                ·
                  refine ⟨115040776367387378944655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1227101614585465375409653 115040776367387378944655)
                  ·
                    rfl

theorem cell22_1008185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 5].length) (baseStart_1008185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008185 prefixEnd_1008185 := by exact prefixLift 1008185
  have htrace : WordTrace (prefixWord ++ tailWord_1008185) baseStart_1008185 baseEnd_1008185 := by
    simpa [prefixWord, tailWord_1008185, baseEnd_1008185] using wordTrace_append hprefix tailTrace_1008185
  have hstable : (prefixWord ++ tailWord_1008185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008185).length < 2 ^ (prefixWord ++ tailWord_1008185).sum := by decide
  have hdescent : baseEnd_1008185 < baseStart_1008185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008189 : List Nat := [1, 4, 1, 3, 2, 2, 1, 4, 1, 3]
def baseStart_1008189 : Nat := 118140960795 + 1008189 * 2 ^ 59
def prefixEnd_1008189 : Nat := 4983230072969 + 3 ^ 40 * 1008189 * 2
def baseEnd_1008189 : Nat := 345123698383907459733953

theorem tailTrace_1008189 : CollatzResearch.WordTrace tailWord_1008189 prefixEnd_1008189 345123698383907459733953 := by
  unfold tailWord_1008189
  simp only [CollatzResearch.WordTrace]
  refine ⟨36771673744510912817963621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24514449163007275211975747 36771673744510912817963621)
  ·
    refine ⟨6894688827095796153368179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36771673744510912817963621 6894688827095796153368179)
    ·
      refine ⟨10342033240643694230052269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6894688827095796153368179 10342033240643694230052269)
      ·
        refine ⟨3878262465241385336269601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10342033240643694230052269 3878262465241385336269601)
        ·
          refine ⟨2908696848931039002202201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3878262465241385336269601 2908696848931039002202201)
          ·
            refine ⟨2181522636698279251651651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2908696848931039002202201 2181522636698279251651651)
            ·
              refine ⟨3272283955047418877477477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2181522636698279251651651 3272283955047418877477477)
              ·
                refine ⟨613553241571391039527027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3272283955047418877477477 613553241571391039527027)
                ·
                  refine ⟨920329862357086559290541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 613553241571391039527027 920329862357086559290541)
                  ·
                    refine ⟨345123698383907459733953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 920329862357086559290541 345123698383907459733953)
                    ·
                      rfl

theorem cell22_1008189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_1008189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008189 prefixEnd_1008189 := by exact prefixLift 1008189
  have htrace : WordTrace (prefixWord ++ tailWord_1008189) baseStart_1008189 baseEnd_1008189 := by
    simpa [prefixWord, tailWord_1008189, baseEnd_1008189] using wordTrace_append hprefix tailTrace_1008189
  have hstable : (prefixWord ++ tailWord_1008189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008189).length < 2 ^ (prefixWord ++ tailWord_1008189).sum := by decide
  have hdescent : baseEnd_1008189 < baseStart_1008189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008213 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 8]
def baseStart_1008213 : Nat := 118140960795 + 1008213 * 2 ^ 59
def prefixEnd_1008213 : Nat := 4983230072969 + 3 ^ 40 * 1008213 * 2
def baseEnd_1008213 : Nat := 115043971358126465711293

theorem tailTrace_1008213 : CollatzResearch.WordTrace tailWord_1008213 prefixEnd_1008213 115043971358126465711293 := by
  unfold tailWord_1008213
  simp only [CollatzResearch.WordTrace]
  refine ⟨36772549096423964916837293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24515032730949309944558195 36772549096423964916837293)
  ·
    refine ⟨13789705911158986843813985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36772549096423964916837293 13789705911158986843813985)
    ·
      refine ⟨10342279433369240132860489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13789705911158986843813985 10342279433369240132860489)
      ·
        refine ⟨7756709575026930099645367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10342279433369240132860489 7756709575026930099645367)
        ·
          refine ⟨11635064362540395149468051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7756709575026930099645367 11635064362540395149468051)
          ·
            refine ⟨17452596543810592724202077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11635064362540395149468051 17452596543810592724202077)
            ·
              refine ⟨6544723703928972271575779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17452596543810592724202077 6544723703928972271575779)
              ·
                refine ⟨9817085555893458407363669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6544723703928972271575779 9817085555893458407363669)
                ·
                  refine ⟨115043971358126465711293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9817085555893458407363669 115043971358126465711293)
                  ·
                    rfl

theorem cell22_1008213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_1008213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008213 prefixEnd_1008213 := by exact prefixLift 1008213
  have htrace : WordTrace (prefixWord ++ tailWord_1008213) baseStart_1008213 baseEnd_1008213 := by
    simpa [prefixWord, tailWord_1008213, baseEnd_1008213] using wordTrace_append hprefix tailTrace_1008213
  have hstable : (prefixWord ++ tailWord_1008213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008213).length < 2 ^ (prefixWord ++ tailWord_1008213).sum := by decide
  have hdescent : baseEnd_1008213 < baseStart_1008213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008215 : List Nat := [1, 1, 3, 2, 2, 2, 2, 4, 1, 4]
def baseStart_1008215 : Nat := 118140960795 + 1008215 * 2 ^ 59
def prefixEnd_1008215 : Nat := 4983230072969 + 3 ^ 40 * 1008215 * 2
def baseEnd_1008215 : Nat := 345132598715252058583873

theorem tailTrace_1008215 : CollatzResearch.WordTrace tailWord_1008215 prefixEnd_1008215 345132598715252058583873 := by
  unfold tailWord_1008215
  simp only [CollatzResearch.WordTrace]
  refine ⟨36772622042416719258410099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24515081361611146172273399 36772622042416719258410099)
  ·
    refine ⟨55158933063625078887615149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36772622042416719258410099 55158933063625078887615149)
    ·
      refine ⟨20684599898859404582855681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55158933063625078887615149 20684599898859404582855681)
      ·
        refine ⟨15513449924144553437141761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20684599898859404582855681 15513449924144553437141761)
        ·
          refine ⟨11635087443108415077856321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15513449924144553437141761 11635087443108415077856321)
          ·
            refine ⟨8726315582331311308392241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11635087443108415077856321 8726315582331311308392241)
            ·
              refine ⟨6544736686748483481294181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8726315582331311308392241 6544736686748483481294181)
              ·
                refine ⟨1227138128765340652742659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6544736686748483481294181 1227138128765340652742659)
                ·
                  refine ⟨1840707193148010979113989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227138128765340652742659 1840707193148010979113989)
                  ·
                    refine ⟨345132598715252058583873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1840707193148010979113989 345132598715252058583873)
                    ·
                      rfl

theorem cell22_1008215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_1008215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008215 prefixEnd_1008215 := by exact prefixLift 1008215
  have htrace : WordTrace (prefixWord ++ tailWord_1008215) baseStart_1008215 baseEnd_1008215 := by
    simpa [prefixWord, tailWord_1008215, baseEnd_1008215] using wordTrace_append hprefix tailTrace_1008215
  have hstable : (prefixWord ++ tailWord_1008215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008215).length < 2 ^ (prefixWord ++ tailWord_1008215).sum := by decide
  have hdescent : baseEnd_1008215 < baseStart_1008215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008260 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_1008260 : Nat := 118140960795 + 1008260 * 2 ^ 59
def prefixEnd_1008260 : Nat := 4983230072969 + 3 ^ 40 * 1008260 * 2
def baseEnd_1008260 : Nat := 345148003134886941208735

theorem tailTrace_1008260 : CollatzResearch.WordTrace tailWord_1008260 prefixEnd_1008260 345148003134886941208735 := by
  unfold tailWord_1008260
  simp only [CollatzResearch.WordTrace]
  refine ⟨18387131663626845971899117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24516175551502461295865489 18387131663626845971899117)
  ·
    refine ⟨6895174373860067239462169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18387131663626845971899117 6895174373860067239462169)
    ·
      refine ⟨5171380780395050429596627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6895174373860067239462169 5171380780395050429596627)
      ·
        refine ⟨7757071170592575644394941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5171380780395050429596627 7757071170592575644394941)
        ·
          refine ⟨2908901688972215866648103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7757071170592575644394941 2908901688972215866648103)
          ·
            refine ⟨4363352533458323799972155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2908901688972215866648103 4363352533458323799972155)
            ·
              refine ⟨6545028800187485699958233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4363352533458323799972155 6545028800187485699958233)
              ·
                refine ⟨4908771600140614274968675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6545028800187485699958233 4908771600140614274968675)
                ·
                  refine ⟨7363157400210921412453013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4908771600140614274968675 7363157400210921412453013)
                  ·
                    refine ⟨345148003134886941208735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7363157400210921412453013 345148003134886941208735)
                    ·
                      rfl

theorem cell22_1008260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_1008260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008260 prefixEnd_1008260 := by exact prefixLift 1008260
  have htrace : WordTrace (prefixWord ++ tailWord_1008260) baseStart_1008260 baseEnd_1008260 := by
    simpa [prefixWord, tailWord_1008260, baseEnd_1008260] using wordTrace_append hprefix tailTrace_1008260
  have hstable : (prefixWord ++ tailWord_1008260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008260).length < 2 ^ (prefixWord ++ tailWord_1008260).sum := by decide
  have hdescent : baseEnd_1008260 < baseStart_1008260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008298 : List Nat := [3, 1, 5, 2, 1, 1, 3, 2, 4]
def baseStart_1008298 : Nat := 118140960795 + 1008298 * 2 ^ 59
def prefixEnd_1008298 : Nat := 4983230072969 + 3 ^ 40 * 1008298 * 2
def baseEnd_1008298 : Nat := 115053670437155836252873

theorem tailTrace_1008298 : CollatzResearch.WordTrace tailWord_1008298 prefixEnd_1008298 115053670437155836252873 := by
  unfold tailWord_1008298
  simp only [CollatzResearch.WordTrace]
  refine ⟨9193912325279006108420387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24517099534077349622454365 9193912325279006108420387)
  ·
    refine ⟨13790868487918509162630581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9193912325279006108420387 13790868487918509162630581)
    ·
      refine ⟨1292893920742360233996617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13790868487918509162630581 1292893920742360233996617)
      ·
        refine ⟨969670440556770175497463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1292893920742360233996617 969670440556770175497463)
        ·
          refine ⟨1454505660835155263246195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969670440556770175497463 1454505660835155263246195)
          ·
            refine ⟨2181758491252732894869293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454505660835155263246195 2181758491252732894869293)
            ·
              refine ⟨818159434219774835575985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2181758491252732894869293 818159434219774835575985)
              ·
                refine ⟨613619575664831126681989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 818159434219774835575985 613619575664831126681989)
                ·
                  refine ⟨115053670437155836252873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 613619575664831126681989 115053670437155836252873)
                  ·
                    rfl

theorem cell22_1008298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 4].length) (baseStart_1008298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008298 prefixEnd_1008298 := by exact prefixLift 1008298
  have htrace : WordTrace (prefixWord ++ tailWord_1008298) baseStart_1008298 baseEnd_1008298 := by
    simpa [prefixWord, tailWord_1008298, baseEnd_1008298] using wordTrace_append hprefix tailTrace_1008298
  have hstable : (prefixWord ++ tailWord_1008298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008298).length < 2 ^ (prefixWord ++ tailWord_1008298).sum := by decide
  have hdescent : baseEnd_1008298 < baseStart_1008298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008307 : List Nat := [1, 1, 1, 2, 3, 4, 3, 1, 3, 3]
def baseStart_1008307 : Nat := 118140960795 + 1008307 * 2 ^ 59
def prefixEnd_1008307 : Nat := 4983230072969 + 3 ^ 40 * 1008307 * 2
def baseEnd_1008307 : Nat := 345164092195394485283591

theorem tailTrace_1008307 : CollatzResearch.WordTrace tailWord_1008307 prefixEnd_1008307 345164092195394485283591 := by
  unfold tailWord_1008307
  simp only [CollatzResearch.WordTrace]
  refine ⟨36775977558083418970759175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24517318372055612647172783 36775977558083418970759175)
  ·
    refine ⟨55163966337125128456138763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36775977558083418970759175 55163966337125128456138763)
    ·
      refine ⟨82745949505687692684208145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55163966337125128456138763 82745949505687692684208145)
      ·
        refine ⟨62059462129265769513156109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82745949505687692684208145 62059462129265769513156109)
        ·
          refine ⟨23272298298474663567433541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62059462129265769513156109 23272298298474663567433541)
          ·
            refine ⟨4363555930963999418893789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23272298298474663567433541 4363555930963999418893789)
            ·
              refine ⟨1636333474111499782085171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4363555930963999418893789 1636333474111499782085171)
              ·
                refine ⟨2454500211167249673127757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1636333474111499782085171 2454500211167249673127757)
                ·
                  refine ⟨920437579187718627422909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2454500211167249673127757 920437579187718627422909)
                  ·
                    refine ⟨345164092195394485283591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 920437579187718627422909 345164092195394485283591)
                    ·
                      rfl

theorem cell22_1008307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 3].length) (baseStart_1008307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008307 prefixEnd_1008307 := by exact prefixLift 1008307
  have htrace : WordTrace (prefixWord ++ tailWord_1008307) baseStart_1008307 baseEnd_1008307 := by
    simpa [prefixWord, tailWord_1008307, baseEnd_1008307] using wordTrace_append hprefix tailTrace_1008307
  have hstable : (prefixWord ++ tailWord_1008307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008307).length < 2 ^ (prefixWord ++ tailWord_1008307).sum := by decide
  have hdescent : baseEnd_1008307 < baseStart_1008307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008382 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 8]
def baseStart_1008382 : Nat := 118140960795 + 1008382 * 2 ^ 59
def prefixEnd_1008382 : Nat := 4983230072969 + 3 ^ 40 * 1008382 * 2
def baseEnd_1008382 : Nat := 115063255409373096552787

theorem tailTrace_1008382 : CollatzResearch.WordTrace tailWord_1008382 prefixEnd_1008382 115063255409373096552787 := by
  unfold tailWord_1008382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4597339129101463347467425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24519142021874471186492933 4597339129101463347467425)
  ·
    refine ⟨3448004346826097510600569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4597339129101463347467425 3448004346826097510600569)
    ·
      refine ⟨2586003260119573132950427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3448004346826097510600569 2586003260119573132950427)
      ·
        refine ⟨3879004890179359699425641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2586003260119573132950427 3879004890179359699425641)
        ·
          refine ⟨2909253667634519774569231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3879004890179359699425641 2909253667634519774569231)
          ·
            refine ⟨4363880501451779661853847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2909253667634519774569231 4363880501451779661853847)
            ·
              refine ⟨6545820752177669492780771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4363880501451779661853847 6545820752177669492780771)
              ·
                refine ⟨9818731128266504239171157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6545820752177669492780771 9818731128266504239171157)
                ·
                  refine ⟨115063255409373096552787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9818731128266504239171157 115063255409373096552787)
                  ·
                    rfl

theorem cell22_1008382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_1008382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008382 prefixEnd_1008382 := by exact prefixLift 1008382
  have htrace : WordTrace (prefixWord ++ tailWord_1008382) baseStart_1008382 baseEnd_1008382 := by
    simpa [prefixWord, tailWord_1008382, baseEnd_1008382] using wordTrace_append hprefix tailTrace_1008382
  have hstable : (prefixWord ++ tailWord_1008382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008382).length < 2 ^ (prefixWord ++ tailWord_1008382).sum := by decide
  have hdescent : baseEnd_1008382 < baseStart_1008382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008410 : List Nat := [3, 1, 1, 3, 2, 1, 11]
def baseStart_1008410 : Nat := 118140960795 + 1008410 * 2 ^ 59
def prefixEnd_1008410 : Nat := 4983230072969 + 3 ^ 40 * 1008410 * 2
def baseEnd_1008410 : Nat := 12785161155568020368825

theorem tailTrace_1008410 : CollatzResearch.WordTrace tailWord_1008410 prefixEnd_1008410 12785161155568020368825 := by
  unfold tailWord_1008410
  simp only [CollatzResearch.WordTrace]
  refine ⟨9194933569177566890439671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24519822851140178374505789 9194933569177566890439671)
  ·
    refine ⟨13792400353766350335659507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9194933569177566890439671 13792400353766350335659507)
    ·
      refine ⟨20688600530649525503489261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13792400353766350335659507 20688600530649525503489261)
      ·
        refine ⟨7758225198993572063808473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20688600530649525503489261 7758225198993572063808473)
        ·
          refine ⟨5818668899245179047856355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7758225198993572063808473 5818668899245179047856355)
          ·
            refine ⟨8728003348867768571784533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5818668899245179047856355 8728003348867768571784533)
            ·
              refine ⟨12785161155568020368825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8728003348867768571784533 12785161155568020368825)
              ·
                rfl

theorem cell22_1008410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 11].length) (baseStart_1008410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008410 prefixEnd_1008410 := by exact prefixLift 1008410
  have htrace : WordTrace (prefixWord ++ tailWord_1008410) baseStart_1008410 baseEnd_1008410 := by
    simpa [prefixWord, tailWord_1008410, baseEnd_1008410] using wordTrace_append hprefix tailTrace_1008410
  have hstable : (prefixWord ++ tailWord_1008410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008410).length < 2 ^ (prefixWord ++ tailWord_1008410).sum := by decide
  have hdescent : baseEnd_1008410 < baseStart_1008410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008461 : List Nat := [1, 6, 1, 2, 3, 1, 8]
def baseStart_1008461 : Nat := 118140960795 + 1008461 * 2 ^ 59
def prefixEnd_1008461 : Nat := 4983230072969 + 3 ^ 40 * 1008461 * 2
def baseEnd_1008461 : Nat := 12785807760836645071597

theorem tailTrace_1008461 : CollatzResearch.WordTrace tailWord_1008461 prefixEnd_1008461 12785807760836645071597 := by
  unfold tailWord_1008461
  simp only [CollatzResearch.WordTrace]
  refine ⟨36781594399525503271865237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24521062933017002181243491 36781594399525503271865237)
  ·
    refine ⟨1724137237477757965868683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36781594399525503271865237 1724137237477757965868683)
    ·
      refine ⟨2586205856216636948803025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1724137237477757965868683 2586205856216636948803025)
      ·
        refine ⟨1939654392162477711602269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2586205856216636948803025 1939654392162477711602269)
        ·
          refine ⟨727370397060929141850851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1939654392162477711602269 727370397060929141850851)
          ·
            refine ⟨1091055595591393712776277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727370397060929141850851 1091055595591393712776277)
            ·
              refine ⟨12785807760836645071597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1091055595591393712776277 12785807760836645071597)
              ·
                rfl

theorem cell22_1008461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 8].length) (baseStart_1008461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008461 prefixEnd_1008461 := by exact prefixLift 1008461
  have htrace : WordTrace (prefixWord ++ tailWord_1008461) baseStart_1008461 baseEnd_1008461 := by
    simpa [prefixWord, tailWord_1008461, baseEnd_1008461] using wordTrace_append hprefix tailTrace_1008461
  have hstable : (prefixWord ++ tailWord_1008461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008461).length < 2 ^ (prefixWord ++ tailWord_1008461).sum := by decide
  have hdescent : baseEnd_1008461 < baseStart_1008461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008476 : List Nat := [2, 2, 4, 2, 1, 1, 3, 1, 3, 3]
def baseStart_1008476 : Nat := 118140960795 + 1008476 * 2 ^ 59
def prefixEnd_1008476 : Nat := 4983230072969 + 3 ^ 40 * 1008476 * 2
def baseEnd_1008476 : Nat := 345221944349134377808073

theorem tailTrace_1008476 : CollatzResearch.WordTrace tailWord_1008476 prefixEnd_1008476 345221944349134377808073 := by
  unfold tailWord_1008476
  simp only [CollatzResearch.WordTrace]
  refine ⟨18391070747235580416830641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24521427662980773889107521 18391070747235580416830641)
  ·
    refine ⟨13793303060426685312622981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18391070747235580416830641 13793303060426685312622981)
    ·
      refine ⟨2586244323830003496116809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13793303060426685312622981 2586244323830003496116809)
      ·
        refine ⟨1939683242872502622087607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2586244323830003496116809 1939683242872502622087607)
        ·
          refine ⟨2909524864308753933131411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1939683242872502622087607 2909524864308753933131411)
          ·
            refine ⟨4364287296463130899697117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2909524864308753933131411 4364287296463130899697117)
            ·
              refine ⟨1636607736173674087386419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4364287296463130899697117 1636607736173674087386419)
              ·
                refine ⟨2454911604260511131079629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1636607736173674087386419 2454911604260511131079629)
                ·
                  refine ⟨920591851597691674154861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2454911604260511131079629 920591851597691674154861)
                  ·
                    refine ⟨345221944349134377808073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 920591851597691674154861 345221944349134377808073)
                    ·
                      rfl

theorem cell22_1008476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_1008476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008476 prefixEnd_1008476 := by exact prefixLift 1008476
  have htrace : WordTrace (prefixWord ++ tailWord_1008476) baseStart_1008476 baseEnd_1008476 := by
    simpa [prefixWord, tailWord_1008476, baseEnd_1008476] using wordTrace_append hprefix tailTrace_1008476
  have hstable : (prefixWord ++ tailWord_1008476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008476).length < 2 ^ (prefixWord ++ tailWord_1008476).sum := by decide
  have hdescent : baseEnd_1008476 < baseStart_1008476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008547 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 4, 4]
def baseStart_1008547 : Nat := 118140960795 + 1008547 * 2 ^ 59
def prefixEnd_1008547 : Nat := 4983230072969 + 3 ^ 40 * 1008547 * 2
def baseEnd_1008547 : Nat := 345246249100113859282855

theorem tailTrace_1008547 : CollatzResearch.WordTrace tailWord_1008547 prefixEnd_1008547 345246249100113859282855 := by
  unfold tailWord_1008547
  simp only [CollatzResearch.WordTrace]
  refine ⟨36784731077213939959495895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24523154051475959972997263 36784731077213939959495895)
  ·
    refine ⟨55177096615820909939243843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36784731077213939959495895 55177096615820909939243843)
    ·
      refine ⟨82765644923731364908865765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55177096615820909939243843 82765644923731364908865765)
      ·
        refine ⟨15518558423199630920412331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82765644923731364908865765 15518558423199630920412331)
        ·
          refine ⟨23277837634799446380618497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15518558423199630920412331 23277837634799446380618497)
          ·
            refine ⟨17458378226099584785463873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23277837634799446380618497 17458378226099584785463873)
            ·
              refine ⟨13093783669574688589097905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17458378226099584785463873 13093783669574688589097905)
              ·
                refine ⟨9820337752181016441823429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13093783669574688589097905 9820337752181016441823429)
                ·
                  refine ⟨1841313328533940582841893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9820337752181016441823429 1841313328533940582841893)
                  ·
                    refine ⟨345246249100113859282855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1841313328533940582841893 345246249100113859282855)
                    ·
                      rfl

theorem cell22_1008547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 4].length) (baseStart_1008547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008547 prefixEnd_1008547 := by exact prefixLift 1008547
  have htrace : WordTrace (prefixWord ++ tailWord_1008547) baseStart_1008547 baseEnd_1008547 := by
    simpa [prefixWord, tailWord_1008547, baseEnd_1008547] using wordTrace_append hprefix tailTrace_1008547
  have hstable : (prefixWord ++ tailWord_1008547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008547).length < 2 ^ (prefixWord ++ tailWord_1008547).sum := by decide
  have hdescent : baseEnd_1008547 < baseStart_1008547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008613 : List Nat := [1, 3, 1, 6, 1, 2, 2, 6]
def baseStart_1008613 : Nat := 118140960795 + 1008613 * 2 ^ 59
def prefixEnd_1008613 : Nat := 4983230072969 + 3 ^ 40 * 1008613 * 2
def baseEnd_1008613 : Nat := 38363204694323520792517

theorem tailTrace_1008613 : CollatzResearch.WordTrace tailWord_1008613 prefixEnd_1008613 38363204694323520792517 := by
  unfold tailWord_1008613
  simp only [CollatzResearch.WordTrace]
  refine ⟨36787138294974833231398493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24524758863316555487598995 36787138294974833231398493)
  ·
    refine ⟨13795176860615562461774435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36787138294974833231398493 13795176860615562461774435)
    ·
      refine ⟨20692765290923343692661653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13795176860615562461774435 20692765290923343692661653)
      ·
        refine ⟨969973373012031735593515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20692765290923343692661653 969973373012031735593515)
        ·
          refine ⟨1454960059518047603390273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969973373012031735593515 1454960059518047603390273)
          ·
            refine ⟨1091220044638535702542705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1454960059518047603390273 1091220044638535702542705)
            ·
              refine ⟨818415033478901776907029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1091220044638535702542705 818415033478901776907029)
              ·
                refine ⟨38363204694323520792517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 818415033478901776907029 38363204694323520792517)
                ·
                  rfl

theorem cell22_1008613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 6].length) (baseStart_1008613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008613 prefixEnd_1008613 := by exact prefixLift 1008613
  have htrace : WordTrace (prefixWord ++ tailWord_1008613) baseStart_1008613 baseEnd_1008613 := by
    simpa [prefixWord, tailWord_1008613, baseEnd_1008613] using wordTrace_append hprefix tailTrace_1008613
  have hstable : (prefixWord ++ tailWord_1008613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008613).length < 2 ^ (prefixWord ++ tailWord_1008613).sum := by decide
  have hdescent : baseEnd_1008613 < baseStart_1008613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008671 : List Nat := [1, 1, 2, 4, 1, 3, 3, 2, 1, 4]
def baseStart_1008671 : Nat := 118140960795 + 1008671 * 2 ^ 59
def prefixEnd_1008671 : Nat := 4983230072969 + 3 ^ 40 * 1008671 * 2
def baseEnd_1008671 : Nat := 345288696834218869182475

theorem tailTrace_1008671 : CollatzResearch.WordTrace tailWord_1008671 prefixEnd_1008671 345288696834218869182475 := by
  unfold tailWord_1008671
  simp only [CollatzResearch.WordTrace]
  refine ⟨36789253728764709137009867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24526169152509806091339911 36789253728764709137009867)
  ·
    refine ⟨55183880593147063705514801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36789253728764709137009867 55183880593147063705514801)
    ·
      refine ⟨41387910444860297779136101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55183880593147063705514801 41387910444860297779136101)
      ·
        refine ⟨7760233208411305833588019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41387910444860297779136101 7760233208411305833588019)
        ·
          refine ⟨11640349812616958750382029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7760233208411305833588019 11640349812616958750382029)
          ·
            refine ⟨4365131179731359531393261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11640349812616958750382029 4365131179731359531393261)
            ·
              refine ⟨1636924192399259824272473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4365131179731359531393261 1636924192399259824272473)
              ·
                refine ⟨1227693144299444868204355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636924192399259824272473 1227693144299444868204355)
                ·
                  refine ⟨1841539716449167302306533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227693144299444868204355 1841539716449167302306533)
                  ·
                    refine ⟨345288696834218869182475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1841539716449167302306533 345288696834218869182475)
                    ·
                      rfl

theorem cell22_1008671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 4].length) (baseStart_1008671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008671 prefixEnd_1008671 := by exact prefixLift 1008671
  have htrace : WordTrace (prefixWord ++ tailWord_1008671) baseStart_1008671 baseEnd_1008671 := by
    simpa [prefixWord, tailWord_1008671, baseEnd_1008671] using wordTrace_append hprefix tailTrace_1008671
  have hstable : (prefixWord ++ tailWord_1008671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008671).length < 2 ^ (prefixWord ++ tailWord_1008671).sum := by decide
  have hdescent : baseEnd_1008671 < baseStart_1008671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008684 : List Nat := [2, 2, 1, 1, 1, 2, 5, 2, 1, 5]
def baseStart_1008684 : Nat := 118140960795 + 1008684 * 2 ^ 59
def prefixEnd_1008684 : Nat := 4983230072969 + 3 ^ 40 * 1008684 * 2
def baseEnd_1008684 : Nat := 345293146999891168607435

theorem tailTrace_1008684 : CollatzResearch.WordTrace tailWord_1008684 prefixEnd_1008684 345293146999891168607435 := by
  unfold tailWord_1008684
  simp only [CollatzResearch.WordTrace]
  refine ⟨18394863938858806178616553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24526485251811741571488737 18394863938858806178616553)
  ·
    refine ⟨13796147954144104633962415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18394863938858806178616553 13796147954144104633962415)
    ·
      refine ⟨20694221931216156950943623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13796147954144104633962415 20694221931216156950943623)
      ·
        refine ⟨31041332896824235426415435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20694221931216156950943623 31041332896824235426415435)
        ·
          refine ⟨46561999345236353139623153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31041332896824235426415435 46561999345236353139623153)
          ·
            refine ⟨34921499508927264854717365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46561999345236353139623153 34921499508927264854717365)
            ·
              refine ⟨3273890578961931080129753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34921499508927264854717365 3273890578961931080129753)
              ·
                refine ⟨2455417934221448310097315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3273890578961931080129753 2455417934221448310097315)
                ·
                  refine ⟨3683126901332172465145973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2455417934221448310097315 3683126901332172465145973)
                  ·
                    refine ⟨345293146999891168607435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3683126901332172465145973 345293146999891168607435)
                    ·
                      rfl

theorem cell22_1008684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_1008684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008684 prefixEnd_1008684 := by exact prefixLift 1008684
  have htrace : WordTrace (prefixWord ++ tailWord_1008684) baseStart_1008684 baseEnd_1008684 := by
    simpa [prefixWord, tailWord_1008684, baseEnd_1008684] using wordTrace_append hprefix tailTrace_1008684
  have hstable : (prefixWord ++ tailWord_1008684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008684).length < 2 ^ (prefixWord ++ tailWord_1008684).sum := by decide
  have hdescent : baseEnd_1008684 < baseStart_1008684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008714 : List Nat := [3, 1, 2, 1, 1, 2, 5, 7]
def baseStart_1008714 : Nat := 118140960795 + 1008714 * 2 ^ 59
def prefixEnd_1008714 : Nat := 4983230072969 + 3 ^ 40 * 1008714 * 2
def baseEnd_1008714 : Nat := 38367046290331232261927

theorem tailTrace_1008714 : CollatzResearch.WordTrace tailWord_1008714 prefixEnd_1008714 38367046290331232261927 := by
  unfold tailWord_1008714
  simp only [CollatzResearch.WordTrace]
  refine ⟨9197705516902231870206299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24527214711739284987216797 9197705516902231870206299)
  ·
    refine ⟨13796558275353347805309449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9197705516902231870206299 13796558275353347805309449)
    ·
      refine ⟨10347418706515010853982087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13796558275353347805309449 10347418706515010853982087)
      ·
        refine ⟨15521128059772516280973131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10347418706515010853982087 15521128059772516280973131)
        ·
          refine ⟨23281692089658774421459697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15521128059772516280973131 23281692089658774421459697)
          ·
            refine ⟨17461269067244080816094773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23281692089658774421459697 17461269067244080816094773)
            ·
              refine ⟨1636993975054132576508885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17461269067244080816094773 1636993975054132576508885)
              ·
                refine ⟨38367046290331232261927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1636993975054132576508885 38367046290331232261927)
                ·
                  rfl

theorem cell22_1008714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 7].length) (baseStart_1008714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008714 prefixEnd_1008714 := by exact prefixLift 1008714
  have htrace : WordTrace (prefixWord ++ tailWord_1008714) baseStart_1008714 baseEnd_1008714 := by
    simpa [prefixWord, tailWord_1008714, baseEnd_1008714] using wordTrace_append hprefix tailTrace_1008714
  have hstable : (prefixWord ++ tailWord_1008714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008714).length < 2 ^ (prefixWord ++ tailWord_1008714).sum := by decide
  have hdescent : baseEnd_1008714 < baseStart_1008714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008733 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1008733 : Nat := 118140960795 + 1008733 * 2 ^ 59
def prefixEnd_1008733 : Nat := 4983230072969 + 3 ^ 40 * 1008733 * 2
def baseEnd_1008733 : Nat := 345309920701271374132285

theorem tailTrace_1008733 : CollatzResearch.WordTrace tailWord_1008733 prefixEnd_1008733 345309920701271374132285 := by
  unfold tailWord_1008733
  simp only [CollatzResearch.WordTrace]
  refine ⟨36791515054540093725766853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24527676703026729150511235 36791515054540093725766853)
  ·
    refine ⟨6898409072726267573581285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36791515054540093725766853 6898409072726267573581285)
    ·
      refine ⟨1293451701136175170046491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6898409072726267573581285 1293451701136175170046491)
      ·
        refine ⟨1940177551704262755069737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1293451701136175170046491 1940177551704262755069737)
        ·
          refine ⟨1455133163778197066302303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1940177551704262755069737 1455133163778197066302303)
          ·
            refine ⟨2182699745667295599453455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455133163778197066302303 2182699745667295599453455)
            ·
              refine ⟨3274049618500943399180183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2182699745667295599453455 3274049618500943399180183)
              ·
                refine ⟨4911074427751415098770275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3274049618500943399180183 4911074427751415098770275)
                ·
                  refine ⟨7366611641627122648155413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4911074427751415098770275 7366611641627122648155413)
                  ·
                    refine ⟨345309920701271374132285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7366611641627122648155413 345309920701271374132285)
                    ·
                      rfl

theorem cell22_1008733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1008733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008733 prefixEnd_1008733 := by exact prefixLift 1008733
  have htrace : WordTrace (prefixWord ++ tailWord_1008733) baseStart_1008733 baseEnd_1008733 := by
    simpa [prefixWord, tailWord_1008733, baseEnd_1008733] using wordTrace_append hprefix tailTrace_1008733
  have hstable : (prefixWord ++ tailWord_1008733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008733).length < 2 ^ (prefixWord ++ tailWord_1008733).sum := by decide
  have hdescent : baseEnd_1008733 < baseStart_1008733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008759 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 7]
def baseStart_1008759 : Nat := 118140960795 + 1008759 * 2 ^ 59
def prefixEnd_1008759 : Nat := 4983230072969 + 3 ^ 40 * 1008759 * 2
def baseEnd_1008759 : Nat := 115106273677538657660735

theorem tailTrace_1008759 : CollatzResearch.WordTrace tailWord_1008759 prefixEnd_1008759 115106273677538657660735 := by
  unfold tailWord_1008759
  simp only [CollatzResearch.WordTrace]
  refine ⟨36792463352445900166213331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24528308901630600110808887 36792463352445900166213331)
  ·
    refine ⟨55188695028668850249319997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36792463352445900166213331 55188695028668850249319997)
    ·
      refine ⟨20695760635750818843494999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55188695028668850249319997 20695760635750818843494999)
      ·
        refine ⟨31043640953626228265242499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20695760635750818843494999 31043640953626228265242499)
        ·
          refine ⟨46565461430439342397863749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31043640953626228265242499 46565461430439342397863749)
          ·
            refine ⟨8731024018207376699599453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46565461430439342397863749 8731024018207376699599453)
            ·
              refine ⟨3274134006827766262349795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8731024018207376699599453 3274134006827766262349795)
              ·
                refine ⟨4911201010241649393524693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3274134006827766262349795 4911201010241649393524693)
                ·
                  refine ⟨115106273677538657660735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4911201010241649393524693 115106273677538657660735)
                  ·
                    rfl

theorem cell22_1008759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 7].length) (baseStart_1008759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008759 prefixEnd_1008759 := by exact prefixLift 1008759
  have htrace : WordTrace (prefixWord ++ tailWord_1008759) baseStart_1008759 baseEnd_1008759 := by
    simpa [prefixWord, tailWord_1008759, baseEnd_1008759] using wordTrace_append hprefix tailTrace_1008759
  have hstable : (prefixWord ++ tailWord_1008759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008759).length < 2 ^ (prefixWord ++ tailWord_1008759).sum := by decide
  have hdescent : baseEnd_1008759 < baseStart_1008759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008853 : List Nat := [1, 3, 2, 4, 1, 2, 1, 2, 1, 5]
def baseStart_1008853 : Nat := 118140960795 + 1008853 * 2 ^ 59
def prefixEnd_1008853 : Nat := 4983230072969 + 3 ^ 40 * 1008853 * 2
def baseEnd_1008853 : Nat := 345350999153631061131917

theorem tailTrace_1008853 : CollatzResearch.WordTrace tailWord_1008853 prefixEnd_1008853 345350999153631061131917 := by
  unfold tailWord_1008853
  simp only [CollatzResearch.WordTrace]
  refine ⟨36795891814105354220135213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24530594542736902813423475 36795891814105354220135213)
  ·
    refine ⟨13798459430289507832550705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36795891814105354220135213 13798459430289507832550705)
    ·
      refine ⟨10348844572717130874413029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13798459430289507832550705 10348844572717130874413029)
      ·
        refine ⟨1940408357384462038952443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10348844572717130874413029 1940408357384462038952443)
        ·
          refine ⟨2910612536076693058428665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1940408357384462038952443 2910612536076693058428665)
          ·
            refine ⟨2182959402057519793821499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2910612536076693058428665 2182959402057519793821499)
            ·
              refine ⟨3274439103086279690732249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2182959402057519793821499 3274439103086279690732249)
              ·
                refine ⟨2455829327314709768049187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3274439103086279690732249 2455829327314709768049187)
                ·
                  refine ⟨3683743990972064652073781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2455829327314709768049187 3683743990972064652073781)
                  ·
                    refine ⟨345350999153631061131917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3683743990972064652073781 345350999153631061131917)
                    ·
                      rfl

theorem cell22_1008853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_1008853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008853 prefixEnd_1008853 := by exact prefixLift 1008853
  have htrace : WordTrace (prefixWord ++ tailWord_1008853) baseStart_1008853 baseEnd_1008853 := by
    simpa [prefixWord, tailWord_1008853, baseEnd_1008853] using wordTrace_append hprefix tailTrace_1008853
  have hstable : (prefixWord ++ tailWord_1008853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008853).length < 2 ^ (prefixWord ++ tailWord_1008853).sum := by decide
  have hdescent : baseEnd_1008853 < baseStart_1008853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008928 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 7]
def baseStart_1008928 : Nat := 118140960795 + 1008928 * 2 ^ 59
def prefixEnd_1008928 : Nat := 4983230072969 + 3 ^ 40 * 1008928 * 2
def baseEnd_1008928 : Nat := 115125557728785288502229

theorem tailTrace_1008928 : CollatzResearch.WordTrace tailWord_1008928 prefixEnd_1008928 115125557728785288502229 := by
  unfold tailWord_1008928
  simp only [CollatzResearch.WordTrace]
  refine ⟨18399313644416821014557719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24532418192555761352743625 18399313644416821014557719)
  ·
    refine ⟨27598970466625231521836579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18399313644416821014557719 27598970466625231521836579)
    ·
      refine ⟨41398455699937847282754869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27598970466625231521836579 41398455699937847282754869)
      ·
        refine ⟨3881105221869173182758269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41398455699937847282754869 3881105221869173182758269)
        ·
          refine ⟨1455414458200939943534351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3881105221869173182758269 1455414458200939943534351)
          ·
            refine ⟨2183121687301409915301527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455414458200939943534351 2183121687301409915301527)
            ·
              refine ⟨3274682530952114872952291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183121687301409915301527 3274682530952114872952291)
              ·
                refine ⟨4912023796428172309428437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3274682530952114872952291 4912023796428172309428437)
                ·
                  refine ⟨115125557728785288502229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4912023796428172309428437 115125557728785288502229)
                  ·
                    rfl

theorem cell22_1008928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 7].length) (baseStart_1008928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008928 prefixEnd_1008928 := by exact prefixLift 1008928
  have htrace : WordTrace (prefixWord ++ tailWord_1008928) baseStart_1008928 baseEnd_1008928 := by
    simpa [prefixWord, tailWord_1008928, baseEnd_1008928] using wordTrace_append hprefix tailTrace_1008928
  have hstable : (prefixWord ++ tailWord_1008928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008928).length < 2 ^ (prefixWord ++ tailWord_1008928).sum := by decide
  have hdescent : baseEnd_1008928 < baseStart_1008928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008945 : List Nat := [1, 2, 2, 3, 3, 2, 3, 1, 5]
def baseStart_1008945 : Nat := 118140960795 + 1008945 * 2 ^ 59
def prefixEnd_1008945 : Nat := 4983230072969 + 3 ^ 40 * 1008945 * 2
def baseEnd_1008945 : Nat := 115127497544591162610545

theorem tailTrace_1008945 : CollatzResearch.WordTrace tailWord_1008945 prefixEnd_1008945 115127497544591162610545 := by
  unfold tailWord_1008945
  simp only [CollatzResearch.WordTrace]
  refine ⟨36799247329772053932484289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24532831553181369288322859 36799247329772053932484289)
  ·
    refine ⟨27599435497329040449363217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36799247329772053932484289 27599435497329040449363217)
    ·
      refine ⟨20699576622996780337022413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27599435497329040449363217 20699576622996780337022413)
      ·
        refine ⟨7762341233623792626383405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20699576622996780337022413 7762341233623792626383405)
        ·
          refine ⟨2910877962608922234893777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7762341233623792626383405 2910877962608922234893777)
          ·
            refine ⟨2183158471956691676170333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2910877962608922234893777 2183158471956691676170333)
            ·
              refine ⟨818684426983759378563875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2183158471956691676170333 818684426983759378563875)
              ·
                refine ⟨1228026640475639067845813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 818684426983759378563875 1228026640475639067845813)
                ·
                  refine ⟨115127497544591162610545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1228026640475639067845813 115127497544591162610545)
                  ·
                    rfl

theorem cell22_1008945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 5].length) (baseStart_1008945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1008945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1008945 prefixEnd_1008945 := by exact prefixLift 1008945
  have htrace : WordTrace (prefixWord ++ tailWord_1008945) baseStart_1008945 baseEnd_1008945 := by
    simpa [prefixWord, tailWord_1008945, baseEnd_1008945] using wordTrace_append hprefix tailTrace_1008945
  have hstable : (prefixWord ++ tailWord_1008945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008945).length < 2 ^ (prefixWord ++ tailWord_1008945).sum := by decide
  have hdescent : baseEnd_1008945 < baseStart_1008945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009050 : List Nat := [3, 1, 1, 4, 1, 1, 2, 3, 3, 3]
def baseStart_1009050 : Nat := 118140960795 + 1009050 * 2 ^ 59
def prefixEnd_1009050 : Nat := 4983230072969 + 3 ^ 40 * 1009050 * 2
def baseEnd_1009050 : Nat := 345418436279588213956313

theorem tailTrace_1009050 : CollatzResearch.WordTrace tailWord_1009050 prefixEnd_1009050 345418436279588213956313 := by
  unfold tailWord_1009050
  simp only [CollatzResearch.WordTrace]
  refine ⟨9200769248597914216264151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24535384662927771243371069 9200769248597914216264151)
  ·
    refine ⟨13801153872896871324396227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9200769248597914216264151 13801153872896871324396227)
    ·
      refine ⟨20701730809345306986594341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13801153872896871324396227 20701730809345306986594341)
      ·
        refine ⟨3881574526752245059986439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20701730809345306986594341 3881574526752245059986439)
        ·
          refine ⟨5822361790128367589979659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3881574526752245059986439 5822361790128367589979659)
          ·
            refine ⟨8733542685192551384969489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5822361790128367589979659 8733542685192551384969489)
            ·
              refine ⟨6550157013894413538727117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8733542685192551384969489 6550157013894413538727117)
              ·
                refine ⟨2456308880210405077022669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6550157013894413538727117 2456308880210405077022669)
                ·
                  refine ⟨921115830078901903883501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2456308880210405077022669 921115830078901903883501)
                  ·
                    refine ⟨345418436279588213956313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 921115830078901903883501 345418436279588213956313)
                    ·
                      rfl

theorem cell22_1009050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_1009050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009050 prefixEnd_1009050 := by exact prefixLift 1009050
  have htrace : WordTrace (prefixWord ++ tailWord_1009050) baseStart_1009050 baseEnd_1009050 := by
    simpa [prefixWord, tailWord_1009050, baseEnd_1009050] using wordTrace_append hprefix tailTrace_1009050
  have hstable : (prefixWord ++ tailWord_1009050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009050).length < 2 ^ (prefixWord ++ tailWord_1009050).sum := by decide
  have hdescent : baseEnd_1009050 < baseStart_1009050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009052 : List Nat := [2, 2, 3, 4, 1, 2, 1, 7]
def baseStart_1009052 : Nat := 118140960795 + 1009052 * 2 ^ 59
def prefixEnd_1009052 : Nat := 4983230072969 + 3 ^ 40 * 1009052 * 2
def baseEnd_1009052 : Nat := 38379902324495652822923

theorem tailTrace_1009052 : CollatzResearch.WordTrace tailWord_1009052 prefixEnd_1009052 38379902324495652822923 := by
  unfold tailWord_1009052
  simp only [CollatzResearch.WordTrace]
  refine ⟨18401574970192205603314705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24535433293589607471086273 18401574970192205603314705)
  ·
    refine ⟨13801181227644154202486029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18401574970192205603314705 13801181227644154202486029)
    ·
      refine ⟨5175442960366557825932261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13801181227644154202486029 5175442960366557825932261)
      ·
        refine ⟨970395555068729592362299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5175442960366557825932261 970395555068729592362299)
        ·
          refine ⟨1455593332603094388543449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970395555068729592362299 1455593332603094388543449)
          ·
            refine ⟨1091694999452320791407587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1455593332603094388543449 1091694999452320791407587)
            ·
              refine ⟨1637542499178481187111381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091694999452320791407587 1637542499178481187111381)
              ·
                refine ⟨38379902324495652822923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1637542499178481187111381 38379902324495652822923)
                ·
                  rfl

theorem cell22_1009052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 7].length) (baseStart_1009052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009052 prefixEnd_1009052 := by exact prefixLift 1009052
  have htrace : WordTrace (prefixWord ++ tailWord_1009052) baseStart_1009052 baseEnd_1009052 := by
    simpa [prefixWord, tailWord_1009052, baseEnd_1009052] using wordTrace_append hprefix tailTrace_1009052
  have hstable : (prefixWord ++ tailWord_1009052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009052).length < 2 ^ (prefixWord ++ tailWord_1009052).sum := by decide
  have hdescent : baseEnd_1009052 < baseStart_1009052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009090 : List Nat := [3, 5, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1009090 : Nat := 118140960795 + 1009090 * 2 ^ 59
def prefixEnd_1009090 : Nat := 4983230072969 + 3 ^ 40 * 1009090 * 2
def baseEnd_1009090 : Nat := 345432129097041442956191

theorem tailTrace_1009090 : CollatzResearch.WordTrace tailWord_1009090 prefixEnd_1009090 345432129097041442956191 := by
  unfold tailWord_1009090
  simp only [CollatzResearch.WordTrace]
  refine ⟨9201133978561685924128181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24536357276164495797675149 9201133978561685924128181)
  ·
    refine ⟨862606310490158055387017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9201133978561685924128181 862606310490158055387017)
    ·
      refine ⟨646954732867618541540263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 862606310490158055387017 646954732867618541540263)
      ·
        refine ⟨970432099301427812310395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646954732867618541540263 970432099301427812310395)
        ·
          refine ⟨1455648148952141718465593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970432099301427812310395 1455648148952141718465593)
          ·
            refine ⟨1091736111714106288849195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1455648148952141718465593 1091736111714106288849195)
            ·
              refine ⟨1637604167571159433273793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091736111714106288849195 1637604167571159433273793)
              ·
                refine ⟨1228203125678369574955345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1637604167571159433273793 1228203125678369574955345)
                ·
                  refine ⟨921152344258777181216509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1228203125678369574955345 921152344258777181216509)
                  ·
                    refine ⟨345432129097041442956191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 921152344258777181216509 345432129097041442956191)
                    ·
                      rfl

theorem cell22_1009090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1009090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009090 prefixEnd_1009090 := by exact prefixLift 1009090
  have htrace : WordTrace (prefixWord ++ tailWord_1009090) baseStart_1009090 baseEnd_1009090 := by
    simpa [prefixWord, tailWord_1009090, baseEnd_1009090] using wordTrace_append hprefix tailTrace_1009090
  have hstable : (prefixWord ++ tailWord_1009090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009090).length < 2 ^ (prefixWord ++ tailWord_1009090).sum := by decide
  have hdescent : baseEnd_1009090 < baseStart_1009090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009125 : List Nat := [1, 3, 1, 5, 1, 1, 2, 2, 6]
def baseStart_1009125 : Nat := 118140960795 + 1009125 * 2 ^ 59
def prefixEnd_1009125 : Nat := 4983230072969 + 3 ^ 40 * 1009125 * 2
def baseEnd_1009125 : Nat := 115148036770771006110361

theorem tailTrace_1009125 : CollatzResearch.WordTrace tailWord_1009125 prefixEnd_1009125 115148036770771006110361 := by
  unfold tailWord_1009125
  simp only [CollatzResearch.WordTrace]
  refine ⟨36805812469119944674036829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24537208312746629782691219 36805812469119944674036829)
  ·
    refine ⟨13802179675919979252763811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36805812469119944674036829 13802179675919979252763811)
    ·
      refine ⟨20703269513879968879145717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13802179675919979252763811 20703269513879968879145717)
      ·
        refine ⟨1940931516926247082419911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20703269513879968879145717 1940931516926247082419911)
        ·
          refine ⟨2911397275389370623629867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1940931516926247082419911 2911397275389370623629867)
          ·
            refine ⟨4367095913084055935444801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2911397275389370623629867 4367095913084055935444801)
            ·
              refine ⟨3275321934813041951583601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4367095913084055935444801 3275321934813041951583601)
              ·
                refine ⟨2456491451109781463687701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3275321934813041951583601 2456491451109781463687701)
                ·
                  refine ⟨115148036770771006110361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2456491451109781463687701 115148036770771006110361)
                  ·
                    rfl

theorem cell22_1009125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_1009125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009125 prefixEnd_1009125 := by exact prefixLift 1009125
  have htrace : WordTrace (prefixWord ++ tailWord_1009125) baseStart_1009125 baseEnd_1009125 := by
    simpa [prefixWord, tailWord_1009125, baseEnd_1009125] using wordTrace_append hprefix tailTrace_1009125
  have hstable : (prefixWord ++ tailWord_1009125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009125).length < 2 ^ (prefixWord ++ tailWord_1009125).sum := by decide
  have hdescent : baseEnd_1009125 < baseStart_1009125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009127 : List Nat := [1, 1, 5, 2, 1, 3, 2, 2, 1, 4]
def baseStart_1009127 : Nat := 118140960795 + 1009127 * 2 ^ 59
def prefixEnd_1009127 : Nat := 4983230072969 + 3 ^ 40 * 1009127 * 2
def baseEnd_1009127 : Nat := 345444794953185679781077

theorem tailTrace_1009127 : CollatzResearch.WordTrace tailWord_1009127 prefixEnd_1009127 345444794953185679781077 := by
  unfold tailWord_1009127
  simp only [CollatzResearch.WordTrace]
  refine ⟨36805885415112699015609635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24537256943408466010406423 36805885415112699015609635)
  ·
    refine ⟨55208828122669048523414453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36805885415112699015609635 55208828122669048523414453)
    ·
      refine ⟨5175827636500223299070105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55208828122669048523414453 5175827636500223299070105)
      ·
        refine ⟨3881870727375167474302579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5175827636500223299070105 3881870727375167474302579)
        ·
          refine ⟨5822806091062751211453869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3881870727375167474302579 5822806091062751211453869)
          ·
            refine ⟨2183552284148531704295201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5822806091062751211453869 2183552284148531704295201)
            ·
              refine ⟨1637664213111398778221401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2183552284148531704295201 1637664213111398778221401)
              ·
                refine ⟨1228248159833549083666051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1637664213111398778221401 1228248159833549083666051)
                ·
                  refine ⟨1842372239750323625499077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1228248159833549083666051 1842372239750323625499077)
                  ·
                    refine ⟨345444794953185679781077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1842372239750323625499077 345444794953185679781077)
                    ·
                      rfl

theorem cell22_1009127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_1009127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009127 prefixEnd_1009127 := by exact prefixLift 1009127
  have htrace : WordTrace (prefixWord ++ tailWord_1009127) baseStart_1009127 baseEnd_1009127 := by
    simpa [prefixWord, tailWord_1009127, baseEnd_1009127] using wordTrace_append hprefix tailTrace_1009127
  have hstable : (prefixWord ++ tailWord_1009127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009127).length < 2 ^ (prefixWord ++ tailWord_1009127).sum := by decide
  have hdescent : baseEnd_1009127 < baseStart_1009127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009159 : List Nat := [1, 1, 4, 3, 2, 2, 3, 2, 4]
def baseStart_1009159 : Nat := 118140960795 + 1009159 * 2 ^ 59
def prefixEnd_1009159 : Nat := 4983230072969 + 3 ^ 40 * 1009159 * 2
def baseEnd_1009159 : Nat := 115151916402382754326993

theorem tailTrace_1009159 : CollatzResearch.WordTrace tailWord_1009159 prefixEnd_1009159 115151916402382754326993 := by
  unfold tailWord_1009159
  simp only [CollatzResearch.WordTrace]
  refine ⟨36807052550996768480774531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24538035033997845653849687 36807052550996768480774531)
  ·
    refine ⟨55210578826495152721161797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36807052550996768480774531 55210578826495152721161797)
    ·
      refine ⟨10351983529967841135217837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55210578826495152721161797 10351983529967841135217837)
      ·
        refine ⟨3881993823737940425706689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10351983529967841135217837 3881993823737940425706689)
        ·
          refine ⟨2911495367803455319280017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3881993823737940425706689 2911495367803455319280017)
          ·
            refine ⟨2183621525852591489460013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2911495367803455319280017 2183621525852591489460013)
            ·
              refine ⟨818858072194721808547505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2183621525852591489460013 818858072194721808547505)
              ·
                refine ⟨614143554146041356410629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 818858072194721808547505 614143554146041356410629)
                ·
                  refine ⟨115151916402382754326993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 614143554146041356410629 115151916402382754326993)
                  ·
                    rfl

theorem cell22_1009159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 4].length) (baseStart_1009159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009159 prefixEnd_1009159 := by exact prefixLift 1009159
  have htrace : WordTrace (prefixWord ++ tailWord_1009159) baseStart_1009159 baseEnd_1009159 := by
    simpa [prefixWord, tailWord_1009159, baseEnd_1009159] using wordTrace_append hprefix tailTrace_1009159
  have hstable : (prefixWord ++ tailWord_1009159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009159).length < 2 ^ (prefixWord ++ tailWord_1009159).sum := by decide
  have hdescent : baseEnd_1009159 < baseStart_1009159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009215 : List Nat := [1, 1, 2, 2, 3, 3, 1, 4, 5]
def baseStart_1009215 : Nat := 118140960795 + 1009215 * 2 ^ 59
def prefixEnd_1009215 : Nat := 4983230072969 + 3 ^ 40 * 1009215 * 2
def baseEnd_1009215 : Nat := 115158306383860927860269

theorem tailTrace_1009215 : CollatzResearch.WordTrace tailWord_1009215 prefixEnd_1009215 115158306383860927860269 := by
  unfold tailWord_1009215
  simp only [CollatzResearch.WordTrace]
  refine ⟨36809095038793890044813099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24539396692529260029875399 36809095038793890044813099)
  ·
    refine ⟨55213642558190835067219649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36809095038793890044813099 55213642558190835067219649)
    ·
      refine ⟨41410231918643126300414737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55213642558190835067219649 41410231918643126300414737)
      ·
        refine ⟨31057673938982344725311053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41410231918643126300414737 31057673938982344725311053)
        ·
          refine ⟨11646627727118379271991645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31057673938982344725311053 11646627727118379271991645)
          ·
            refine ⟨4367485397669392226996867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11646627727118379271991645 4367485397669392226996867)
            ·
              refine ⟨6551228096504088340495301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4367485397669392226996867 6551228096504088340495301)
              ·
                refine ⟨1228355268094516563842869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6551228096504088340495301 1228355268094516563842869)
                ·
                  refine ⟨115158306383860927860269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1228355268094516563842869 115158306383860927860269)
                  ·
                    rfl

theorem cell22_1009215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 5].length) (baseStart_1009215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009215 prefixEnd_1009215 := by exact prefixLift 1009215
  have htrace : WordTrace (prefixWord ++ tailWord_1009215) baseStart_1009215 baseEnd_1009215 := by
    simpa [prefixWord, tailWord_1009215, baseEnd_1009215] using wordTrace_append hprefix tailTrace_1009215
  have hstable : (prefixWord ++ tailWord_1009215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009215).length < 2 ^ (prefixWord ++ tailWord_1009215).sum := by decide
  have hdescent : baseEnd_1009215 < baseStart_1009215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009277 : List Nat := [1, 4, 1, 1, 4, 2, 2, 1, 6]
def baseStart_1009277 : Nat := 118140960795 + 1009277 * 2 ^ 59
def prefixEnd_1009277 : Nat := 4983230072969 + 3 ^ 40 * 1009277 * 2
def baseEnd_1009277 : Nat := 115165381006211762843539

theorem tailTrace_1009277 : CollatzResearch.WordTrace tailWord_1009277 prefixEnd_1009277 115165381006211762843539 := by
  unfold tailWord_1009277
  simp only [CollatzResearch.WordTrace]
  refine ⟨36811356364569274633570085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24540904243046183089046723 36811356364569274633570085)
  ·
    refine ⟨6902129318356738993794391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36811356364569274633570085 6902129318356738993794391)
    ·
      refine ⟨10353193977535108490691587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6902129318356738993794391 10353193977535108490691587)
      ·
        refine ⟨15529790966302662736037381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10353193977535108490691587 15529790966302662736037381)
        ·
          refine ⟨2911835806181749263007009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15529790966302662736037381 2911835806181749263007009)
          ·
            refine ⟨2183876854636311947255257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2911835806181749263007009 2183876854636311947255257)
            ·
              refine ⟨1637907640977233960441443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2183876854636311947255257 1637907640977233960441443)
              ·
                refine ⟨2456861461465850940662165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1637907640977233960441443 2456861461465850940662165)
                ·
                  refine ⟨115165381006211762843539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2456861461465850940662165 115165381006211762843539)
                  ·
                    rfl

theorem cell22_1009277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_1009277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009277 prefixEnd_1009277 := by exact prefixLift 1009277
  have htrace : WordTrace (prefixWord ++ tailWord_1009277) baseStart_1009277 baseEnd_1009277 := by
    simpa [prefixWord, tailWord_1009277, baseEnd_1009277] using wordTrace_append hprefix tailTrace_1009277
  have hstable : (prefixWord ++ tailWord_1009277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009277).length < 2 ^ (prefixWord ++ tailWord_1009277).sum := by decide
  have hdescent : baseEnd_1009277 < baseStart_1009277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009384 : List Nat := [2, 1, 4, 1, 3, 2, 2, 2, 5]
def baseStart_1009384 : Nat := 118140960795 + 1009384 * 2 ^ 59
def prefixEnd_1009384 : Nat := 4983230072969 + 3 ^ 40 * 1009384 * 2
def baseEnd_1009384 : Nat := 115177590435107558701763

theorem tailTrace_1009384 : CollatzResearch.WordTrace tailWord_1009384 prefixEnd_1009384 115177590435107558701763 := by
  unfold tailWord_1009384
  simp only [CollatzResearch.WordTrace]
  refine ⟨18407629487590815953857603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24543505983454421271810137 18407629487590815953857603)
  ·
    refine ⟨27611444231386223930786405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18407629487590815953857603 27611444231386223930786405)
    ·
      refine ⟨5177145793384916987022451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27611444231386223930786405 5177145793384916987022451)
      ·
        refine ⟨7765718690077375480533677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5177145793384916987022451 7765718690077375480533677)
        ·
          refine ⟨2912144508779015805200129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7765718690077375480533677 2912144508779015805200129)
          ·
            refine ⟨2184108381584261853900097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2912144508779015805200129 2184108381584261853900097)
            ·
              refine ⟨1638081286188196390425073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2184108381584261853900097 1638081286188196390425073)
              ·
                refine ⟨1228560964641147292818805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1638081286188196390425073 1228560964641147292818805)
                ·
                  refine ⟨115177590435107558701763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1228560964641147292818805 115177590435107558701763)
                  ·
                    rfl

theorem cell22_1009384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 5].length) (baseStart_1009384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009384 prefixEnd_1009384 := by exact prefixLift 1009384
  have htrace : WordTrace (prefixWord ++ tailWord_1009384) baseStart_1009384 baseEnd_1009384 := by
    simpa [prefixWord, tailWord_1009384, baseEnd_1009384] using wordTrace_append hprefix tailTrace_1009384
  have hstable : (prefixWord ++ tailWord_1009384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009384).length < 2 ^ (prefixWord ++ tailWord_1009384).sum := by decide
  have hdescent : baseEnd_1009384 < baseStart_1009384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009412 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 8]
def baseStart_1009412 : Nat := 118140960795 + 1009412 * 2 ^ 59
def prefixEnd_1009412 : Nat := 4983230072969 + 3 ^ 40 * 1009412 * 2
def baseEnd_1009412 : Nat := 115180785425846645468401

theorem tailTrace_1009412 : CollatzResearch.WordTrace tailWord_1009412 prefixEnd_1009412 115180785425846645468401 := by
  unfold tailWord_1009412
  simp only [CollatzResearch.WordTrace]
  refine ⟨18408140109540096344867245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24544186812720128459822993 18408140109540096344867245)
  ·
    refine ⟨6903052541077536129325217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18408140109540096344867245 6903052541077536129325217)
    ·
      refine ⟨5177289405808152096993913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6903052541077536129325217 5177289405808152096993913)
      ·
        refine ⟨3882967054356114072745435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5177289405808152096993913 3882967054356114072745435)
        ·
          refine ⟨5824450581534171109118153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3882967054356114072745435 5824450581534171109118153)
          ·
            refine ⟨4368337936150628331838615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5824450581534171109118153 4368337936150628331838615)
            ·
              refine ⟨6552506904225942497757923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4368337936150628331838615 6552506904225942497757923)
              ·
                refine ⟨9828760356338913746636885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6552506904225942497757923 9828760356338913746636885)
                ·
                  refine ⟨115180785425846645468401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9828760356338913746636885 115180785425846645468401)
                  ·
                    rfl

theorem cell22_1009412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_1009412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009412 prefixEnd_1009412 := by exact prefixLift 1009412
  have htrace : WordTrace (prefixWord ++ tailWord_1009412) baseStart_1009412 baseEnd_1009412 := by
    simpa [prefixWord, tailWord_1009412, baseEnd_1009412] using wordTrace_append hprefix tailTrace_1009412
  have hstable : (prefixWord ++ tailWord_1009412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009412).length < 2 ^ (prefixWord ++ tailWord_1009412).sum := by decide
  have hdescent : baseEnd_1009412 < baseStart_1009412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009429 : List Nat := [1, 3, 2, 1, 2, 3, 1, 5, 4]
def baseStart_1009429 : Nat := 118140960795 + 1009429 * 2 ^ 59
def prefixEnd_1009429 : Nat := 4983230072969 + 3 ^ 40 * 1009429 * 2
def baseEnd_1009429 : Nat := 115182725241652519576717

theorem tailTrace_1009429 : CollatzResearch.WordTrace tailWord_1009429 prefixEnd_1009429 115182725241652519576717 := by
  unfold tailWord_1009429
  simp only [CollatzResearch.WordTrace]
  refine ⟨36816900260018604593103341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24544600173345736395402227 36816900260018604593103341)
  ·
    refine ⟨13806337597506976722413753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36816900260018604593103341 13806337597506976722413753)
    ·
      refine ⟨10354753198130232541810315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13806337597506976722413753 10354753198130232541810315)
      ·
        refine ⟨15532129797195348812715473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10354753198130232541810315 15532129797195348812715473)
        ·
          refine ⟨11649097347896511609536605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15532129797195348812715473 11649097347896511609536605)
          ·
            refine ⟨4368411505461191853576227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11649097347896511609536605 4368411505461191853576227)
            ·
              refine ⟨6552617258191787780364341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4368411505461191853576227 6552617258191787780364341)
              ·
                refine ⟨614307867955480104409157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6552617258191787780364341 614307867955480104409157)
                ·
                  refine ⟨115182725241652519576717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 614307867955480104409157 115182725241652519576717)
                  ·
                    rfl

theorem cell22_1009429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 4].length) (baseStart_1009429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009429 prefixEnd_1009429 := by exact prefixLift 1009429
  have htrace : WordTrace (prefixWord ++ tailWord_1009429) baseStart_1009429 baseEnd_1009429 := by
    simpa [prefixWord, tailWord_1009429, baseEnd_1009429] using wordTrace_append hprefix tailTrace_1009429
  have hstable : (prefixWord ++ tailWord_1009429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009429).length < 2 ^ (prefixWord ++ tailWord_1009429).sum := by decide
  have hdescent : baseEnd_1009429 < baseStart_1009429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009431 : List Nat := [1, 1, 3, 4, 2, 1, 4, 1, 1, 4]
def baseStart_1009431 : Nat := 118140960795 + 1009431 * 2 ^ 59
def prefixEnd_1009431 : Nat := 4983230072969 + 3 ^ 40 * 1009431 * 2
def baseEnd_1009431 : Nat := 345548860365830220180145

theorem tailTrace_1009431 : CollatzResearch.WordTrace tailWord_1009431 prefixEnd_1009431 345548860365830220180145 := by
  unfold tailWord_1009431
  simp only [CollatzResearch.WordTrace]
  refine ⟨36816973206011358934676147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24544648804007572623117431 36816973206011358934676147)
  ·
    refine ⟨55225459809017038402014221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36816973206011358934676147 55225459809017038402014221)
    ·
      refine ⟨20709547428381389400755333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55225459809017038402014221 20709547428381389400755333)
      ·
        refine ⟨3883040142821510512641625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20709547428381389400755333 3883040142821510512641625)
        ·
          refine ⟨2912280107116132884481219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3883040142821510512641625 2912280107116132884481219)
          ·
            refine ⟨4368420160674199326721829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2912280107116132884481219 4368420160674199326721829)
            ·
              refine ⟨819078780126412373760343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4368420160674199326721829 819078780126412373760343)
              ·
                refine ⟨1228618170189618560640515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819078780126412373760343 1228618170189618560640515)
                ·
                  refine ⟨1842927255284427840960773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1228618170189618560640515 1842927255284427840960773)
                  ·
                    refine ⟨345548860365830220180145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1842927255284427840960773 345548860365830220180145)
                    ·
                      rfl

theorem cell22_1009431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 1, 4].length) (baseStart_1009431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009431 prefixEnd_1009431 := by exact prefixLift 1009431
  have htrace : WordTrace (prefixWord ++ tailWord_1009431) baseStart_1009431 baseEnd_1009431 := by
    simpa [prefixWord, tailWord_1009431, baseEnd_1009431] using wordTrace_append hprefix tailTrace_1009431
  have hstable : (prefixWord ++ tailWord_1009431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009431).length < 2 ^ (prefixWord ++ tailWord_1009431).sum := by decide
  have hdescent : baseEnd_1009431 < baseStart_1009431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009461 : List Nat := [1, 3, 3, 1, 4, 2, 1, 1, 1, 5]
def baseStart_1009461 : Nat := 118140960795 + 1009461 * 2 ^ 59
def prefixEnd_1009461 : Nat := 4983230072969 + 3 ^ 40 * 1009461 * 2
def baseEnd_1009461 : Nat := 345559129978920141930053

theorem tailTrace_1009461 : CollatzResearch.WordTrace tailWord_1009461 prefixEnd_1009461 345559129978920141930053 := by
  unfold tailWord_1009461
  simp only [CollatzResearch.WordTrace]
  refine ⟨36818067395902674058268237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24545378263935116038845491 36818067395902674058268237)
  ·
    refine ⟨13806775273463502771850589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36818067395902674058268237 13806775273463502771850589)
    ·
      refine ⟨5177540727548813539443971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13806775273463502771850589 5177540727548813539443971)
      ·
        refine ⟨7766311091323220309165957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5177540727548813539443971 7766311091323220309165957)
        ·
          refine ⟨1456183329623103807968617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7766311091323220309165957 1456183329623103807968617)
          ·
            refine ⟨1092137497217327855976463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1456183329623103807968617 1092137497217327855976463)
            ·
              refine ⟨1638206245825991783964695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092137497217327855976463 1638206245825991783964695)
              ·
                refine ⟨2457309368738987675947043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1638206245825991783964695 2457309368738987675947043)
                ·
                  refine ⟨3685964053108481513920565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2457309368738987675947043 3685964053108481513920565)
                  ·
                    refine ⟨345559129978920141930053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3685964053108481513920565 345559129978920141930053)
                    ·
                      rfl

theorem cell22_1009461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_1009461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009461 prefixEnd_1009461 := by exact prefixLift 1009461
  have htrace : WordTrace (prefixWord ++ tailWord_1009461) baseStart_1009461 baseEnd_1009461 := by
    simpa [prefixWord, tailWord_1009461, baseEnd_1009461] using wordTrace_append hprefix tailTrace_1009461
  have hstable : (prefixWord ++ tailWord_1009461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009461).length < 2 ^ (prefixWord ++ tailWord_1009461).sum := by decide
  have hdescent : baseEnd_1009461 < baseStart_1009461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009478 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_1009478 : Nat := 118140960795 + 1009478 * 2 ^ 59
def prefixEnd_1009478 : Nat := 4983230072969 + 3 ^ 40 * 1009478 * 2
def baseEnd_1009478 : Nat := 345564949426337764255001

theorem tailTrace_1009478 : CollatzResearch.WordTrace tailWord_1009478 prefixEnd_1009478 345564949426337764255001 := by
  unfold tailWord_1009478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1150583982401283936301159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24545791624560723974424725 1150583982401283936301159)
  ·
    refine ⟨1725875973601925904451739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1150583982401283936301159 1725875973601925904451739)
    ·
      refine ⟨2588813960402888856677609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1725875973601925904451739 2588813960402888856677609)
      ·
        refine ⟨1941610470302166642508207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2588813960402888856677609 1941610470302166642508207)
        ·
          refine ⟨2912415705453249963762311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1941610470302166642508207 2912415705453249963762311)
          ·
            refine ⟨4368623558179874945643467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2912415705453249963762311 4368623558179874945643467)
            ·
              refine ⟨6552935337269812418465201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4368623558179874945643467 6552935337269812418465201)
              ·
                refine ⟨4914701502952359313848901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6552935337269812418465201 4914701502952359313848901)
                ·
                  refine ⟨921506531803567371346669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4914701502952359313848901 921506531803567371346669)
                  ·
                    refine ⟨345564949426337764255001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 921506531803567371346669 345564949426337764255001)
                    ·
                      rfl

theorem cell22_1009478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_1009478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009478 prefixEnd_1009478 := by exact prefixLift 1009478
  have htrace : WordTrace (prefixWord ++ tailWord_1009478) baseStart_1009478 baseEnd_1009478 := by
    simpa [prefixWord, tailWord_1009478, baseEnd_1009478] using wordTrace_append hprefix tailTrace_1009478
  have hstable : (prefixWord ++ tailWord_1009478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009478).length < 2 ^ (prefixWord ++ tailWord_1009478).sum := by decide
  have hdescent : baseEnd_1009478 < baseStart_1009478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009594 : List Nat := [3, 1, 1, 1, 2, 1, 2, 5, 2, 4]
def baseStart_1009594 : Nat := 118140960795 + 1009594 * 2 ^ 59
def prefixEnd_1009594 : Nat := 4983230072969 + 3 ^ 40 * 1009594 * 2
def baseEnd_1009594 : Nat := 345604658596952128354645

theorem tailTrace_1009594 : CollatzResearch.WordTrace tailWord_1009594 prefixEnd_1009594 345604658596952128354645 := by
  unfold tailWord_1009594
  simp only [CollatzResearch.WordTrace]
  refine ⟨9205729576105209443214959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24548612202947225181906557 9205729576105209443214959)
  ·
    refine ⟨13808594364157814164822439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9205729576105209443214959 13808594364157814164822439)
    ·
      refine ⟨20712891546236721247233659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13808594364157814164822439 20712891546236721247233659)
      ·
        refine ⟨31069337319355081870850489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20712891546236721247233659 31069337319355081870850489)
        ·
          refine ⟨23302002989516311403137867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31069337319355081870850489 23302002989516311403137867)
          ·
            refine ⟨34953004484274467104706801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23302002989516311403137867 34953004484274467104706801)
            ·
              refine ⟨26214753363205850328530101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34953004484274467104706801 26214753363205850328530101)
              ·
                refine ⟨2457633127800548468299697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26214753363205850328530101 2457633127800548468299697)
                ·
                  refine ⟨1843224845850411351224773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2457633127800548468299697 1843224845850411351224773)
                  ·
                    refine ⟨345604658596952128354645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1843224845850411351224773 345604658596952128354645)
                    ·
                      rfl

theorem cell22_1009594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_1009594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009594 prefixEnd_1009594 := by exact prefixLift 1009594
  have htrace : WordTrace (prefixWord ++ tailWord_1009594) baseStart_1009594 baseEnd_1009594 := by
    simpa [prefixWord, tailWord_1009594, baseEnd_1009594] using wordTrace_append hprefix tailTrace_1009594
  have hstable : (prefixWord ++ tailWord_1009594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009594).length < 2 ^ (prefixWord ++ tailWord_1009594).sum := by decide
  have hdescent : baseEnd_1009594 < baseStart_1009594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009598 : List Nat := [4, 2, 1, 1, 1, 4, 2, 3, 4]
def baseStart_1009598 : Nat := 118140960795 + 1009598 * 2 ^ 59
def prefixEnd_1009598 : Nat := 4983230072969 + 3 ^ 40 * 1009598 * 2
def baseEnd_1009598 : Nat := 115202009292899150418211

theorem tailTrace_1009598 : CollatzResearch.WordTrace tailWord_1009598 prefixEnd_1009598 115202009292899150418211 := by
  unfold tailWord_1009598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4602883024550793307000681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24548709464270897637336965 4602883024550793307000681)
  ·
    refine ⟨3452162268413094980250511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4602883024550793307000681 3452162268413094980250511)
    ·
      refine ⟨5178243402619642470375767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3452162268413094980250511 5178243402619642470375767)
      ·
        refine ⟨7767365103929463705563651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5178243402619642470375767 7767365103929463705563651)
        ·
          refine ⟨11651047655894195558345477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7767365103929463705563651 11651047655894195558345477)
          ·
            refine ⟨2184571435480161667189777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11651047655894195558345477 2184571435480161667189777)
            ·
              refine ⟨1638428576610121250392333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2184571435480161667189777 1638428576610121250392333)
              ·
                refine ⟨614410716228795468897125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1638428576610121250392333 614410716228795468897125)
                ·
                  refine ⟨115202009292899150418211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 614410716228795468897125 115202009292899150418211)
                  ·
                    rfl

theorem cell22_1009598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_1009598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009598 prefixEnd_1009598 := by exact prefixLift 1009598
  have htrace : WordTrace (prefixWord ++ tailWord_1009598) baseStart_1009598 baseEnd_1009598 := by
    simpa [prefixWord, tailWord_1009598, baseEnd_1009598] using wordTrace_append hprefix tailTrace_1009598
  have hstable : (prefixWord ++ tailWord_1009598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009598).length < 2 ^ (prefixWord ++ tailWord_1009598).sum := by decide
  have hdescent : baseEnd_1009598 < baseStart_1009598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009675 : List Nat := [1, 1, 1, 1, 6, 1, 5, 2, 1, 3]
def baseStart_1009675 : Nat := 118140960795 + 1009675 * 2 ^ 59
def prefixEnd_1009675 : Nat := 4983230072969 + 3 ^ 40 * 1009675 * 2
def baseEnd_1009675 : Nat := 345632386552294917079397

theorem tailTrace_1009675 : CollatzResearch.WordTrace tailWord_1009675 prefixEnd_1009675 345632386552294917079397 := by
  unfold tailWord_1009675
  simp only [CollatzResearch.WordTrace]
  refine ⟨36825872617127388606558479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24550581744751592404372319 36825872617127388606558479)
  ·
    refine ⟨55238808925691082909837719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36825872617127388606558479 55238808925691082909837719)
    ·
      refine ⟨82858213388536624364756579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55238808925691082909837719 82858213388536624364756579)
      ·
        refine ⟨124287320082804936547134869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82858213388536624364756579 124287320082804936547134869)
        ·
          refine ⟨5825968128881481400646947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 124287320082804936547134869 5825968128881481400646947)
          ·
            refine ⟨8738952193322222100970421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5825968128881481400646947 8738952193322222100970421)
            ·
              refine ⟨819276768123958321965977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8738952193322222100970421 819276768123958321965977)
              ·
                refine ⟨614457576092968741474483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 819276768123958321965977 614457576092968741474483)
                ·
                  refine ⟨921686364139453112211725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 614457576092968741474483 921686364139453112211725)
                  ·
                    refine ⟨345632386552294917079397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 921686364139453112211725 345632386552294917079397)
                    ·
                      rfl

theorem cell22_1009675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 1, 3].length) (baseStart_1009675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009675 prefixEnd_1009675 := by exact prefixLift 1009675
  have htrace : WordTrace (prefixWord ++ tailWord_1009675) baseStart_1009675 baseEnd_1009675 := by
    simpa [prefixWord, tailWord_1009675, baseEnd_1009675] using wordTrace_append hprefix tailTrace_1009675
  have hstable : (prefixWord ++ tailWord_1009675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009675).length < 2 ^ (prefixWord ++ tailWord_1009675).sum := by decide
  have hdescent : baseEnd_1009675 < baseStart_1009675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009699 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 8]
def baseStart_1009699 : Nat := 118140960795 + 1009699 * 2 ^ 59
def prefixEnd_1009699 : Nat := 4983230072969 + 3 ^ 40 * 1009699 * 2
def baseEnd_1009699 : Nat := 115213534080922284826441

theorem tailTrace_1009699 : CollatzResearch.WordTrace tailWord_1009699 prefixEnd_1009699 115213534080922284826441 := by
  unfold tailWord_1009699
  simp only [CollatzResearch.WordTrace]
  refine ⟨36826747969040440705432151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24551165312693627136954767 36826747969040440705432151)
  ·
    refine ⟨55240121953560661058148227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36826747969040440705432151 55240121953560661058148227)
    ·
      refine ⟨82860182930340991587222341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55240121953560661058148227 82860182930340991587222341)
      ·
        refine ⟨15536284299438935922604189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82860182930340991587222341 15536284299438935922604189)
        ·
          refine ⟨5826106612289600970976571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15536284299438935922604189 5826106612289600970976571)
          ·
            refine ⟨8739159918434401456464857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5826106612289600970976571 8739159918434401456464857)
            ·
              refine ⟨6554369938825801092348643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8739159918434401456464857 6554369938825801092348643)
              ·
                refine ⟨9831554908238701638522965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6554369938825801092348643 9831554908238701638522965)
                ·
                  refine ⟨115213534080922284826441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9831554908238701638522965 115213534080922284826441)
                  ·
                    rfl

theorem cell22_1009699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 8].length) (baseStart_1009699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009699 prefixEnd_1009699 := by exact prefixLift 1009699
  have htrace : WordTrace (prefixWord ++ tailWord_1009699) baseStart_1009699 baseEnd_1009699 := by
    simpa [prefixWord, tailWord_1009699, baseEnd_1009699] using wordTrace_append hprefix tailTrace_1009699
  have hstable : (prefixWord ++ tailWord_1009699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009699).length < 2 ^ (prefixWord ++ tailWord_1009699).sum := by decide
  have hdescent : baseEnd_1009699 < baseStart_1009699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009701 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 3, 4]
def baseStart_1009701 : Nat := 118140960795 + 1009701 * 2 ^ 59
def prefixEnd_1009701 : Nat := 4983230072969 + 3 ^ 40 * 1009701 * 2
def baseEnd_1009701 : Nat := 345641286883639515929317

theorem tailTrace_1009701 : CollatzResearch.WordTrace tailWord_1009701 prefixEnd_1009701 345641286883639515929317 := by
  unfold tailWord_1009701
  simp only [CollatzResearch.WordTrace]
  refine ⟨36826820915033195047004957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24551213943355463364669971 36826820915033195047004957)
  ·
    refine ⟨13810057843137448142626859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36826820915033195047004957 13810057843137448142626859)
    ·
      refine ⟨20715086764706172213940289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13810057843137448142626859 20715086764706172213940289)
      ·
        refine ⟨15536315073529629160455217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20715086764706172213940289 15536315073529629160455217)
        ·
          refine ⟨11652236305147221870341413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15536315073529629160455217 11652236305147221870341413)
          ·
            refine ⟨2184794307215104100689015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11652236305147221870341413 2184794307215104100689015)
            ·
              refine ⟨3277191460822656151033523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2184794307215104100689015 3277191460822656151033523)
              ·
                refine ⟨4915787191233984226550285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3277191460822656151033523 4915787191233984226550285)
                ·
                  refine ⟨1843420196712744084956357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4915787191233984226550285 1843420196712744084956357)
                  ·
                    refine ⟨345641286883639515929317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1843420196712744084956357 345641286883639515929317)
                    ·
                      rfl

theorem cell22_1009701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_1009701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009701 prefixEnd_1009701 := by exact prefixLift 1009701
  have htrace : WordTrace (prefixWord ++ tailWord_1009701) baseStart_1009701 baseEnd_1009701 := by
    simpa [prefixWord, tailWord_1009701, baseEnd_1009701] using wordTrace_append hprefix tailTrace_1009701
  have hstable : (prefixWord ++ tailWord_1009701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009701).length < 2 ^ (prefixWord ++ tailWord_1009701).sum := by decide
  have hdescent : baseEnd_1009701 < baseStart_1009701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009726 : List Nat := [4, 2, 1, 3, 3, 1, 2, 2, 1, 3]
def baseStart_1009726 : Nat := 118140960795 + 1009726 * 2 ^ 59
def prefixEnd_1009726 : Nat := 4983230072969 + 3 ^ 40 * 1009726 * 2
def baseEnd_1009726 : Nat := 345649844894547784054241

theorem tailTrace_1009726 : CollatzResearch.WordTrace tailWord_1009726 prefixEnd_1009726 345649844894547784054241 := by
  unfold tailWord_1009726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4603466592492828039583129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24551821826628416211110021 4603466592492828039583129)
  ·
    refine ⟨3452599944369621029687347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4603466592492828039583129 3452599944369621029687347)
    ·
      refine ⟨5178899916554431544531021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3452599944369621029687347 5178899916554431544531021)
      ·
        refine ⟨1942087468707911829199133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5178899916554431544531021 1942087468707911829199133)
        ·
          refine ⟨728282800765466935949675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1942087468707911829199133 728282800765466935949675)
          ·
            refine ⟨1092424201148200403924513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728282800765466935949675 1092424201148200403924513)
            ·
              refine ⟨819318150861150302943385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1092424201148200403924513 819318150861150302943385)
              ·
                refine ⟨614488613145862727207539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 819318150861150302943385 614488613145862727207539)
                ·
                  refine ⟨921732919718794090811309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 614488613145862727207539 921732919718794090811309)
                  ·
                    refine ⟨345649844894547784054241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 921732919718794090811309 345649844894547784054241)
                    ·
                      rfl

theorem cell22_1009726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_1009726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009726 prefixEnd_1009726 := by exact prefixLift 1009726
  have htrace : WordTrace (prefixWord ++ tailWord_1009726) baseStart_1009726 baseEnd_1009726 := by
    simpa [prefixWord, tailWord_1009726, baseEnd_1009726] using wordTrace_append hprefix tailTrace_1009726
  have hstable : (prefixWord ++ tailWord_1009726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009726).length < 2 ^ (prefixWord ++ tailWord_1009726).sum := by decide
  have hdescent : baseEnd_1009726 < baseStart_1009726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009750 : List Nat := [5, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_1009750 : Nat := 118140960795 + 1009750 * 2 ^ 59
def prefixEnd_1009750 : Nat := 4983230072969 + 3 ^ 40 * 1009750 * 2
def baseEnd_1009750 : Nat := 115219353528339907151389

theorem tailTrace_1009750 : CollatzResearch.WordTrace tailWord_1009750 prefixEnd_1009750 115219353528339907151389 := by
  unfold tailWord_1009750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2301788005740979775971169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24552405394570450943692469 2301788005740979775971169)
  ·
    refine ⟨1726341004305734831978377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2301788005740979775971169 1726341004305734831978377)
    ·
      refine ⟨1294755753229301123983783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1726341004305734831978377 1294755753229301123983783)
      ·
        refine ⟨1942133629843951685975675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1294755753229301123983783 1942133629843951685975675)
        ·
          refine ⟨2913200444765927528963513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1942133629843951685975675 2913200444765927528963513)
          ·
            refine ⟨2184900333574445646722635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2913200444765927528963513 2184900333574445646722635)
            ·
              refine ⟨3277350500361668470083953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2184900333574445646722635 3277350500361668470083953)
              ·
                refine ⟨2458012875271251352562965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3277350500361668470083953 2458012875271251352562965)
                ·
                  refine ⟨115219353528339907151389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2458012875271251352562965 115219353528339907151389)
                  ·
                    rfl

theorem cell22_1009750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_1009750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009750 prefixEnd_1009750 := by exact prefixLift 1009750
  have htrace : WordTrace (prefixWord ++ tailWord_1009750) baseStart_1009750 baseEnd_1009750 := by
    simpa [prefixWord, tailWord_1009750, baseEnd_1009750] using wordTrace_append hprefix tailTrace_1009750
  have hstable : (prefixWord ++ tailWord_1009750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009750).length < 2 ^ (prefixWord ++ tailWord_1009750).sum := by decide
  have hdescent : baseEnd_1009750 < baseStart_1009750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009759 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 1, 9]
def baseStart_1009759 : Nat := 118140960795 + 1009759 * 2 ^ 59
def prefixEnd_1009759 : Nat := 4983230072969 + 3 ^ 40 * 1009759 * 2
def baseEnd_1009759 : Nat := 345661141468946697979139

theorem tailTrace_1009759 : CollatzResearch.WordTrace tailWord_1009759 prefixEnd_1009759 345661141468946697979139 := by
  unfold tailWord_1009759
  simp only [CollatzResearch.WordTrace]
  refine ⟨36828936348823070952616331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24552624232548713968410887 36828936348823070952616331)
  ·
    refine ⟨55243404523234606428924497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36828936348823070952616331 55243404523234606428924497)
    ·
      refine ⟨41432553392425954821693373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55243404523234606428924497 41432553392425954821693373)
      ·
        refine ⟨15537207522159733058135015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41432553392425954821693373 15537207522159733058135015)
        ·
          refine ⟨23305811283239599587202523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15537207522159733058135015 23305811283239599587202523)
          ·
            refine ⟨34958716924859399380803785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23305811283239599587202523 34958716924859399380803785)
            ·
              refine ⟨26219037693644549535602839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34958716924859399380803785 26219037693644549535602839)
              ·
                refine ⟨39328556540466824303404259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26219037693644549535602839 39328556540466824303404259)
                ·
                  refine ⟨58992834810700236455106389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39328556540466824303404259 58992834810700236455106389)
                  ·
                    refine ⟨345661141468946697979139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 58992834810700236455106389 345661141468946697979139)
                    ·
                      rfl

theorem cell22_1009759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_1009759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009759 prefixEnd_1009759 := by exact prefixLift 1009759
  have htrace : WordTrace (prefixWord ++ tailWord_1009759) baseStart_1009759 baseEnd_1009759 := by
    simpa [prefixWord, tailWord_1009759, baseEnd_1009759] using wordTrace_append hprefix tailTrace_1009759
  have hstable : (prefixWord ++ tailWord_1009759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009759).length < 2 ^ (prefixWord ++ tailWord_1009759).sum := by decide
  have hdescent : baseEnd_1009759 < baseStart_1009759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009782 : List Nat := [5, 1, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_1009782 : Nat := 118140960795 + 1009782 * 2 ^ 59
def prefixEnd_1009782 : Nat := 4983230072969 + 3 ^ 40 * 1009782 * 2
def baseEnd_1009782 : Nat := 345669014838982304654069

theorem tailTrace_1009782 : CollatzResearch.WordTrace tailWord_1009782 prefixEnd_1009782 345669014838982304654069 := by
  unfold tailWord_1009782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2301860951733734117543975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24553183485159830587135733 2301860951733734117543975)
  ·
    refine ⟨3452791427600601176315963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2301860951733734117543975 3452791427600601176315963)
    ·
      refine ⟨5179187141400901764473945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3452791427600601176315963 5179187141400901764473945)
      ·
        refine ⟨3884390356050676323355459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5179187141400901764473945 3884390356050676323355459)
        ·
          refine ⟨5826585534076014485033189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3884390356050676323355459 5826585534076014485033189)
          ·
            refine ⟨1092484787639252715943723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5826585534076014485033189 1092484787639252715943723)
            ·
              refine ⟨1638727181458879073915585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092484787639252715943723 1638727181458879073915585)
              ·
                refine ⟨1229045386094159305436689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1638727181458879073915585 1229045386094159305436689)
                ·
                  refine ⟨921784039570619479077517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1229045386094159305436689 921784039570619479077517)
                  ·
                    refine ⟨345669014838982304654069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 921784039570619479077517 345669014838982304654069)
                    ·
                      rfl

theorem cell22_1009782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_1009782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009782 prefixEnd_1009782 := by exact prefixLift 1009782
  have htrace : WordTrace (prefixWord ++ tailWord_1009782) baseStart_1009782 baseEnd_1009782 := by
    simpa [prefixWord, tailWord_1009782, baseEnd_1009782] using wordTrace_append hprefix tailTrace_1009782
  have hstable : (prefixWord ++ tailWord_1009782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009782).length < 2 ^ (prefixWord ++ tailWord_1009782).sum := by decide
  have hdescent : baseEnd_1009782 < baseStart_1009782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009812 : List Nat := [2, 4, 2, 3, 1, 2, 2, 6]
def baseStart_1009812 : Nat := 118140960795 + 1009812 * 2 ^ 59
def prefixEnd_1009812 : Nat := 4983230072969 + 3 ^ 40 * 1009812 * 2
def baseEnd_1009812 : Nat := 38408809383563580711553

theorem tailTrace_1009812 : CollatzResearch.WordTrace tailWord_1009812 prefixEnd_1009812 38408809383563580711553 := by
  unfold tailWord_1009812
  simp only [CollatzResearch.WordTrace]
  refine ⟨18415434708815530502147845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24553912945087374002863793 18415434708815530502147845)
  ·
    refine ⟨3452894007902911969152721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18415434708815530502147845 3452894007902911969152721)
    ·
      refine ⟨2589670505927183976864541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3452894007902911969152721 2589670505927183976864541)
      ·
        refine ⟨971126439722693991324203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2589670505927183976864541 971126439722693991324203)
        ·
          refine ⟨1456689659584040986986305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971126439722693991324203 1456689659584040986986305)
          ·
            refine ⟨1092517244688030740239729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1456689659584040986986305 1092517244688030740239729)
            ·
              refine ⟨819387933516023055179797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1092517244688030740239729 819387933516023055179797)
              ·
                refine ⟨38408809383563580711553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 819387933516023055179797 38408809383563580711553)
                ·
                  rfl

theorem cell22_1009812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 6].length) (baseStart_1009812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009812 prefixEnd_1009812 := by exact prefixLift 1009812
  have htrace : WordTrace (prefixWord ++ tailWord_1009812) baseStart_1009812 baseEnd_1009812 := by
    simpa [prefixWord, tailWord_1009812, baseEnd_1009812] using wordTrace_append hprefix tailTrace_1009812
  have hstable : (prefixWord ++ tailWord_1009812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009812).length < 2 ^ (prefixWord ++ tailWord_1009812).sum := by decide
  have hdescent : baseEnd_1009812 < baseStart_1009812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009870 : List Nat := [4, 1, 1, 1, 4, 1, 3, 2, 1, 4]
def baseStart_1009870 : Nat := 118140960795 + 1009870 * 2 ^ 59
def prefixEnd_1009870 : Nat := 4983230072969 + 3 ^ 40 * 1009870 * 2
def baseEnd_1009870 : Nat := 345699139037379408453799

theorem tailTrace_1009870 : CollatzResearch.WordTrace tailWord_1009870 prefixEnd_1009870 345699139037379408453799 := by
  unfold tailWord_1009870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4604123106427617113738383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24555323234280624606604709 4604123106427617113738383)
  ·
    refine ⟨6906184659641425670607575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4604123106427617113738383 6906184659641425670607575)
    ·
      refine ⟨10359276989462138505911363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6906184659641425670607575 10359276989462138505911363)
      ·
        refine ⟨15538915484193207758867045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10359276989462138505911363 15538915484193207758867045)
        ·
          refine ⟨2913546653286226454787571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15538915484193207758867045 2913546653286226454787571)
          ·
            refine ⟨4370319979929339682181357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2913546653286226454787571 4370319979929339682181357)
            ·
              refine ⟨1638869992473502380818009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4370319979929339682181357 1638869992473502380818009)
              ·
                refine ⟨1229152494355126785613507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1638869992473502380818009 1229152494355126785613507)
                ·
                  refine ⟨1843728741532690178420261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1229152494355126785613507 1843728741532690178420261)
                  ·
                    refine ⟨345699139037379408453799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1843728741532690178420261 345699139037379408453799)
                    ·
                      rfl

theorem cell22_1009870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_1009870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009870 prefixEnd_1009870 := by exact prefixLift 1009870
  have htrace : WordTrace (prefixWord ++ tailWord_1009870) baseStart_1009870 baseEnd_1009870 := by
    simpa [prefixWord, tailWord_1009870, baseEnd_1009870] using wordTrace_append hprefix tailTrace_1009870
  have hstable : (prefixWord ++ tailWord_1009870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009870).length < 2 ^ (prefixWord ++ tailWord_1009870).sum := by decide
  have hdescent : baseEnd_1009870 < baseStart_1009870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009881 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 1, 6]
def baseStart_1009881 : Nat := 118140960795 + 1009881 * 2 ^ 59
def prefixEnd_1009881 : Nat := 4983230072969 + 3 ^ 40 * 1009881 * 2
def baseEnd_1009881 : Nat := 345702904562179046428765

theorem tailTrace_1009881 : CollatzResearch.WordTrace tailWord_1009881 prefixEnd_1009881 345702904562179046428765 := by
  unfold tailWord_1009881
  simp only [CollatzResearch.WordTrace]
  refine ⟨36833386054381085788557497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24555590702920723859038331 36833386054381085788557497)
  ·
    refine ⟨27625039540785814341418123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36833386054381085788557497 27625039540785814341418123)
    ·
      refine ⟨41437559311178721512127185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27625039540785814341418123 41437559311178721512127185)
      ·
        refine ⟨31078169483384041134095389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41437559311178721512127185 31078169483384041134095389)
        ·
          refine ⟨11654313556269015425285771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31078169483384041134095389 11654313556269015425285771)
          ·
            refine ⟨17481470334403523137928657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11654313556269015425285771 17481470334403523137928657)
            ·
              refine ⟨13111102750802642353446493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17481470334403523137928657 13111102750802642353446493)
              ·
                refine ⟨4916663531550990882542435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13111102750802642353446493 4916663531550990882542435)
                ·
                  refine ⟨7374995297326486323813653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4916663531550990882542435 7374995297326486323813653)
                  ·
                    refine ⟨345702904562179046428765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7374995297326486323813653 345702904562179046428765)
                    ·
                      rfl

theorem cell22_1009881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_1009881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009881 prefixEnd_1009881 := by exact prefixLift 1009881
  have htrace : WordTrace (prefixWord ++ tailWord_1009881) baseStart_1009881 baseEnd_1009881 := by
    simpa [prefixWord, tailWord_1009881, baseEnd_1009881] using wordTrace_append hprefix tailTrace_1009881
  have hstable : (prefixWord ++ tailWord_1009881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009881).length < 2 ^ (prefixWord ++ tailWord_1009881).sum := by decide
  have hdescent : baseEnd_1009881 < baseStart_1009881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009896 : List Nat := [2, 1, 4, 1, 2, 12]
def baseStart_1009896 : Nat := 118140960795 + 1009896 * 2 ^ 59
def prefixEnd_1009896 : Nat := 4983230072969 + 3 ^ 40 * 1009896 * 2
def baseEnd_1009896 : Nat := 4268000486033629719799

theorem tailTrace_1009896 : CollatzResearch.WordTrace tailWord_1009896 prefixEnd_1009896 4268000486033629719799 := by
  unfold tailWord_1009896
  simp only [CollatzResearch.WordTrace]
  refine ⟨18416966574663371675176771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24555955432884495566902361 18416966574663371675176771)
  ·
    refine ⟨27625449861995057512765157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18416966574663371675176771 27625449861995057512765157)
    ·
      refine ⟨5179771849124073283643467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27625449861995057512765157 5179771849124073283643467)
      ·
        refine ⟨7769657773686109925465201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5179771849124073283643467 7769657773686109925465201)
        ·
          refine ⟨5827243330264582444098901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7769657773686109925465201 5827243330264582444098901)
          ·
            refine ⟨4268000486033629719799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 5827243330264582444098901 4268000486033629719799)
            ·
              rfl

theorem cell22_1009896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 12].length) (baseStart_1009896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009896 prefixEnd_1009896 := by exact prefixLift 1009896
  have htrace : WordTrace (prefixWord ++ tailWord_1009896) baseStart_1009896 baseEnd_1009896 := by
    simpa [prefixWord, tailWord_1009896, baseEnd_1009896] using wordTrace_append hprefix tailTrace_1009896
  have hstable : (prefixWord ++ tailWord_1009896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009896).length < 2 ^ (prefixWord ++ tailWord_1009896).sum := by decide
  have hdescent : baseEnd_1009896 < baseStart_1009896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009898 : List Nat := [3, 1, 3, 1, 1, 2, 1, 4, 2, 4]
def baseStart_1009898 : Nat := 118140960795 + 1009898 * 2 ^ 59
def prefixEnd_1009898 : Nat := 4983230072969 + 3 ^ 40 * 1009898 * 2
def baseEnd_1009898 : Nat := 345708724009596668753713

theorem tailTrace_1009898 : CollatzResearch.WordTrace tailWord_1009898 prefixEnd_1009898 345708724009596668753713 := by
  unfold tailWord_1009898
  simp only [CollatzResearch.WordTrace]
  refine ⟨9208501523829874422981587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24556004063546331794617565 9208501523829874422981587)
  ·
    refine ⟨13812752285744811634472381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9208501523829874422981587 13812752285744811634472381)
    ·
      refine ⟨5179782107154304362927143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13812752285744811634472381 5179782107154304362927143)
      ·
        refine ⟨7769673160731456544390715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5179782107154304362927143 7769673160731456544390715)
        ·
          refine ⟨11654509741097184816586073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7769673160731456544390715 11654509741097184816586073)
          ·
            refine ⟨8740882305822888612439555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11654509741097184816586073 8740882305822888612439555)
            ·
              refine ⟨13111323458734332918659333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8740882305822888612439555 13111323458734332918659333)
              ·
                refine ⟨2458373148512687422248625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13111323458734332918659333 2458373148512687422248625)
                ·
                  refine ⟨1843779861384515566686469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2458373148512687422248625 1843779861384515566686469)
                  ·
                    refine ⟨345708724009596668753713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1843779861384515566686469 345708724009596668753713)
                    ·
                      rfl

theorem cell22_1009898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_1009898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009898 prefixEnd_1009898 := by exact prefixLift 1009898
  have htrace : WordTrace (prefixWord ++ tailWord_1009898) baseStart_1009898 baseEnd_1009898 := by
    simpa [prefixWord, tailWord_1009898, baseEnd_1009898] using wordTrace_append hprefix tailTrace_1009898
  have hstable : (prefixWord ++ tailWord_1009898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009898).length < 2 ^ (prefixWord ++ tailWord_1009898).sum := by decide
  have hdescent : baseEnd_1009898 < baseStart_1009898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009900 : List Nat := [2, 2, 1, 1, 2, 3, 4, 2, 2, 3]
def baseStart_1009900 : Nat := 118140960795 + 1009900 * 2 ^ 59
def prefixEnd_1009900 : Nat := 4983230072969 + 3 ^ 40 * 1009900 * 2
def baseEnd_1009900 : Nat := 345709408650469330203707

theorem tailTrace_1009900 : CollatzResearch.WordTrace tailWord_1009900 prefixEnd_1009900 345709408650469330203707 := by
  unfold tailWord_1009900
  simp only [CollatzResearch.WordTrace]
  refine ⟨18417039520656126016749577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24556052694208168022332769 18417039520656126016749577)
  ·
    refine ⟨13812779640492094512562183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18417039520656126016749577 13812779640492094512562183)
    ·
      refine ⟨20719169460738141768843275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13812779640492094512562183 20719169460738141768843275)
      ·
        refine ⟨31078754191107212653264913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20719169460738141768843275 31078754191107212653264913)
        ·
          refine ⟨23309065643330409489948685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31078754191107212653264913 23309065643330409489948685)
          ·
            refine ⟨8740899616248903558730757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23309065643330409489948685 8740899616248903558730757)
            ·
              refine ⟨1638918678046669417262017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8740899616248903558730757 1638918678046669417262017)
              ·
                refine ⟨1229189008535002062946513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1638918678046669417262017 1229189008535002062946513)
                ·
                  refine ⟨921891756401251547209885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1229189008535002062946513 921891756401251547209885)
                  ·
                    refine ⟨345709408650469330203707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 921891756401251547209885 345709408650469330203707)
                    ·
                      rfl

theorem cell22_1009900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_1009900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009900 prefixEnd_1009900 := by exact prefixLift 1009900
  have htrace : WordTrace (prefixWord ++ tailWord_1009900) baseStart_1009900 baseEnd_1009900 := by
    simpa [prefixWord, tailWord_1009900, baseEnd_1009900] using wordTrace_append hprefix tailTrace_1009900
  have hstable : (prefixWord ++ tailWord_1009900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009900).length < 2 ^ (prefixWord ++ tailWord_1009900).sum := by decide
  have hdescent : baseEnd_1009900 < baseStart_1009900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009973 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 2, 5]
def baseStart_1009973 : Nat := 118140960795 + 1009973 * 2 ^ 59
def prefixEnd_1009973 : Nat := 4983230072969 + 3 ^ 40 * 1009973 * 2
def baseEnd_1009973 : Nat := 345734398042321473128483

theorem tailTrace_1009973 : CollatzResearch.WordTrace tailWord_1009973 prefixEnd_1009973 345734398042321473128483 := by
  unfold tailWord_1009973
  simp only [CollatzResearch.WordTrace]
  refine ⟨36836741570047785500906573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24557827713365190333937715 36836741570047785500906573)
  ·
    refine ⟨13813778088767919562839965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36836741570047785500906573 13813778088767919562839965)
    ·
      refine ⟨5180166783287969836064987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13813778088767919562839965 5180166783287969836064987)
      ·
        refine ⟨7770250174931954754097481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5180166783287969836064987 7770250174931954754097481)
        ·
          refine ⟨5827687631198966065573111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7770250174931954754097481 5827687631198966065573111)
          ·
            refine ⟨8741531446798449098359667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5827687631198966065573111 8741531446798449098359667)
            ·
              refine ⟨13112297170197673647539501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8741531446798449098359667 13112297170197673647539501)
              ·
                refine ⟨4917111438824127617827313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13112297170197673647539501 4917111438824127617827313)
                ·
                  refine ⟨3687833579118095713370485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4917111438824127617827313 3687833579118095713370485)
                  ·
                    refine ⟨345734398042321473128483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3687833579118095713370485 345734398042321473128483)
                    ·
                      rfl

theorem cell22_1009973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_1009973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1009973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1009973 prefixEnd_1009973 := by exact prefixLift 1009973
  have htrace : WordTrace (prefixWord ++ tailWord_1009973) baseStart_1009973 baseEnd_1009973 := by
    simpa [prefixWord, tailWord_1009973, baseEnd_1009973] using wordTrace_append hprefix tailTrace_1009973
  have hstable : (prefixWord ++ tailWord_1009973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009973).length < 2 ^ (prefixWord ++ tailWord_1009973).sum := by decide
  have hdescent : baseEnd_1009973 < baseStart_1009973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010033 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 6, 4]
def baseStart_1010033 : Nat := 118140960795 + 1010033 * 2 ^ 59
def prefixEnd_1010033 : Nat := 4983230072969 + 3 ^ 40 * 1010033 * 2
def baseEnd_1010033 : Nat := 345754937268501316628299

theorem tailTrace_1010033 : CollatzResearch.WordTrace tailWord_1010033 prefixEnd_1010033 345754937268501316628299 := by
  unfold tailWord_1010033
  simp only [CollatzResearch.WordTrace]
  refine ⟨36838929949830415748090753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24559286633220277165393835 36838929949830415748090753)
  ·
    refine ⟨27629197462372811811068065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36838929949830415748090753 27629197462372811811068065)
    ·
      refine ⟨20721898096779608858301049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27629197462372811811068065 20721898096779608858301049)
      ·
        refine ⟨15541423572584706643725787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20721898096779608858301049 15541423572584706643725787)
        ·
          refine ⟨23312135358877059965588681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15541423572584706643725787 23312135358877059965588681)
          ·
            refine ⟨17484101519157794974191511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23312135358877059965588681 17484101519157794974191511)
            ·
              refine ⟨26226152278736692461287267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17484101519157794974191511 26226152278736692461287267)
              ·
                refine ⟨39339228418105038691930901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26226152278736692461287267 39339228418105038691930901)
                ·
                  refine ⟨1844026332098673688684261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39339228418105038691930901 1844026332098673688684261)
                  ·
                    refine ⟨345754937268501316628299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1844026332098673688684261 345754937268501316628299)
                    ·
                      rfl

theorem cell22_1010033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_1010033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010033 prefixEnd_1010033 := by exact prefixLift 1010033
  have htrace : WordTrace (prefixWord ++ tailWord_1010033) baseStart_1010033 baseEnd_1010033 := by
    simpa [prefixWord, tailWord_1010033, baseEnd_1010033] using wordTrace_append hprefix tailTrace_1010033
  have hstable : (prefixWord ++ tailWord_1010033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010033).length < 2 ^ (prefixWord ++ tailWord_1010033).sum := by decide
  have hdescent : baseEnd_1010033 < baseStart_1010033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010035 : List Nat := [1, 1, 1, 2, 2, 1, 2, 7, 2, 3]
def baseStart_1010035 : Nat := 118140960795 + 1010035 * 2 ^ 59
def prefixEnd_1010035 : Nat := 4983230072969 + 3 ^ 40 * 1010035 * 2
def baseEnd_1010035 : Nat := 345755621909373978078293

theorem tailTrace_1010035 : CollatzResearch.WordTrace tailWord_1010035 prefixEnd_1010035 345755621909373978078293 := by
  unfold tailWord_1010035
  simp only [CollatzResearch.WordTrace]
  refine ⟨36839002895823170089663559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24559335263882113393109039 36839002895823170089663559)
  ·
    refine ⟨55258504343734755134495339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36839002895823170089663559 55258504343734755134495339)
    ·
      refine ⟨82887756515602132701743009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55258504343734755134495339 82887756515602132701743009)
      ·
        refine ⟨62165817386701599526307257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82887756515602132701743009 62165817386701599526307257)
        ·
          refine ⟨46624363040026199644730443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62165817386701599526307257 46624363040026199644730443)
          ·
            refine ⟨69936544560039299467095665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46624363040026199644730443 69936544560039299467095665)
            ·
              refine ⟨52452408420029474600321749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69936544560039299467095665 52452408420029474600321749)
              ·
                refine ⟨1229353322344440810945041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 52452408420029474600321749 1229353322344440810945041)
                ·
                  refine ⟨922014991758330608208781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1229353322344440810945041 922014991758330608208781)
                  ·
                    refine ⟨345755621909373978078293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 922014991758330608208781 345755621909373978078293)
                    ·
                      rfl

theorem cell22_1010035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 3].length) (baseStart_1010035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010035 prefixEnd_1010035 := by exact prefixLift 1010035
  have htrace : WordTrace (prefixWord ++ tailWord_1010035) baseStart_1010035 baseEnd_1010035 := by
    simpa [prefixWord, tailWord_1010035, baseEnd_1010035] using wordTrace_append hprefix tailTrace_1010035
  have hstable : (prefixWord ++ tailWord_1010035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010035).length < 2 ^ (prefixWord ++ tailWord_1010035).sum := by decide
  have hdescent : baseEnd_1010035 < baseStart_1010035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010097 : List Nat := [1, 2, 2, 4, 1, 3, 1, 2, 3, 3]
def baseStart_1010097 : Nat := 118140960795 + 1010097 * 2 ^ 59
def prefixEnd_1010097 : Nat := 4983230072969 + 3 ^ 40 * 1010097 * 2
def baseEnd_1010097 : Nat := 345776845776426483028103

theorem tailTrace_1010097 : CollatzResearch.WordTrace tailWord_1010097 prefixEnd_1010097 345776845776426483028103 := by
  unfold tailWord_1010097
  simp only [CollatzResearch.WordTrace]
  refine ⟨36841264221598554678420545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24560842814399036452280363 36841264221598554678420545)
  ·
    refine ⟨27630948166198916008815409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36841264221598554678420545 27630948166198916008815409)
    ·
      refine ⟨20723211124649187006611557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27630948166198916008815409 20723211124649187006611557)
      ·
        refine ⟨3885602085871722563739667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20723211124649187006611557 3885602085871722563739667)
        ·
          refine ⟨5828403128807583845609501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3885602085871722563739667 5828403128807583845609501)
          ·
            refine ⟨2185651173302843942103563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5828403128807583845609501 2185651173302843942103563)
            ·
              refine ⟨3278476759954265913155345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2185651173302843942103563 3278476759954265913155345)
              ·
                refine ⟨2458857569965699434866509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3278476759954265913155345 2458857569965699434866509)
                ·
                  refine ⟨922071588737137288074941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2458857569965699434866509 922071588737137288074941)
                  ·
                    refine ⟨345776845776426483028103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 922071588737137288074941 345776845776426483028103)
                    ·
                      rfl

theorem cell22_1010097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_1010097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010097 prefixEnd_1010097 := by exact prefixLift 1010097
  have htrace : WordTrace (prefixWord ++ tailWord_1010097) baseStart_1010097 baseEnd_1010097 := by
    simpa [prefixWord, tailWord_1010097, baseEnd_1010097] using wordTrace_append hprefix tailTrace_1010097
  have hstable : (prefixWord ++ tailWord_1010097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010097).length < 2 ^ (prefixWord ++ tailWord_1010097).sum := by decide
  have hdescent : baseEnd_1010097 < baseStart_1010097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010165 : List Nat := [1, 3, 5, 1, 3, 1, 1, 3, 1, 3]
def baseStart_1010165 : Nat := 118140960795 + 1010165 * 2 ^ 59
def prefixEnd_1010165 : Nat := 4983230072969 + 3 ^ 40 * 1010165 * 2
def baseEnd_1010165 : Nat := 345800123566096972327895

theorem tailTrace_1010165 : CollatzResearch.WordTrace tailWord_1010165 prefixEnd_1010165 345800123566096972327895 := by
  unfold tailWord_1010165
  simp only [CollatzResearch.WordTrace]
  refine ⟨36843744385352202291895949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24562496256901468194597299 36843744385352202291895949)
  ·
    refine ⟨13816404144507075859460981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36843744385352202291895949 13816404144507075859460981)
    ·
      refine ⟨1295287888547538361824467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13816404144507075859460981 1295287888547538361824467)
      ·
        refine ⟨1942931832821307542736701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1295287888547538361824467 1942931832821307542736701)
        ·
          refine ⟨728599437307990328526263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1942931832821307542736701 728599437307990328526263)
          ·
            refine ⟨1092899155961985492789395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728599437307990328526263 1092899155961985492789395)
            ·
              refine ⟨1639348733942978239184093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092899155961985492789395 1639348733942978239184093)
              ·
                refine ⟨614755775228616839694035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1639348733942978239184093 614755775228616839694035)
                ·
                  refine ⟨922133662842925259541053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 614755775228616839694035 922133662842925259541053)
                  ·
                    refine ⟨345800123566096972327895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 922133662842925259541053 345800123566096972327895)
                    ·
                      rfl

theorem cell22_1010165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_1010165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010165 prefixEnd_1010165 := by exact prefixLift 1010165
  have htrace : WordTrace (prefixWord ++ tailWord_1010165) baseStart_1010165 baseEnd_1010165 := by
    simpa [prefixWord, tailWord_1010165, baseEnd_1010165] using wordTrace_append hprefix tailTrace_1010165
  have hstable : (prefixWord ++ tailWord_1010165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010165).length < 2 ^ (prefixWord ++ tailWord_1010165).sum := by decide
  have hdescent : baseEnd_1010165 < baseStart_1010165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010182 : List Nat := [6, 2, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_1010182 : Nat := 118140960795 + 1010182 * 2 ^ 59
def prefixEnd_1010182 : Nat := 4983230072969 + 3 ^ 40 * 1010182 * 2
def baseEnd_1010182 : Nat := 345805943013514594652843

theorem tailTrace_1010182 : CollatzResearch.WordTrace tailWord_1010182 prefixEnd_1010182 345805943013514594652843 := by
  unfold tailWord_1010182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1151386388321581693602025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24562909617527076130176533 1151386388321581693602025)
  ·
    refine ⟨863539791241186270201519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1151386388321581693602025 863539791241186270201519)
    ·
      refine ⟨1295309686861779405302279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 863539791241186270201519 1295309686861779405302279)
      ·
        refine ⟨1942964530292669107953419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1295309686861779405302279 1942964530292669107953419)
        ·
          refine ⟨2914446795439003661930129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1942964530292669107953419 2914446795439003661930129)
          ·
            refine ⟨2185835096579252746447597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2914446795439003661930129 2185835096579252746447597)
            ·
              refine ⟨819688161217219779917849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2185835096579252746447597 819688161217219779917849)
              ·
                refine ⟨614766120912914834938387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 819688161217219779917849 614766120912914834938387)
                ·
                  refine ⟨922149181369372252407581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 614766120912914834938387 922149181369372252407581)
                  ·
                    refine ⟨345805943013514594652843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 922149181369372252407581 345805943013514594652843)
                    ·
                      rfl

theorem cell22_1010182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_1010182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010182 prefixEnd_1010182 := by exact prefixLift 1010182
  have htrace : WordTrace (prefixWord ++ tailWord_1010182) baseStart_1010182 baseEnd_1010182 := by
    simpa [prefixWord, tailWord_1010182, baseEnd_1010182] using wordTrace_append hprefix tailTrace_1010182
  have hstable : (prefixWord ++ tailWord_1010182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010182).length < 2 ^ (prefixWord ++ tailWord_1010182).sum := by decide
  have hdescent : baseEnd_1010182 < baseStart_1010182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010187 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 4, 3]
def baseStart_1010187 : Nat := 118140960795 + 1010187 * 2 ^ 59
def prefixEnd_1010187 : Nat := 4983230072969 + 3 ^ 40 * 1010187 * 2
def baseEnd_1010187 : Nat := 345807654615696248277827

theorem tailTrace_1010187 : CollatzResearch.WordTrace tailWord_1010187 prefixEnd_1010187 345807654615696248277827 := by
  unfold tailWord_1010187
  simp only [CollatzResearch.WordTrace]
  refine ⟨36844546791272500049196815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24563031194181666699464543 36844546791272500049196815)
  ·
    refine ⟨55266820186908750073795223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36844546791272500049196815 55266820186908750073795223)
    ·
      refine ⟨82900230280363125110692835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55266820186908750073795223 82900230280363125110692835)
      ·
        refine ⟨124350345420544687666039253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82900230280363125110692835 124350345420544687666039253)
        ·
          refine ⟨2914461220794016117172795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 124350345420544687666039253 2914461220794016117172795)
          ·
            refine ⟨4371691831191024175759193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2914461220794016117172795 4371691831191024175759193)
            ·
              refine ⟨3278768873393268131819395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4371691831191024175759193 3278768873393268131819395)
              ·
                refine ⟨4918153310089902197729093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3278768873393268131819395 4918153310089902197729093)
                ·
                  refine ⟨922153745641856662074205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4918153310089902197729093 922153745641856662074205)
                  ·
                    refine ⟨345807654615696248277827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 922153745641856662074205 345807654615696248277827)
                    ·
                      rfl

theorem cell22_1010187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 3].length) (baseStart_1010187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010187 prefixEnd_1010187 := by exact prefixLift 1010187
  have htrace : WordTrace (prefixWord ++ tailWord_1010187) baseStart_1010187 baseEnd_1010187 := by
    simpa [prefixWord, tailWord_1010187, baseEnd_1010187] using wordTrace_append hprefix tailTrace_1010187
  have hstable : (prefixWord ++ tailWord_1010187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010187).length < 2 ^ (prefixWord ++ tailWord_1010187).sum := by decide
  have hdescent : baseEnd_1010187 < baseStart_1010187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010200 : List Nat := [2, 1, 2, 3, 3, 1, 1, 9]
def baseStart_1010200 : Nat := 118140960795 + 1010200 * 2 ^ 59
def prefixEnd_1010200 : Nat := 4983230072969 + 3 ^ 40 * 1010200 * 2
def baseEnd_1010200 : Nat := 38423567197929838633643

theorem tailTrace_1010200 : CollatzResearch.WordTrace tailWord_1010200 prefixEnd_1010200 38423567197929838633643 := by
  unfold tailWord_1010200
  simp only [CollatzResearch.WordTrace]
  refine ⟨18422510470112701634710027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24563347293483602179613369 18422510470112701634710027)
  ·
    refine ⟨27633765705169052452065041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18422510470112701634710027 27633765705169052452065041)
    ·
      refine ⟨20725324278876789339048781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27633765705169052452065041 20725324278876789339048781)
      ·
        refine ⟨7771996604578796002143293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20725324278876789339048781 7771996604578796002143293)
        ·
          refine ⟨2914498726717048500803735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7771996604578796002143293 2914498726717048500803735)
          ·
            refine ⟨4371748090075572751205603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2914498726717048500803735 4371748090075572751205603)
            ·
              refine ⟨6557622135113359126808405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4371748090075572751205603 6557622135113359126808405)
              ·
                refine ⟨38423567197929838633643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6557622135113359126808405 38423567197929838633643)
                ·
                  rfl

theorem cell22_1010200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 9].length) (baseStart_1010200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010200 prefixEnd_1010200 := by exact prefixLift 1010200
  have htrace : WordTrace (prefixWord ++ tailWord_1010200) baseStart_1010200 baseEnd_1010200 := by
    simpa [prefixWord, tailWord_1010200, baseEnd_1010200] using wordTrace_append hprefix tailTrace_1010200
  have hstable : (prefixWord ++ tailWord_1010200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010200).length < 2 ^ (prefixWord ++ tailWord_1010200).sum := by decide
  have hdescent : baseEnd_1010200 < baseStart_1010200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010204 : List Nat := [2, 2, 3, 1, 2, 3, 1, 3, 2, 3]
def baseStart_1010204 : Nat := 118140960795 + 1010204 * 2 ^ 59
def prefixEnd_1010204 : Nat := 4983230072969 + 3 ^ 40 * 1010204 * 2
def baseEnd_1010204 : Nat := 345813474063113870602775

theorem tailTrace_1010204 : CollatzResearch.WordTrace tailWord_1010204 prefixEnd_1010204 345813474063113870602775 := by
  unfold tailWord_1010204
  simp only [CollatzResearch.WordTrace]
  refine ⟨18422583416105455976282833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24563444554807274635043777 18422583416105455976282833)
  ·
    refine ⟨13816937562079091982212125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18422583416105455976282833 13816937562079091982212125)
    ·
      refine ⟨5181351585779659493329547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13816937562079091982212125 5181351585779659493329547)
      ·
        refine ⟨7772027378669489239994321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5181351585779659493329547 7772027378669489239994321)
        ·
          refine ⟨5829020534002116929995741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7772027378669489239994321 5829020534002116929995741)
          ·
            refine ⟨2185882700250793848748403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5829020534002116929995741 2185882700250793848748403)
            ·
              refine ⟨3278824050376190773122605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2185882700250793848748403 3278824050376190773122605)
              ·
                refine ⟨1229559018891071539920977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3278824050376190773122605 1229559018891071539920977)
                ·
                  refine ⟨922169264168303654940733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1229559018891071539920977 922169264168303654940733)
                  ·
                    refine ⟨345813474063113870602775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 922169264168303654940733 345813474063113870602775)
                    ·
                      rfl

theorem cell22_1010204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_1010204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010204 prefixEnd_1010204 := by exact prefixLift 1010204
  have htrace : WordTrace (prefixWord ++ tailWord_1010204) baseStart_1010204 baseEnd_1010204 := by
    simpa [prefixWord, tailWord_1010204, baseEnd_1010204] using wordTrace_append hprefix tailTrace_1010204
  have hstable : (prefixWord ++ tailWord_1010204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010204).length < 2 ^ (prefixWord ++ tailWord_1010204).sum := by decide
  have hdescent : baseEnd_1010204 < baseStart_1010204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010238 : List Nat := [4, 2, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_1010238 : Nat := 118140960795 + 1010238 * 2 ^ 59
def prefixEnd_1010238 : Nat := 4983230072969 + 3 ^ 40 * 1010238 * 2
def baseEnd_1010238 : Nat := 345825112957949115252671

theorem tailTrace_1010238 : CollatzResearch.WordTrace tailWord_1010238 prefixEnd_1010238 345825112957949115252671 := by
  unfold tailWord_1010238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4605800864260966969912921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24564271276058490506202245 4605800864260966969912921)
  ·
    refine ⟨3454350648195725227434691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4605800864260966969912921 3454350648195725227434691)
    ·
      refine ⟨5181525972293587841152037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3454350648195725227434691 5181525972293587841152037)
      ·
        refine ⟨971536119805047720216007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5181525972293587841152037 971536119805047720216007)
        ·
          refine ⟨1457304179707571580324011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971536119805047720216007 1457304179707571580324011)
          ·
            refine ⟨2185956269561357370486017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457304179707571580324011 2185956269561357370486017)
            ·
              refine ⟨1639467202171018027864513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2185956269561357370486017 1639467202171018027864513)
              ·
                refine ⟨1229600401628263520898385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1639467202171018027864513 1229600401628263520898385)
                ·
                  refine ⟨922200301221197640673789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1229600401628263520898385 922200301221197640673789)
                  ·
                    refine ⟨345825112957949115252671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 922200301221197640673789 345825112957949115252671)
                    ·
                      rfl

theorem cell22_1010238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_1010238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010238 prefixEnd_1010238 := by exact prefixLift 1010238
  have htrace : WordTrace (prefixWord ++ tailWord_1010238) baseStart_1010238 baseEnd_1010238 := by
    simpa [prefixWord, tailWord_1010238, baseEnd_1010238] using wordTrace_append hprefix tailTrace_1010238
  have hstable : (prefixWord ++ tailWord_1010238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010238).length < 2 ^ (prefixWord ++ tailWord_1010238).sum := by decide
  have hdescent : baseEnd_1010238 < baseStart_1010238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010270 : List Nat := [4, 4, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_1010270 : Nat := 118140960795 + 1010270 * 2 ^ 59
def prefixEnd_1010270 : Nat := 4983230072969 + 3 ^ 40 * 1010270 * 2
def baseEnd_1010270 : Nat := 345836067211911698452573

theorem tailTrace_1010270 : CollatzResearch.WordTrace tailWord_1010270 prefixEnd_1010270 345836067211911698452573 := by
  unfold tailWord_1010270
  simp only [CollatzResearch.WordTrace]
  refine ⟨4605946756246475653058533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24565049366647870149645509 4605946756246475653058533)
  ·
    refine ⟨863615016796214184948475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4605946756246475653058533 863615016796214184948475)
    ·
      refine ⟨1295422525194321277422713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 863615016796214184948475 1295422525194321277422713)
      ·
        refine ⟨971566893895740958067035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1295422525194321277422713 971566893895740958067035)
        ·
          refine ⟨1457350340843611437100553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971566893895740958067035 1457350340843611437100553)
          ·
            refine ⟨1093012755632708577825415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1457350340843611437100553 1093012755632708577825415)
            ·
              refine ⟨1639519133449062866738123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093012755632708577825415 1639519133449062866738123)
              ·
                refine ⟨2459278700173594300107185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1639519133449062866738123 2459278700173594300107185)
                ·
                  refine ⟨1844459025130195725080389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2459278700173594300107185 1844459025130195725080389)
                  ·
                    refine ⟨345836067211911698452573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1844459025130195725080389 345836067211911698452573)
                    ·
                      rfl

theorem cell22_1010270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_1010270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010270 prefixEnd_1010270 := by exact prefixLift 1010270
  have htrace : WordTrace (prefixWord ++ tailWord_1010270) baseStart_1010270 baseEnd_1010270 := by
    simpa [prefixWord, tailWord_1010270, baseEnd_1010270] using wordTrace_append hprefix tailTrace_1010270
  have hstable : (prefixWord ++ tailWord_1010270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010270).length < 2 ^ (prefixWord ++ tailWord_1010270).sum := by decide
  have hdescent : baseEnd_1010270 < baseStart_1010270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010324 : List Nat := [2, 4, 2, 2, 1, 1, 2, 2, 6]
def baseStart_1010324 : Nat := 118140960795 + 1010324 * 2 ^ 59
def prefixEnd_1010324 : Nat := 4983230072969 + 3 ^ 40 * 1010324 * 2
def baseEnd_1010324 : Nat := 115284850838491185867469

theorem tailTrace_1010324 : CollatzResearch.WordTrace tailWord_1010324 prefixEnd_1010324 115284850838491185867469 := by
  unfold tailWord_1010324
  simp only [CollatzResearch.WordTrace]
  refine ⟨18424771795888086223467013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24566362394517448297956017 18424771795888086223467013)
  ·
    refine ⟨3454644711729016166900065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18424771795888086223467013 3454644711729016166900065)
    ·
      refine ⟨2590983533796762125175049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3454644711729016166900065 2590983533796762125175049)
      ·
        refine ⟨1943237650347571593881287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2590983533796762125175049 1943237650347571593881287)
        ·
          refine ⟨2914856475521357390821931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1943237650347571593881287 2914856475521357390821931)
          ·
            refine ⟨4372284713282036086232897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2914856475521357390821931 4372284713282036086232897)
            ·
              refine ⟨3279213534961527064674673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4372284713282036086232897 3279213534961527064674673)
              ·
                refine ⟨2459410151221145298506005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3279213534961527064674673 2459410151221145298506005)
                ·
                  refine ⟨115284850838491185867469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2459410151221145298506005 115284850838491185867469)
                  ·
                    rfl

theorem cell22_1010324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_1010324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010324 prefixEnd_1010324 := by exact prefixLift 1010324
  have htrace : WordTrace (prefixWord ++ tailWord_1010324) baseStart_1010324 baseEnd_1010324 := by
    simpa [prefixWord, tailWord_1010324, baseEnd_1010324] using wordTrace_append hprefix tailTrace_1010324
  have hstable : (prefixWord ++ tailWord_1010324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010324).length < 2 ^ (prefixWord ++ tailWord_1010324).sum := by decide
  have hdescent : baseEnd_1010324 < baseStart_1010324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010358 : List Nat := [5, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_1010358 : Nat := 118140960795 + 1010358 * 2 ^ 59
def prefixEnd_1010358 : Nat := 4983230072969 + 3 ^ 40 * 1010358 * 2
def baseEnd_1010358 : Nat := 115288730470102934084101

theorem tailTrace_1010358 : CollatzResearch.WordTrace tailWord_1010358 prefixEnd_1010358 115288730470102934084101 := by
  unfold tailWord_1010358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2303173979603312265854483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24567189115768664169114485 2303173979603312265854483)
  ·
    refine ⟨3454760969404968398781725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2303173979603312265854483 3454760969404968398781725)
    ·
      refine ⟨1295535363526863149543147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3454760969404968398781725 1295535363526863149543147)
      ·
        refine ⟨1943303045290294724314721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1295535363526863149543147 1943303045290294724314721)
        ·
          refine ⟨1457477283967721043236041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1943303045290294724314721 1457477283967721043236041)
          ·
            refine ⟨1093107962975790782427031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1457477283967721043236041 1093107962975790782427031)
            ·
              refine ⟨1639661944463686173640547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093107962975790782427031 1639661944463686173640547)
              ·
                refine ⟨2459492916695529260460821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1639661944463686173640547 2459492916695529260460821)
                ·
                  refine ⟨115288730470102934084101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2459492916695529260460821 115288730470102934084101)
                  ·
                    rfl

theorem cell22_1010358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_1010358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010358 prefixEnd_1010358 := by exact prefixLift 1010358
  have htrace : WordTrace (prefixWord ++ tailWord_1010358) baseStart_1010358 baseEnd_1010358 := by
    simpa [prefixWord, tailWord_1010358, baseEnd_1010358] using wordTrace_append hprefix tailTrace_1010358
  have hstable : (prefixWord ++ tailWord_1010358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010358).length < 2 ^ (prefixWord ++ tailWord_1010358).sum := by decide
  have hdescent : baseEnd_1010358 < baseStart_1010358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010412 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 2, 5]
def baseStart_1010412 : Nat := 118140960795 + 1010412 * 2 ^ 59
def prefixEnd_1010412 : Nat := 4983230072969 + 3 ^ 40 * 1010412 * 2
def baseEnd_1010412 : Nat := 345884676713870661402137

theorem tailTrace_1010412 : CollatzResearch.WordTrace tailWord_1010412 prefixEnd_1010412 345884676713870661402137 := by
  unfold tailWord_1010412
  simp only [CollatzResearch.WordTrace]
  refine ⟨18426376607728681738068745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24568502143638242317424993 18426376607728681738068745)
  ·
    refine ⟨13819782455796511303551559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18426376607728681738068745 13819782455796511303551559)
    ·
      refine ⟨20729673683694766955327339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13819782455796511303551559 20729673683694766955327339)
      ·
        refine ⟨31094510525542150432991009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20729673683694766955327339 31094510525542150432991009)
        ·
          refine ⟨23320882894156612824743257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31094510525542150432991009 23320882894156612824743257)
          ·
            refine ⟨17490662170617459618557443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23320882894156612824743257 17490662170617459618557443)
            ·
              refine ⟨26235993255926189427836165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17490662170617459618557443 26235993255926189427836165)
              ·
                refine ⟨4919248735486160517719281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26235993255926189427836165 4919248735486160517719281)
                ·
                  refine ⟨3689436551614620388289461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4919248735486160517719281 3689436551614620388289461)
                  ·
                    refine ⟨345884676713870661402137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3689436551614620388289461 345884676713870661402137)
                    ·
                      rfl

theorem cell22_1010412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_1010412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010412 prefixEnd_1010412 := by exact prefixLift 1010412
  have htrace : WordTrace (prefixWord ++ tailWord_1010412) baseStart_1010412 baseEnd_1010412 := by
    simpa [prefixWord, tailWord_1010412, baseEnd_1010412] using wordTrace_append hprefix tailTrace_1010412
  have hstable : (prefixWord ++ tailWord_1010412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010412).length < 2 ^ (prefixWord ++ tailWord_1010412).sum := by decide
  have hdescent : baseEnd_1010412 < baseStart_1010412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010414 : List Nat := [4, 1, 2, 1, 1, 3, 1, 4, 5]
def baseStart_1010414 : Nat := 118140960795 + 1010414 * 2 ^ 59
def prefixEnd_1010414 : Nat := 4983230072969 + 3 ^ 40 * 1010414 * 2
def baseEnd_1010414 : Nat := 115295120451581107617377

theorem tailTrace_1010414 : CollatzResearch.WordTrace tailWord_1010414 prefixEnd_1010414 115295120451581107617377 := by
  unfold tailWord_1010414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4606603270181264727213787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24568550774300078545140197 4606603270181264727213787)
  ·
    refine ⟨6909904905271897090820681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4606603270181264727213787 6909904905271897090820681)
    ·
      refine ⟨5182428678953922818115511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6909904905271897090820681 5182428678953922818115511)
      ·
        refine ⟨7773643018430884227173267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5182428678953922818115511 7773643018430884227173267)
        ·
          refine ⟨11660464527646326340759901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7773643018430884227173267 11660464527646326340759901)
          ·
            refine ⟨4372674197867372377784963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11660464527646326340759901 4372674197867372377784963)
            ·
              refine ⟨6559011296801058566677445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4372674197867372377784963 6559011296801058566677445)
              ·
                refine ⟨1229814618150198481252021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6559011296801058566677445 1229814618150198481252021)
                ·
                  refine ⟨115295120451581107617377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1229814618150198481252021 115295120451581107617377)
                  ·
                    rfl

theorem cell22_1010414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_1010414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010414 prefixEnd_1010414 := by exact prefixLift 1010414
  have htrace : WordTrace (prefixWord ++ tailWord_1010414) baseStart_1010414 baseEnd_1010414 := by
    simpa [prefixWord, tailWord_1010414, baseEnd_1010414] using wordTrace_append hprefix tailTrace_1010414
  have hstable : (prefixWord ++ tailWord_1010414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010414).length < 2 ^ (prefixWord ++ tailWord_1010414).sum := by decide
  have hdescent : baseEnd_1010414 < baseStart_1010414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010418 : List Nat := [3, 2, 1, 3, 1, 3, 1, 4, 1, 3]
def baseStart_1010418 : Nat := 118140960795 + 1010418 * 2 ^ 59
def prefixEnd_1010418 : Nat := 4983230072969 + 3 ^ 40 * 1010418 * 2
def baseEnd_1010418 : Nat := 345886730636488645752119

theorem tailTrace_1010418 : CollatzResearch.WordTrace tailWord_1010418 prefixEnd_1010418 345886730636488645752119 := by
  unfold tailWord_1010418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9213243013358906625213977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24568648035623751000570605 9213243013358906625213977)
  ·
    refine ⟨6909932260019179968910483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9213243013358906625213977 6909932260019179968910483)
    ·
      refine ⟨10364898390028769953365725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6909932260019179968910483 10364898390028769953365725)
      ·
        refine ⟨3886836896260788732512147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10364898390028769953365725 3886836896260788732512147)
        ·
          refine ⟨5830255344391183098768221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3886836896260788732512147 5830255344391183098768221)
          ·
            refine ⟨2186345754146693662038083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5830255344391183098768221 2186345754146693662038083)
            ·
              refine ⟨3279518631220040493057125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2186345754146693662038083 3279518631220040493057125)
              ·
                refine ⟨614909743353757592448211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3279518631220040493057125 614909743353757592448211)
                ·
                  refine ⟨922364615030636388672317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 614909743353757592448211 922364615030636388672317)
                  ·
                    refine ⟨345886730636488645752119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 922364615030636388672317 345886730636488645752119)
                    ·
                      rfl

theorem cell22_1010418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_1010418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010418 prefixEnd_1010418 := by exact prefixLift 1010418
  have htrace : WordTrace (prefixWord ++ tailWord_1010418) baseStart_1010418 baseEnd_1010418 := by
    simpa [prefixWord, tailWord_1010418, baseEnd_1010418] using wordTrace_append hprefix tailTrace_1010418
  have hstable : (prefixWord ++ tailWord_1010418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010418).length < 2 ^ (prefixWord ++ tailWord_1010418).sum := by decide
  have hdescent : baseEnd_1010418 < baseStart_1010418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010420 : List Nat := [2, 6, 1, 1, 3, 1, 1, 7]
def baseStart_1010420 : Nat := 118140960795 + 1010420 * 2 ^ 59
def prefixEnd_1010420 : Nat := 4983230072969 + 3 ^ 40 * 1010420 * 2
def baseEnd_1010420 : Nat := 38431935030817923022457

theorem tailTrace_1010420 : CollatzResearch.WordTrace tailWord_1010420 prefixEnd_1010420 38431935030817923022457 := by
  unfold tailWord_1010420
  simp only [CollatzResearch.WordTrace]
  refine ⟨18426522499714190421214357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24568696666285587228285809 18426522499714190421214357)
  ·
    refine ⟨863743242174102675994423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18426522499714190421214357 863743242174102675994423)
    ·
      refine ⟨1295614863261154013991635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 863743242174102675994423 1295614863261154013991635)
      ·
        refine ⟨1943422294891731020987453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1295614863261154013991635 1943422294891731020987453)
        ·
          refine ⟨728783360584399132870295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1943422294891731020987453 728783360584399132870295)
          ·
            refine ⟨1093175040876598699305443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728783360584399132870295 1093175040876598699305443)
            ·
              refine ⟨1639762561314898048958165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093175040876598699305443 1639762561314898048958165)
              ·
                refine ⟨38431935030817923022457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1639762561314898048958165 38431935030817923022457)
                ·
                  rfl

theorem cell22_1010420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 7].length) (baseStart_1010420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010420 prefixEnd_1010420 := by exact prefixLift 1010420
  have htrace : WordTrace (prefixWord ++ tailWord_1010420) baseStart_1010420 baseEnd_1010420 := by
    simpa [prefixWord, tailWord_1010420, baseEnd_1010420] using wordTrace_append hprefix tailTrace_1010420
  have hstable : (prefixWord ++ tailWord_1010420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010420).length < 2 ^ (prefixWord ++ tailWord_1010420).sum := by decide
  have hdescent : baseEnd_1010420 < baseStart_1010420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010444 : List Nat := [2, 2, 1, 2, 2, 1, 1, 6, 1, 4]
def baseStart_1010444 : Nat := 118140960795 + 1010444 * 2 ^ 59
def prefixEnd_1010444 : Nat := 4983230072969 + 3 ^ 40 * 1010444 * 2
def baseEnd_1010444 : Nat := 345895630967833244602039

theorem tailTrace_1010444 : CollatzResearch.WordTrace tailWord_1010444 prefixEnd_1010444 345895630967833244602039 := by
  unfold tailWord_1010444
  simp only [CollatzResearch.WordTrace]
  refine ⟨18426960175670716470651193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24569280234227621960868257 18426960175670716470651193)
  ·
    refine ⟨13820220131753037352988395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18426960175670716470651193 13820220131753037352988395)
    ·
      refine ⟨20730330197629556029482593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13820220131753037352988395 20730330197629556029482593)
      ·
        refine ⟨15547747648222167022111945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20730330197629556029482593 15547747648222167022111945)
        ·
          refine ⟨11660810736166625266583959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15547747648222167022111945 11660810736166625266583959)
          ·
            refine ⟨17491216104249937899875939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11660810736166625266583959 17491216104249937899875939)
            ·
              refine ⟨26236824156374906849813909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17491216104249937899875939 26236824156374906849813909)
              ·
                refine ⟨1229851132330073758585027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26236824156374906849813909 1229851132330073758585027)
                ·
                  refine ⟨1844776698495110637877541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1229851132330073758585027 1844776698495110637877541)
                  ·
                    refine ⟨345895630967833244602039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1844776698495110637877541 345895630967833244602039)
                    ·
                      rfl

theorem cell22_1010444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_1010444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010444 prefixEnd_1010444 := by exact prefixLift 1010444
  have htrace : WordTrace (prefixWord ++ tailWord_1010444) baseStart_1010444 baseEnd_1010444 := by
    simpa [prefixWord, tailWord_1010444, baseEnd_1010444] using wordTrace_append hprefix tailTrace_1010444
  have hstable : (prefixWord ++ tailWord_1010444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010444).length < 2 ^ (prefixWord ++ tailWord_1010444).sum := by decide
  have hdescent : baseEnd_1010444 < baseStart_1010444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010457 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 3, 5]
def baseStart_1010457 : Nat := 118140960795 + 1010457 * 2 ^ 59
def prefixEnd_1010457 : Nat := 4983230072969 + 3 ^ 40 * 1010457 * 2
def baseEnd_1010457 : Nat := 345900081133505544026999

theorem tailTrace_1010457 : CollatzResearch.WordTrace tailWord_1010457 prefixEnd_1010457 345900081133505544026999 := by
  unfold tailWord_1010457
  simp only [CollatzResearch.WordTrace]
  refine ⟨36854394500294336161525625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24569596333529557441017083 36854394500294336161525625)
  ·
    refine ⟨27640795875220752121144219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36854394500294336161525625 27640795875220752121144219)
    ·
      refine ⟨41461193812831128181716329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27640795875220752121144219 41461193812831128181716329)
      ·
        refine ⟨31095895359623346136287247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41461193812831128181716329 31095895359623346136287247)
        ·
          refine ⟨46643843039435019204430871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31095895359623346136287247 46643843039435019204430871)
          ·
            refine ⟨69965764559152528806646307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46643843039435019204430871 69965764559152528806646307)
            ·
              refine ⟨104948646838728793209969461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69965764559152528806646307 104948646838728793209969461)
              ·
                refine ⟨9838935641130824363434637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104948646838728793209969461 9838935641130824363434637)
                ·
                  refine ⟨3689600865424059136287989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9838935641130824363434637 3689600865424059136287989)
                  ·
                    refine ⟨345900081133505544026999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3689600865424059136287989 345900081133505544026999)
                    ·
                      rfl

theorem cell22_1010457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_1010457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010457 prefixEnd_1010457 := by exact prefixLift 1010457
  have htrace : WordTrace (prefixWord ++ tailWord_1010457) baseStart_1010457 baseEnd_1010457 := by
    simpa [prefixWord, tailWord_1010457, baseEnd_1010457] using wordTrace_append hprefix tailTrace_1010457
  have hstable : (prefixWord ++ tailWord_1010457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010457).length < 2 ^ (prefixWord ++ tailWord_1010457).sum := by decide
  have hdescent : baseEnd_1010457 < baseStart_1010457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010487 : List Nat := [1, 1, 3, 1, 2, 1, 4, 9]
def baseStart_1010487 : Nat := 118140960795 + 1010487 * 2 ^ 59
def prefixEnd_1010487 : Nat := 4983230072969 + 3 ^ 40 * 1010487 * 2
def baseEnd_1010487 : Nat := 38434483416288385086323

theorem tailTrace_1010487 : CollatzResearch.WordTrace tailWord_1010487 prefixEnd_1010487 38434483416288385086323 := by
  unfold tailWord_1010487
  simp only [CollatzResearch.WordTrace]
  refine ⟨36855488690185651285117715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24570325793457100856745143 36855488690185651285117715)
  ·
    refine ⟨55283233035278476927676573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36855488690185651285117715 55283233035278476927676573)
    ·
      refine ⟨20731212388229428847878715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55283233035278476927676573 20731212388229428847878715)
      ·
        refine ⟨31096818582344143271818073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20731212388229428847878715 31096818582344143271818073)
        ·
          refine ⟨23322613936758107453863555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31096818582344143271818073 23322613936758107453863555)
          ·
            refine ⟨34983920905137161180795333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23322613936758107453863555 34983920905137161180795333)
            ·
              refine ⟨6559485169713217721399125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34983920905137161180795333 6559485169713217721399125)
              ·
                refine ⟨38434483416288385086323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6559485169713217721399125 38434483416288385086323)
                ·
                  rfl

theorem cell22_1010487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 9].length) (baseStart_1010487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010487 prefixEnd_1010487 := by exact prefixLift 1010487
  have htrace : WordTrace (prefixWord ++ tailWord_1010487) baseStart_1010487 baseEnd_1010487 := by
    simpa [prefixWord, tailWord_1010487, baseEnd_1010487] using wordTrace_append hprefix tailTrace_1010487
  have hstable : (prefixWord ++ tailWord_1010487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010487).length < 2 ^ (prefixWord ++ tailWord_1010487).sum := by decide
  have hdescent : baseEnd_1010487 < baseStart_1010487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010542 : List Nat := [4, 1, 2, 3, 2, 2, 2, 1, 2, 3]
def baseStart_1010542 : Nat := 118140960795 + 1010542 * 2 ^ 59
def prefixEnd_1010542 : Nat := 4983230072969 + 3 ^ 40 * 1010542 * 2
def baseEnd_1010542 : Nat := 345929178370593655651739

theorem tailTrace_1010542 : CollatzResearch.WordTrace tailWord_1010542 prefixEnd_1010542 345929178370593655651739 := by
  unfold tailWord_1010542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4607186838123299459796235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24571663136657597118913253 4607186838123299459796235)
  ·
    refine ⟨6910780257184949189694353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4607186838123299459796235 6910780257184949189694353)
    ·
      refine ⟨5183085192888711892270765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6910780257184949189694353 5183085192888711892270765)
      ·
        refine ⟨1943656947333266959601537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5183085192888711892270765 1943656947333266959601537)
        ·
          refine ⟨1457742710499950219701153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1943656947333266959601537 1457742710499950219701153)
          ·
            refine ⟨1093307032874962664775865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1457742710499950219701153 1093307032874962664775865)
            ·
              refine ⟨819980274656221998581899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1093307032874962664775865 819980274656221998581899)
              ·
                refine ⟨1229970411984332997872849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819980274656221998581899 1229970411984332997872849)
                ·
                  refine ⟨922477808988249748404637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1229970411984332997872849 922477808988249748404637)
                  ·
                    refine ⟨345929178370593655651739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 922477808988249748404637 345929178370593655651739)
                    ·
                      rfl

theorem cell22_1010542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_1010542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010542 prefixEnd_1010542 := by exact prefixLift 1010542
  have htrace : WordTrace (prefixWord ++ tailWord_1010542) baseStart_1010542 baseEnd_1010542 := by
    simpa [prefixWord, tailWord_1010542, baseEnd_1010542] using wordTrace_append hprefix tailTrace_1010542
  have hstable : (prefixWord ++ tailWord_1010542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010542).length < 2 ^ (prefixWord ++ tailWord_1010542).sum := by decide
  have hdescent : baseEnd_1010542 < baseStart_1010542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010564 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_1010564 : Nat := 118140960795 + 1010564 * 2 ^ 59
def prefixEnd_1010564 : Nat := 4983230072969 + 3 ^ 40 * 1010564 * 2
def baseEnd_1010564 : Nat := 345936709420192931601671

theorem tailTrace_1010564 : CollatzResearch.WordTrace tailWord_1010564 prefixEnd_1010564 345936709420192931601671 := by
  unfold tailWord_1010564
  simp only [CollatzResearch.WordTrace]
  refine ⟨18429148555453346717835373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24572198073937795623780497 18429148555453346717835373)
  ·
    refine ⟨6910930708295005019188265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18429148555453346717835373 6910930708295005019188265)
    ·
      refine ⟨5183198031221253764391199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6910930708295005019188265 5183198031221253764391199)
      ·
        refine ⟨7774797046831880646586799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5183198031221253764391199 7774797046831880646586799)
        ·
          refine ⟨11662195570247820969880199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7774797046831880646586799 11662195570247820969880199)
          ·
            refine ⟨17493293355371731454820299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11662195570247820969880199 17493293355371731454820299)
            ·
              refine ⟨26239940033057597182230449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17493293355371731454820299 26239940033057597182230449)
              ·
                refine ⟨19679955024793197886672837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26239940033057597182230449 19679955024793197886672837)
                ·
                  refine ⟨3689991567148724603751157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19679955024793197886672837 3689991567148724603751157)
                  ·
                    refine ⟨345936709420192931601671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3689991567148724603751157 345936709420192931601671)
                    ·
                      rfl

theorem cell22_1010564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_1010564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010564 prefixEnd_1010564 := by exact prefixLift 1010564
  have htrace : WordTrace (prefixWord ++ tailWord_1010564) baseStart_1010564 baseEnd_1010564 := by
    simpa [prefixWord, tailWord_1010564, baseEnd_1010564] using wordTrace_append hprefix tailTrace_1010564
  have hstable : (prefixWord ++ tailWord_1010564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010564).length < 2 ^ (prefixWord ++ tailWord_1010564).sum := by decide
  have hdescent : baseEnd_1010564 < baseStart_1010564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010639 : List Nat := [1, 1, 2, 1, 1, 7, 9]
def baseStart_1010639 : Nat := 118140960795 + 1010639 * 2 ^ 59
def prefixEnd_1010639 : Nat := 4983230072969 + 3 ^ 40 * 1010639 * 2
def baseEnd_1010639 : Nat := 12813421609367323554683

theorem tailTrace_1010639 : CollatzResearch.WordTrace tailWord_1010639 prefixEnd_1010639 12813421609367323554683 := by
  unfold tailWord_1010639
  simp only [CollatzResearch.WordTrace]
  refine ⟨36861032585634981244650971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24574021723756654163100647 36861032585634981244650971)
  ·
    refine ⟨55291548878452471866976457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36861032585634981244650971 55291548878452471866976457)
    ·
      refine ⟨41468661658839353900232343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55291548878452471866976457 41468661658839353900232343)
      ·
        refine ⟨62202992488259030850348515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41468661658839353900232343 62202992488259030850348515)
        ·
          refine ⟨93304488732388546275522773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62202992488259030850348515 93304488732388546275522773)
          ·
            refine ⟨2186823954665356553332565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 93304488732388546275522773 2186823954665356553332565)
            ·
              refine ⟨12813421609367323554683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2186823954665356553332565 12813421609367323554683)
              ·
                rfl

theorem cell22_1010639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 9].length) (baseStart_1010639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010639 prefixEnd_1010639 := by exact prefixLift 1010639
  have htrace : WordTrace (prefixWord ++ tailWord_1010639) baseStart_1010639 baseEnd_1010639 := by
    simpa [prefixWord, tailWord_1010639, baseEnd_1010639] using wordTrace_append hprefix tailTrace_1010639
  have hstable : (prefixWord ++ tailWord_1010639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010639).length < 2 ^ (prefixWord ++ tailWord_1010639).sum := by decide
  have hdescent : baseEnd_1010639 < baseStart_1010639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010658 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1010658 : Nat := 118140960795 + 1010658 * 2 ^ 59
def prefixEnd_1010658 : Nat := 4983230072969 + 3 ^ 40 * 1010658 * 2
def baseEnd_1010658 : Nat := 345968887541208019751383

theorem tailTrace_1010658 : CollatzResearch.WordTrace tailWord_1010658 prefixEnd_1010658 345968887541208019751383 := by
  unfold tailWord_1010658
  simp only [CollatzResearch.WordTrace]
  refine ⟨9215431393141536872398157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24574483715044098326395085 9215431393141536872398157)
  ·
    refine ⟨3455786772428076327149309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9215431393141536872398157 3455786772428076327149309)
    ·
      refine ⟨1295920039660528622680991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3455786772428076327149309 1295920039660528622680991)
      ·
        refine ⟨1943880059490792934021487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1295920039660528622680991 1943880059490792934021487)
        ·
          refine ⟨2915820089236189401032231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1943880059490792934021487 2915820089236189401032231)
          ·
            refine ⟨4373730133854284101548347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2915820089236189401032231 4373730133854284101548347)
            ·
              refine ⟨6560595200781426152322521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4373730133854284101548347 6560595200781426152322521)
              ·
                refine ⟨4920446400586069614241891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6560595200781426152322521 4920446400586069614241891)
                ·
                  refine ⟨7380669600879104421362837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4920446400586069614241891 7380669600879104421362837)
                  ·
                    refine ⟨345968887541208019751383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7380669600879104421362837 345968887541208019751383)
                    ·
                      rfl

theorem cell22_1010658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1010658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010658 prefixEnd_1010658 := by exact prefixLift 1010658
  have htrace : WordTrace (prefixWord ++ tailWord_1010658) baseStart_1010658 baseEnd_1010658 := by
    simpa [prefixWord, tailWord_1010658, baseEnd_1010658] using wordTrace_append hprefix tailTrace_1010658
  have hstable : (prefixWord ++ tailWord_1010658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010658).length < 2 ^ (prefixWord ++ tailWord_1010658).sum := by decide
  have hdescent : baseEnd_1010658 < baseStart_1010658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010673 : List Nat := [1, 2, 2, 2, 4, 3, 2, 6]
def baseStart_1010673 : Nat := 118140960795 + 1010673 * 2 ^ 59
def prefixEnd_1010673 : Nat := 4983230072969 + 3 ^ 40 * 1010673 * 2
def baseEnd_1010673 : Nat := 38441558038639220069593

theorem tailTrace_1010673 : CollatzResearch.WordTrace tailWord_1010673 prefixEnd_1010673 38441558038639220069593 := by
  unfold tailWord_1010673
  simp only [CollatzResearch.WordTrace]
  refine ⟨36862272667511805051388673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24574848445007870034259115 36862272667511805051388673)
  ·
    refine ⟨27646704500633853788541505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36862272667511805051388673 27646704500633853788541505)
    ·
      refine ⟨20735028375475390341406129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27646704500633853788541505 20735028375475390341406129)
      ·
        refine ⟨15551271281606542756054597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20735028375475390341406129 15551271281606542756054597)
        ·
          refine ⟨2915863365301226766760237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15551271281606542756054597 2915863365301226766760237)
          ·
            refine ⟨1093448761987960037535089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2915863365301226766760237 1093448761987960037535089)
            ·
              refine ⟨820086571490970028151317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1093448761987960037535089 820086571490970028151317)
              ·
                refine ⟨38441558038639220069593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 820086571490970028151317 38441558038639220069593)
                ·
                  rfl

theorem cell22_1010673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 6].length) (baseStart_1010673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010673 prefixEnd_1010673 := by exact prefixLift 1010673
  have htrace : WordTrace (prefixWord ++ tailWord_1010673) baseStart_1010673 baseEnd_1010673 := by
    simpa [prefixWord, tailWord_1010673, baseEnd_1010673] using wordTrace_append hprefix tailTrace_1010673
  have hstable : (prefixWord ++ tailWord_1010673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010673).length < 2 ^ (prefixWord ++ tailWord_1010673).sum := by decide
  have hdescent : baseEnd_1010673 < baseStart_1010673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010690 : List Nat := [3, 4, 1, 3, 1, 2, 8]
def baseStart_1010690 : Nat := 118140960795 + 1010690 * 2 ^ 59
def prefixEnd_1010690 : Nat := 4983230072969 + 3 ^ 40 * 1010690 * 2
def baseEnd_1010690 : Nat := 12814068214635948257455

theorem tailTrace_1010690 : CollatzResearch.WordTrace tailWord_1010690 prefixEnd_1010690 12814068214635948257455 := by
  unfold tailWord_1010690
  simp only [CollatzResearch.WordTrace]
  refine ⟨9215723177112554238689381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24575261805633477969838349 9215723177112554238689381)
  ·
    refine ⟨1727948095708603919754259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9215723177112554238689381 1727948095708603919754259)
    ·
      refine ⟨2591922143562905879631389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1727948095708603919754259 2591922143562905879631389)
      ·
        refine ⟨971970803836089704861771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2591922143562905879631389 971970803836089704861771)
        ·
          refine ⟨1457956205754134557292657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971970803836089704861771 1457956205754134557292657)
          ·
            refine ⟨1093467154315600917969493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1457956205754134557292657 1093467154315600917969493)
            ·
              refine ⟨12814068214635948257455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1093467154315600917969493 12814068214635948257455)
              ·
                rfl

theorem cell22_1010690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 8].length) (baseStart_1010690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010690 prefixEnd_1010690 := by exact prefixLift 1010690
  have htrace : WordTrace (prefixWord ++ tailWord_1010690) baseStart_1010690 baseEnd_1010690 := by
    simpa [prefixWord, tailWord_1010690, baseEnd_1010690] using wordTrace_append hprefix tailTrace_1010690
  have hstable : (prefixWord ++ tailWord_1010690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010690).length < 2 ^ (prefixWord ++ tailWord_1010690).sum := by decide
  have hdescent : baseEnd_1010690 < baseStart_1010690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010731 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 3, 4]
def baseStart_1010731 : Nat := 118140960795 + 1010731 * 2 ^ 59
def prefixEnd_1010731 : Nat := 4983230072969 + 3 ^ 40 * 1010731 * 2
def baseEnd_1010731 : Nat := 345993876933060162676159

theorem tailTrace_1010731 : CollatzResearch.WordTrace tailWord_1010731 prefixEnd_1010731 345993876933060162676159 := by
  unfold tailWord_1010731
  simp only [CollatzResearch.WordTrace]
  refine ⟨36864388101301680957000047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24576258734201120638000031 36864388101301680957000047)
  ·
    refine ⟨55296582151952521435500071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36864388101301680957000047 55296582151952521435500071)
    ·
      refine ⟨82944873227928782153250107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55296582151952521435500071 82944873227928782153250107)
      ·
        refine ⟨124417309841893173229875161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82944873227928782153250107 124417309841893173229875161)
        ·
          refine ⟨93312982381419879922406371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124417309841893173229875161 93312982381419879922406371)
          ·
            refine ⟨139969473572129819883609557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93312982381419879922406371 139969473572129819883609557)
            ·
              refine ⟨3280534536846792653522099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 139969473572129819883609557 3280534536846792653522099)
              ·
                refine ⟨4920801805270188980283149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3280534536846792653522099 4920801805270188980283149)
                ·
                  refine ⟨1845300676976320867606181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4920801805270188980283149 1845300676976320867606181)
                  ·
                    refine ⟨345993876933060162676159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1845300676976320867606181 345993876933060162676159)
                    ·
                      rfl

theorem cell22_1010731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 4].length) (baseStart_1010731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010731 prefixEnd_1010731 := by exact prefixLift 1010731
  have htrace : WordTrace (prefixWord ++ tailWord_1010731) baseStart_1010731 baseEnd_1010731 := by
    simpa [prefixWord, tailWord_1010731, baseEnd_1010731] using wordTrace_append hprefix tailTrace_1010731
  have hstable : (prefixWord ++ tailWord_1010731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010731).length < 2 ^ (prefixWord ++ tailWord_1010731).sum := by decide
  have hdescent : baseEnd_1010731 < baseStart_1010731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010776 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 1, 6]
def baseStart_1010776 : Nat := 118140960795 + 1010776 * 2 ^ 59
def prefixEnd_1010776 : Nat := 4983230072969 + 3 ^ 40 * 1010776 * 2
def baseEnd_1010776 : Nat := 346009281352695045301021

theorem tailTrace_1010776 : CollatzResearch.WordTrace tailWord_1010776 prefixEnd_1010776 346009281352695045301021 := by
  unfold tailWord_1010776
  simp only [CollatzResearch.WordTrace]
  refine ⟨18433014693069326821194091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24577352924092435761592121 18433014693069326821194091)
  ·
    refine ⟨27649522039603990231791137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18433014693069326821194091 27649522039603990231791137)
    ·
      refine ⟨20737141529702992673843353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27649522039603990231791137 20737141529702992673843353)
      ·
        refine ⟨15552856147277244505382515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20737141529702992673843353 15552856147277244505382515)
        ·
          refine ⟨23329284220915866758073773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15552856147277244505382515 23329284220915866758073773)
          ·
            refine ⟨8748481582843450034277665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23329284220915866758073773 8748481582843450034277665)
            ·
              refine ⟨6561361187132587525708249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8748481582843450034277665 6561361187132587525708249)
              ·
                refine ⟨4921020890349440644281187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6561361187132587525708249 4921020890349440644281187)
                ·
                  refine ⟨7381531335524160966421781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4921020890349440644281187 7381531335524160966421781)
                  ·
                    refine ⟨346009281352695045301021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7381531335524160966421781 346009281352695045301021)
                    ·
                      rfl

theorem cell22_1010776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_1010776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010776 prefixEnd_1010776 := by exact prefixLift 1010776
  have htrace : WordTrace (prefixWord ++ tailWord_1010776) baseStart_1010776 baseEnd_1010776 := by
    simpa [prefixWord, tailWord_1010776, baseEnd_1010776] using wordTrace_append hprefix tailTrace_1010776
  have hstable : (prefixWord ++ tailWord_1010776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010776).length < 2 ^ (prefixWord ++ tailWord_1010776).sum := by decide
  have hdescent : baseEnd_1010776 < baseStart_1010776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010782 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1010782 : Nat := 118140960795 + 1010782 * 2 ^ 59
def prefixEnd_1010782 : Nat := 4983230072969 + 3 ^ 40 * 1010782 * 2
def baseEnd_1010782 : Nat := 346011335275313029651003

theorem tailTrace_1010782 : CollatzResearch.WordTrace tailWord_1010782 prefixEnd_1010782 346011335275313029651003 := by
  unfold tailWord_1010782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4608281028014614583388325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24577498816077944444737733 4608281028014614583388325)
  ·
    refine ⟨864052692752740234385311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4608281028014614583388325 864052692752740234385311)
    ·
      refine ⟨1296079039129110351577967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 864052692752740234385311 1296079039129110351577967)
      ·
        refine ⟨1944118558693665527366951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1296079039129110351577967 1944118558693665527366951)
        ·
          refine ⟨2916177838040498291050427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1944118558693665527366951 2916177838040498291050427)
          ·
            refine ⟨4374266757060747436575641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2916177838040498291050427 4374266757060747436575641)
            ·
              refine ⟨3280700067795560577431731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4374266757060747436575641 3280700067795560577431731)
              ·
                refine ⟨4921050101693340866147597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3280700067795560577431731 4921050101693340866147597)
                ·
                  refine ⟨1845393788135002824805349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4921050101693340866147597 1845393788135002824805349)
                  ·
                    refine ⟨346011335275313029651003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1845393788135002824805349 346011335275313029651003)
                    ·
                      rfl

theorem cell22_1010782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1010782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010782 prefixEnd_1010782 := by exact prefixLift 1010782
  have htrace : WordTrace (prefixWord ++ tailWord_1010782) baseStart_1010782 baseEnd_1010782 := by
    simpa [prefixWord, tailWord_1010782, baseEnd_1010782] using wordTrace_append hprefix tailTrace_1010782
  have hstable : (prefixWord ++ tailWord_1010782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010782).length < 2 ^ (prefixWord ++ tailWord_1010782).sum := by decide
  have hdescent : baseEnd_1010782 < baseStart_1010782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010793 : List Nat := [1, 2, 1, 1, 1, 6, 3, 1, 2, 4]
def baseStart_1010793 : Nat := 118140960795 + 1010793 * 2 ^ 59
def prefixEnd_1010793 : Nat := 4983230072969 + 3 ^ 40 * 1010793 * 2
def baseEnd_1010793 : Nat := 346015100800112667625969

theorem tailTrace_1010793 : CollatzResearch.WordTrace tailWord_1010793 prefixEnd_1010793 346015100800112667625969 := by
  unfold tailWord_1010793
  simp only [CollatzResearch.WordTrace]
  refine ⟨36866649427077065545757033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24577766284718043697171355 36866649427077065545757033)
  ·
    refine ⟨27649987070307799159317775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36866649427077065545757033 27649987070307799159317775)
    ·
      refine ⟨41474980605461698738976663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27649987070307799159317775 41474980605461698738976663)
      ·
        refine ⟨62212470908192548108464995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41474980605461698738976663 62212470908192548108464995)
        ·
          refine ⟨93318706362288822162697493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62212470908192548108464995 93318706362288822162697493)
          ·
            refine ⟨4374314360732288538876445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93318706362288822162697493 4374314360732288538876445)
            ·
              refine ⟨1640367885274608202078667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4374314360732288538876445 1640367885274608202078667)
              ·
                refine ⟨2460551827911912303118001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640367885274608202078667 2460551827911912303118001)
                ·
                  refine ⟨1845413870933934227338501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2460551827911912303118001 1845413870933934227338501)
                  ·
                    refine ⟨346015100800112667625969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1845413870933934227338501 346015100800112667625969)
                    ·
                      rfl

theorem cell22_1010793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 4].length) (baseStart_1010793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010793 prefixEnd_1010793 := by exact prefixLift 1010793
  have htrace : WordTrace (prefixWord ++ tailWord_1010793) baseStart_1010793 baseEnd_1010793 := by
    simpa [prefixWord, tailWord_1010793, baseEnd_1010793] using wordTrace_append hprefix tailTrace_1010793
  have hstable : (prefixWord ++ tailWord_1010793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010793).length < 2 ^ (prefixWord ++ tailWord_1010793).sum := by decide
  have hdescent : baseEnd_1010793 < baseStart_1010793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010814 : List Nat := [4, 2, 4, 1, 1, 1, 2, 1, 6]
def baseStart_1010814 : Nat := 118140960795 + 1010814 * 2 ^ 59
def prefixEnd_1010814 : Nat := 4983230072969 + 3 ^ 40 * 1010814 * 2
def baseEnd_1010814 : Nat := 115340763176425204283635

theorem tailTrace_1010814 : CollatzResearch.WordTrace tailWord_1010814 prefixEnd_1010814 115340763176425204283635 := by
  unfold tailWord_1010814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4608426920000123266533937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24578276906667324088180997 4608426920000123266533937)
  ·
    refine ⟨3456320190000092449900453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4608426920000123266533937 3456320190000092449900453)
    ·
      refine ⟨648060035625017334356335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3456320190000092449900453 648060035625017334356335)
      ·
        refine ⟨972090053437526001534503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648060035625017334356335 972090053437526001534503)
        ·
          refine ⟨1458135080156289002301755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972090053437526001534503 1458135080156289002301755)
          ·
            refine ⟨2187202620234433503452633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1458135080156289002301755 2187202620234433503452633)
            ·
              refine ⟨1640401965175825127589475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2187202620234433503452633 1640401965175825127589475)
              ·
                refine ⟨2460602947763737691384213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640401965175825127589475 2460602947763737691384213)
                ·
                  refine ⟨115340763176425204283635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2460602947763737691384213 115340763176425204283635)
                  ·
                    rfl

theorem cell22_1010814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_1010814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010814 prefixEnd_1010814 := by exact prefixLift 1010814
  have htrace : WordTrace (prefixWord ++ tailWord_1010814) baseStart_1010814 baseEnd_1010814 := by
    simpa [prefixWord, tailWord_1010814, baseEnd_1010814] using wordTrace_append hprefix tailTrace_1010814
  have hstable : (prefixWord ++ tailWord_1010814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010814).length < 2 ^ (prefixWord ++ tailWord_1010814).sum := by decide
  have hdescent : baseEnd_1010814 < baseStart_1010814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010840 : List Nat := [2, 1, 2, 4, 2, 1, 2, 2, 3, 3]
def baseStart_1010840 : Nat := 118140960795 + 1010840 * 2 ^ 59
def prefixEnd_1010840 : Nat := 4983230072969 + 3 ^ 40 * 1010840 * 2
def baseEnd_1010840 : Nat := 346031189860620211700825

theorem tailTrace_1010840 : CollatzResearch.WordTrace tailWord_1010840 prefixEnd_1010840 346031189860620211700825 := by
  unfold tailWord_1010840
  simp only [CollatzResearch.WordTrace]
  refine ⟨18434181828953396286358987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24578909105271195048478649 18434181828953396286358987)
  ·
    refine ⟨27651272743430094429538481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18434181828953396286358987 27651272743430094429538481)
    ·
      refine ⟨20738454557572570822153861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27651272743430094429538481 20738454557572570822153861)
      ·
        refine ⟨3888460229544857029153849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20738454557572570822153861 3888460229544857029153849)
        ·
          refine ⟨2916345172158642771865387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3888460229544857029153849 2916345172158642771865387)
          ·
            refine ⟨4374517758237964157798081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2916345172158642771865387 4374517758237964157798081)
            ·
              refine ⟨3280888318678473118348561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4374517758237964157798081 3280888318678473118348561)
              ·
                refine ⟨2460666239008854838761421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3280888318678473118348561 2460666239008854838761421)
                ·
                  refine ⟨922749839628320564535533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2460666239008854838761421 922749839628320564535533)
                  ·
                    refine ⟨346031189860620211700825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 922749839628320564535533 346031189860620211700825)
                    ·
                      rfl

theorem cell22_1010840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_1010840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010840 prefixEnd_1010840 := by exact prefixLift 1010840
  have htrace : WordTrace (prefixWord ++ tailWord_1010840) baseStart_1010840 baseEnd_1010840 := by
    simpa [prefixWord, tailWord_1010840, baseEnd_1010840] using wordTrace_append hprefix tailTrace_1010840
  have hstable : (prefixWord ++ tailWord_1010840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010840).length < 2 ^ (prefixWord ++ tailWord_1010840).sum := by decide
  have hdescent : baseEnd_1010840 < baseStart_1010840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010851 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 1, 7]
def baseStart_1010851 : Nat := 118140960795 + 1010851 * 2 ^ 59
def prefixEnd_1010851 : Nat := 4983230072969 + 3 ^ 40 * 1010851 * 2
def baseEnd_1010851 : Nat := 346034955385419849675791

theorem tailTrace_1010851 : CollatzResearch.WordTrace tailWord_1010851 prefixEnd_1010851 346034955385419849675791 := by
  unfold tailWord_1010851
  simp only [CollatzResearch.WordTrace]
  refine ⟨36868764860866941451368407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24579176573911294300912271 36868764860866941451368407)
  ·
    refine ⟨55303147291300412177052611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36868764860866941451368407 55303147291300412177052611)
    ·
      refine ⟨82954720936950618265578917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55303147291300412177052611 82954720936950618265578917)
      ·
        refine ⟨15554010175678240924796047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82954720936950618265578917 15554010175678240924796047)
        ·
          refine ⟨23331015263517361387194071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15554010175678240924796047 23331015263517361387194071)
          ·
            refine ⟨34996522895276042080791107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23331015263517361387194071 34996522895276042080791107)
            ·
              refine ⟨52494784342914063121186661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34996522895276042080791107 52494784342914063121186661)
              ·
                refine ⟨9842772064296386835222499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52494784342914063121186661 9842772064296386835222499)
                ·
                  refine ⟨14764158096444580252833749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9842772064296386835222499 14764158096444580252833749)
                  ·
                    refine ⟨346034955385419849675791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14764158096444580252833749 346034955385419849675791)
                    ·
                      rfl

theorem cell22_1010851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 7].length) (baseStart_1010851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010851 prefixEnd_1010851 := by exact prefixLift 1010851
  have htrace : WordTrace (prefixWord ++ tailWord_1010851) baseStart_1010851 baseEnd_1010851 := by
    simpa [prefixWord, tailWord_1010851, baseEnd_1010851] using wordTrace_append hprefix tailTrace_1010851
  have hstable : (prefixWord ++ tailWord_1010851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010851).length < 2 ^ (prefixWord ++ tailWord_1010851).sum := by decide
  have hdescent : baseEnd_1010851 < baseStart_1010851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010898 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 8]
def baseStart_1010898 : Nat := 118140960795 + 1010898 * 2 ^ 59
def prefixEnd_1010898 : Nat := 4983230072969 + 3 ^ 40 * 1010898 * 2
def baseEnd_1010898 : Nat := 115350348148642464583549

theorem tailTrace_1010898 : CollatzResearch.WordTrace tailWord_1010898 prefixEnd_1010898 115350348148642464583549 := by
  unfold tailWord_1010898
  simp only [CollatzResearch.WordTrace]
  refine ⟨9217619772924167119582337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24580319394464445652219565 9217619772924167119582337)
  ·
    refine ⟨6913214829693125339686753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9217619772924167119582337 6913214829693125339686753)
    ·
      refine ⟨5184911122269844004765065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6913214829693125339686753 5184911122269844004765065)
      ·
        refine ⟨3888683341702383003573799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5184911122269844004765065 3888683341702383003573799)
        ·
          refine ⟨5833025012553574505360699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3888683341702383003573799 5833025012553574505360699)
          ·
            refine ⟨8749537518830361758041049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5833025012553574505360699 8749537518830361758041049)
            ·
              refine ⟨6562153139122771318530787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8749537518830361758041049 6562153139122771318530787)
              ·
                refine ⟨9843229708684156977796181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6562153139122771318530787 9843229708684156977796181)
                ·
                  refine ⟨115350348148642464583549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9843229708684156977796181 115350348148642464583549)
                  ·
                    rfl

theorem cell22_1010898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_1010898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010898 prefixEnd_1010898 := by exact prefixLift 1010898
  have htrace : WordTrace (prefixWord ++ tailWord_1010898) baseStart_1010898 baseEnd_1010898 := by
    simpa [prefixWord, tailWord_1010898, baseEnd_1010898] using wordTrace_append hprefix tailTrace_1010898
  have hstable : (prefixWord ++ tailWord_1010898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010898).length < 2 ^ (prefixWord ++ tailWord_1010898).sum := by decide
  have hdescent : baseEnd_1010898 < baseStart_1010898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010913 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 3, 5]
def baseStart_1010913 : Nat := 118140960795 + 1010913 * 2 ^ 59
def prefixEnd_1010913 : Nat := 4983230072969 + 3 ^ 40 * 1010913 * 2
def baseEnd_1010913 : Nat := 346056179252472354625601

theorem tailTrace_1010913 : CollatzResearch.WordTrace tailWord_1010913 prefixEnd_1010913 346056179252472354625601 := by
  unfold tailWord_1010913
  simp only [CollatzResearch.WordTrace]
  refine ⟨36871026186642326040125393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24580684124428217360083595 36871026186642326040125393)
  ·
    refine ⟨27653269639981744530094045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36871026186642326040125393 27653269639981744530094045)
    ·
      refine ⟨10369976114993154198785267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27653269639981744530094045 10369976114993154198785267)
      ·
        refine ⟨15554964172489731298177901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10369976114993154198785267 15554964172489731298177901)
        ·
          refine ⟨5833111564683649236816713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15554964172489731298177901 5833111564683649236816713)
          ·
            refine ⟨4374833673512736927612535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5833111564683649236816713 4374833673512736927612535)
            ·
              refine ⟨6562250510269105391418803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4374833673512736927612535 6562250510269105391418803)
              ·
                refine ⟨9843375765403658087128205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6562250510269105391418803 9843375765403658087128205)
                ·
                  refine ⟨3691265912026371782673077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9843375765403658087128205 3691265912026371782673077)
                  ·
                    refine ⟨346056179252472354625601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3691265912026371782673077 346056179252472354625601)
                    ·
                      rfl

theorem cell22_1010913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_1010913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010913 prefixEnd_1010913 := by exact prefixLift 1010913
  have htrace : WordTrace (prefixWord ++ tailWord_1010913) baseStart_1010913 baseEnd_1010913 := by
    simpa [prefixWord, tailWord_1010913, baseEnd_1010913] using wordTrace_append hprefix tailTrace_1010913
  have hstable : (prefixWord ++ tailWord_1010913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010913).length < 2 ^ (prefixWord ++ tailWord_1010913).sum := by decide
  have hdescent : baseEnd_1010913 < baseStart_1010913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010943 : List Nat := [1, 1, 2, 2, 1, 5, 3, 7]
def baseStart_1010943 : Nat := 118140960795 + 1010943 * 2 ^ 59
def prefixEnd_1010943 : Nat := 4983230072969 + 3 ^ 40 * 1010943 * 2
def baseEnd_1010943 : Nat := 38451827651729141819501

theorem tailTrace_1010943 : CollatzResearch.WordTrace tailWord_1010943 prefixEnd_1010943 38451827651729141819501 := by
  unfold tailWord_1010943
  simp only [CollatzResearch.WordTrace]
  refine ⟨36872120376533641163717483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24581413584355760775811655 36872120376533641163717483)
  ·
    refine ⟨55308180564800461745576225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36872120376533641163717483 55308180564800461745576225)
    ·
      refine ⟨41481135423600346309182169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55308180564800461745576225 41481135423600346309182169)
      ·
        refine ⟨31110851567700259731886627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41481135423600346309182169 31110851567700259731886627)
        ·
          refine ⟨46666277351550389597829941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31110851567700259731886627 46666277351550389597829941)
          ·
            refine ⟨4374963501707849024796557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46666277351550389597829941 4374963501707849024796557)
            ·
              refine ⟨1640611313140443384298709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4374963501707849024796557 1640611313140443384298709)
              ·
                refine ⟨38451827651729141819501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1640611313140443384298709 38451827651729141819501)
                ·
                  rfl

theorem cell22_1010943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 7].length) (baseStart_1010943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010943 prefixEnd_1010943 := by exact prefixLift 1010943
  have htrace : WordTrace (prefixWord ++ tailWord_1010943) baseStart_1010943 baseEnd_1010943 := by
    simpa [prefixWord, tailWord_1010943, baseEnd_1010943] using wordTrace_append hprefix tailTrace_1010943
  have hstable : (prefixWord ++ tailWord_1010943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010943).length < 2 ^ (prefixWord ++ tailWord_1010943).sum := by decide
  have hdescent : baseEnd_1010943 < baseStart_1010943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010992 : List Nat := [2, 1, 1, 1, 2, 2, 3, 6, 1, 3]
def baseStart_1010992 : Nat := 118140960795 + 1010992 * 2 ^ 59
def prefixEnd_1010992 : Nat := 4983230072969 + 3 ^ 40 * 1010992 * 2
def baseEnd_1010992 : Nat := 346083222566942481900359

theorem tailTrace_1010992 : CollatzResearch.WordTrace tailWord_1010992 prefixEnd_1010992 346083222566942481900359 := by
  unfold tailWord_1010992
  simp only [CollatzResearch.WordTrace]
  refine ⟨18436953776678061266125615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24582605035570748354834153 18436953776678061266125615)
  ·
    refine ⟨27655430665017091899188423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18436953776678061266125615 27655430665017091899188423)
    ·
      refine ⟨41483145997525637848782635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27655430665017091899188423 41483145997525637848782635)
      ·
        refine ⟨62224718996288456773173953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41483145997525637848782635 62224718996288456773173953)
        ·
          refine ⟨46668539247216342579880465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62224718996288456773173953 46668539247216342579880465)
          ·
            refine ⟨35001404435412256934910349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46668539247216342579880465 35001404435412256934910349)
            ·
              refine ⟨13125526663279596350591381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35001404435412256934910349 13125526663279596350591381)
              ·
                refine ⟨615259062341231078933971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13125526663279596350591381 615259062341231078933971)
                ·
                  refine ⟨922888593511846618400957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615259062341231078933971 922888593511846618400957)
                  ·
                    refine ⟨346083222566942481900359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 922888593511846618400957 346083222566942481900359)
                    ·
                      rfl

theorem cell22_1010992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 1, 3].length) (baseStart_1010992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010992 prefixEnd_1010992 := by exact prefixLift 1010992
  have htrace : WordTrace (prefixWord ++ tailWord_1010992) baseStart_1010992 baseEnd_1010992 := by
    simpa [prefixWord, tailWord_1010992, baseEnd_1010992] using wordTrace_append hprefix tailTrace_1010992
  have hstable : (prefixWord ++ tailWord_1010992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010992).length < 2 ^ (prefixWord ++ tailWord_1010992).sum := by decide
  have hdescent : baseEnd_1010992 < baseStart_1010992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010998 : List Nat := [5, 1, 2, 3, 1, 1, 3, 1, 2, 3]
def baseStart_1010998 : Nat := 118140960795 + 1010998 * 2 ^ 59
def prefixEnd_1010998 : Nat := 4983230072969 + 3 ^ 40 * 1010998 * 2
def baseEnd_1010998 : Nat := 346085276489560466250341

theorem tailTrace_1010998 : CollatzResearch.WordTrace tailWord_1010998 prefixEnd_1010998 346085276489560466250341 := by
  unfold tailWord_1010998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2304632899458399097310603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24582750927556257037979765 2304632899458399097310603)
  ·
    refine ⟨3456949349187598645965905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2304632899458399097310603 3456949349187598645965905)
    ·
      refine ⟨2592712011890698984474429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3456949349187598645965905 2592712011890698984474429)
      ·
        refine ⟨972267004459012119177911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2592712011890698984474429 972267004459012119177911)
        ·
          refine ⟨1458400506688518178766867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972267004459012119177911 1458400506688518178766867)
          ·
            refine ⟨2187600760032777268150301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1458400506688518178766867 2187600760032777268150301)
            ·
              refine ⟨820350285012291475556363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2187600760032777268150301 820350285012291475556363)
              ·
                refine ⟨1230525427518437213334545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 820350285012291475556363 1230525427518437213334545)
                ·
                  refine ⟨922894070638827910000909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1230525427518437213334545 922894070638827910000909)
                  ·
                    refine ⟨346085276489560466250341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 922894070638827910000909 346085276489560466250341)
                    ·
                      rfl

theorem cell22_1010998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_1010998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1010998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1010998 prefixEnd_1010998 := by exact prefixLift 1010998
  have htrace : WordTrace (prefixWord ++ tailWord_1010998) baseStart_1010998 baseEnd_1010998 := by
    simpa [prefixWord, tailWord_1010998, baseEnd_1010998] using wordTrace_append hprefix tailTrace_1010998
  have hstable : (prefixWord ++ tailWord_1010998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010998).length < 2 ^ (prefixWord ++ tailWord_1010998).sum := by decide
  have hdescent : baseEnd_1010998 < baseStart_1010998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011018 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 2, 8]
def baseStart_1011018 : Nat := 118140960795 + 1011018 * 2 ^ 59
def prefixEnd_1011018 : Nat := 4983230072969 + 3 ^ 40 * 1011018 * 2
def baseEnd_1011018 : Nat := 346092122898287080750279

theorem tailTrace_1011018 : CollatzResearch.WordTrace tailWord_1011018 prefixEnd_1011018 346092122898287080750279 := by
  unfold tailWord_1011018
  simp only [CollatzResearch.WordTrace]
  refine ⟨9218713962815482243174427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24583237234174619315131805 9218713962815482243174427)
  ·
    refine ⟨13828070944223223364761641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9218713962815482243174427 13828070944223223364761641)
    ·
      refine ⟨10371053208167417523571231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13828070944223223364761641 10371053208167417523571231)
      ·
        refine ⟨15556579812251126285356847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10371053208167417523571231 15556579812251126285356847)
        ·
          refine ⟨23334869718376689428035271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15556579812251126285356847 23334869718376689428035271)
          ·
            refine ⟨35002304577565034142052907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23334869718376689428035271 35002304577565034142052907)
            ·
              refine ⟨52503456866347551213079361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35002304577565034142052907 52503456866347551213079361)
              ·
                refine ⟨39377592649760663409809521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52503456866347551213079361 39377592649760663409809521)
                ·
                  refine ⟨29533194487320497557357141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39377592649760663409809521 29533194487320497557357141)
                  ·
                    refine ⟨346092122898287080750279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29533194487320497557357141 346092122898287080750279)
                    ·
                      rfl

theorem cell22_1011018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_1011018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011018 prefixEnd_1011018 := by exact prefixLift 1011018
  have htrace : WordTrace (prefixWord ++ tailWord_1011018) baseStart_1011018 baseEnd_1011018 := by
    simpa [prefixWord, tailWord_1011018, baseEnd_1011018] using wordTrace_append hprefix tailTrace_1011018
  have hstable : (prefixWord ++ tailWord_1011018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011018).length < 2 ^ (prefixWord ++ tailWord_1011018).sum := by decide
  have hdescent : baseEnd_1011018 < baseStart_1011018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011033 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 8]
def baseStart_1011033 : Nat := 118140960795 + 1011033 * 2 ^ 59
def prefixEnd_1011033 : Nat := 4983230072969 + 3 ^ 40 * 1011033 * 2
def baseEnd_1011033 : Nat := 115365752568277347208411

theorem tailTrace_1011033 : CollatzResearch.WordTrace tailWord_1011033 prefixEnd_1011033 115365752568277347208411 := by
  unfold tailWord_1011033
  simp only [CollatzResearch.WordTrace]
  refine ⟨36875402946207586534493753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24583601964138391022995835 36875402946207586534493753)
  ·
    refine ⟨27656552209655689900870315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36875402946207586534493753 27656552209655689900870315)
    ·
      refine ⟨41484828314483534851305473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27656552209655689900870315 41484828314483534851305473)
      ·
        refine ⟨31113621235862651138479105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41484828314483534851305473 31113621235862651138479105)
        ·
          refine ⟨23335215926896988353859329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31113621235862651138479105 23335215926896988353859329)
          ·
            refine ⟨17501411945172741265394497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23335215926896988353859329 17501411945172741265394497)
            ·
              refine ⟨13126058958879555949045873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17501411945172741265394497 13126058958879555949045873)
              ·
                refine ⟨9844544219159666961784405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13126058958879555949045873 9844544219159666961784405)
                ·
                  refine ⟨115365752568277347208411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9844544219159666961784405 115365752568277347208411)
                  ·
                    rfl

theorem cell22_1011033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 8].length) (baseStart_1011033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011033 prefixEnd_1011033 := by exact prefixLift 1011033
  have htrace : WordTrace (prefixWord ++ tailWord_1011033) baseStart_1011033 baseEnd_1011033 := by
    simpa [prefixWord, tailWord_1011033, baseEnd_1011033] using wordTrace_append hprefix tailTrace_1011033
  have hstable : (prefixWord ++ tailWord_1011033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011033).length < 2 ^ (prefixWord ++ tailWord_1011033).sum := by decide
  have hdescent : baseEnd_1011033 < baseStart_1011033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011086 : List Nat := [4, 1, 1, 4, 2, 1, 3, 1, 1, 4]
def baseStart_1011086 : Nat := 118140960795 + 1011086 * 2 ^ 59
def prefixEnd_1011086 : Nat := 4983230072969 + 3 ^ 40 * 1011086 * 2
def baseEnd_1011086 : Nat := 346115400687957570050071

theorem tailTrace_1011086 : CollatzResearch.WordTrace tailWord_1011086 prefixEnd_1011086 346115400687957570050071 := by
  unfold tailWord_1011086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4609667001876947073271639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24584890676677051057448741 4609667001876947073271639)
  ·
    refine ⟨6914500502815420609907459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4609667001876947073271639 6914500502815420609907459)
    ·
      refine ⟨10371750754223130914861189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6914500502815420609907459 10371750754223130914861189)
      ·
        refine ⟨1944703266416837046536473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10371750754223130914861189 1944703266416837046536473)
        ·
          refine ⟨1458527449812627784902355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1944703266416837046536473 1458527449812627784902355)
          ·
            refine ⟨2187791174718941677353533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1458527449812627784902355 2187791174718941677353533)
            ·
              refine ⟨820421690519603129007575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2187791174718941677353533 820421690519603129007575)
              ·
                refine ⟨1230632535779404693511363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 820421690519603129007575 1230632535779404693511363)
                ·
                  refine ⟨1845948803669107040267045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1230632535779404693511363 1845948803669107040267045)
                  ·
                    refine ⟨346115400687957570050071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1845948803669107040267045 346115400687957570050071)
                    ·
                      rfl

theorem cell22_1011086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_1011086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011086 prefixEnd_1011086 := by exact prefixLift 1011086
  have htrace : WordTrace (prefixWord ++ tailWord_1011086) baseStart_1011086 baseEnd_1011086 := by
    simpa [prefixWord, tailWord_1011086, baseEnd_1011086] using wordTrace_append hprefix tailTrace_1011086
  have hstable : (prefixWord ++ tailWord_1011086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011086).length < 2 ^ (prefixWord ++ tailWord_1011086).sum := by decide
  have hdescent : baseEnd_1011086 < baseStart_1011086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011101 : List Nat := [1, 4, 2, 1, 3, 3, 2, 2, 4]
def baseStart_1011101 : Nat := 118140960795 + 1011101 * 2 ^ 59
def prefixEnd_1011101 : Nat := 4983230072969 + 3 ^ 40 * 1011101 * 2
def baseEnd_1011101 : Nat := 115373511831500843641675

theorem tailTrace_1011101 : CollatzResearch.WordTrace tailWord_1011101 prefixEnd_1011101 115373511831500843641675 := by
  unfold tailWord_1011101
  simp only [CollatzResearch.WordTrace]
  refine ⟨36877883109961234147969157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24585255406640822765312771 36877883109961234147969157)
  ·
    refine ⟨6914603083117731402744217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36877883109961234147969157 6914603083117731402744217)
    ·
      refine ⟨5185952312338298552058163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6914603083117731402744217 5185952312338298552058163)
      ·
        refine ⟨7778928468507447828087245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5185952312338298552058163 7778928468507447828087245)
        ·
          refine ⟨2917098175690292935532717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7778928468507447828087245 2917098175690292935532717)
          ·
            refine ⟨1093911815883859850824769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2917098175690292935532717 1093911815883859850824769)
            ·
              refine ⟨820433861912894888118577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1093911815883859850824769 820433861912894888118577)
              ·
                refine ⟨615325396434671166088933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 820433861912894888118577 615325396434671166088933)
                ·
                  refine ⟨115373511831500843641675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 615325396434671166088933 115373511831500843641675)
                  ·
                    rfl

theorem cell22_1011101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_1011101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011101 prefixEnd_1011101 := by exact prefixLift 1011101
  have htrace : WordTrace (prefixWord ++ tailWord_1011101) baseStart_1011101 baseEnd_1011101 := by
    simpa [prefixWord, tailWord_1011101, baseEnd_1011101] using wordTrace_append hprefix tailTrace_1011101
  have hstable : (prefixWord ++ tailWord_1011101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011101).length < 2 ^ (prefixWord ++ tailWord_1011101).sum := by decide
  have hdescent : baseEnd_1011101 < baseStart_1011101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011127 : List Nat := [1, 1, 3, 1, 3, 2, 3, 2, 3, 3]
def baseStart_1011127 : Nat := 118140960795 + 1011127 * 2 ^ 59
def prefixEnd_1011127 : Nat := 4983230072969 + 3 ^ 40 * 1011127 * 2
def baseEnd_1011127 : Nat := 346129435825847129774945

theorem tailTrace_1011127 : CollatzResearch.WordTrace tailWord_1011127 prefixEnd_1011127 346129435825847129774945 := by
  unfold tailWord_1011127
  simp only [CollatzResearch.WordTrace]
  refine ⟨36878831407867040588415635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24585887605244693725610423 36878831407867040588415635)
  ·
    refine ⟨55318247111800560882623453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36878831407867040588415635 55318247111800560882623453)
    ·
      refine ⟨20744342666925210330983795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55318247111800560882623453 20744342666925210330983795)
      ·
        refine ⟨31116514000387815496475693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20744342666925210330983795 31116514000387815496475693)
        ·
          refine ⟨11668692750145430811178385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31116514000387815496475693 11668692750145430811178385)
          ·
            refine ⟨8751519562609073108383789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11668692750145430811178385 8751519562609073108383789)
            ·
              refine ⟨3281819835978402415643921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8751519562609073108383789 3281819835978402415643921)
              ·
                refine ⟨2461364876983801811732941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3281819835978402415643921 2461364876983801811732941)
                ·
                  refine ⟨923011828868925679399853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2461364876983801811732941 923011828868925679399853)
                  ·
                    refine ⟨346129435825847129774945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 923011828868925679399853 346129435825847129774945)
                    ·
                      rfl

theorem cell22_1011127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_1011127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011127 prefixEnd_1011127 := by exact prefixLift 1011127
  have htrace : WordTrace (prefixWord ++ tailWord_1011127) baseStart_1011127 baseEnd_1011127 := by
    simpa [prefixWord, tailWord_1011127, baseEnd_1011127] using wordTrace_append hprefix tailTrace_1011127
  have hstable : (prefixWord ++ tailWord_1011127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011127).length < 2 ^ (prefixWord ++ tailWord_1011127).sum := by decide
  have hdescent : baseEnd_1011127 < baseStart_1011127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011217 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 4, 3]
def baseStart_1011217 : Nat := 118140960795 + 1011217 * 2 ^ 59
def prefixEnd_1011217 : Nat := 4983230072969 + 3 ^ 40 * 1011217 * 2
def baseEnd_1011217 : Nat := 346160244665116895024669

theorem tailTrace_1011217 : CollatzResearch.WordTrace tailWord_1011217 prefixEnd_1011217 346160244665116895024669 := by
  unfold tailWord_1011217
  simp only [CollatzResearch.WordTrace]
  refine ⟨36882113977540985959191905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24588075985027323972794603 36882113977540985959191905)
  ·
    refine ⟨27661585483155739469393929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36882113977540985959191905 27661585483155739469393929)
    ·
      refine ⟨20746189112366804602045447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27661585483155739469393929 20746189112366804602045447)
      ·
        refine ⟨31119283668550206903068171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20746189112366804602045447 31119283668550206903068171)
        ·
          refine ⟨46678925502825310354602257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31119283668550206903068171 46678925502825310354602257)
          ·
            refine ⟨35009194127118982765951693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46678925502825310354602257 35009194127118982765951693)
            ·
              refine ⟨13128447797669618537231885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35009194127118982765951693 13128447797669618537231885)
              ·
                refine ⟨4923167924126106951461957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13128447797669618537231885 4923167924126106951461957)
                ·
                  refine ⟨923093985773645053399117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4923167924126106951461957 923093985773645053399117)
                  ·
                    refine ⟨346160244665116895024669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 923093985773645053399117 346160244665116895024669)
                    ·
                      rfl

theorem cell22_1011217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_1011217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011217 prefixEnd_1011217 := by exact prefixLift 1011217
  have htrace : WordTrace (prefixWord ++ tailWord_1011217) baseStart_1011217 baseEnd_1011217 := by
    simpa [prefixWord, tailWord_1011217, baseEnd_1011217] using wordTrace_append hprefix tailTrace_1011217
  have hstable : (prefixWord ++ tailWord_1011217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011217).length < 2 ^ (prefixWord ++ tailWord_1011217).sum := by decide
  have hdescent : baseEnd_1011217 < baseStart_1011217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011322 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 5, 4]
def baseStart_1011322 : Nat := 118140960795 + 1011322 * 2 ^ 59
def prefixEnd_1011322 : Nat := 4983230072969 + 3 ^ 40 * 1011322 * 2
def baseEnd_1011322 : Nat := 346196188310931621149347

theorem tailTrace_1011322 : CollatzResearch.WordTrace tailWord_1011322 prefixEnd_1011322 346196188310931621149347 := by
  unfold tailWord_1011322
  simp only [CollatzResearch.WordTrace]
  refine ⟨9221485910540147222941055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24590629094773725927842813 9221485910540147222941055)
  ·
    refine ⟨13832228865810220834411583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9221485910540147222941055 13832228865810220834411583)
    ·
      refine ⟨20748343298715331251617375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13832228865810220834411583 20748343298715331251617375)
      ·
        refine ⟨31122514948072996877426063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20748343298715331251617375 31122514948072996877426063)
        ·
          refine ⟨46683772422109495316139095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31122514948072996877426063 46683772422109495316139095)
          ·
            refine ⟨70025658633164242974208643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46683772422109495316139095 70025658633164242974208643)
            ·
              refine ⟨105038487949746364461312965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70025658633164242974208643 105038487949746364461312965)
              ·
                refine ⟨19694716490577443336496181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105038487949746364461312965 19694716490577443336496181)
                ·
                  refine ⟨1846379670991635312796517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19694716490577443336496181 1846379670991635312796517)
                  ·
                    refine ⟨346196188310931621149347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1846379670991635312796517 346196188310931621149347)
                    ·
                      rfl

theorem cell22_1011322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_1011322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011322 prefixEnd_1011322 := by exact prefixLift 1011322
  have htrace : WordTrace (prefixWord ++ tailWord_1011322) baseStart_1011322 baseEnd_1011322 := by
    simpa [prefixWord, tailWord_1011322, baseEnd_1011322] using wordTrace_append hprefix tailTrace_1011322
  have hstable : (prefixWord ++ tailWord_1011322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011322).length < 2 ^ (prefixWord ++ tailWord_1011322).sum := by decide
  have hdescent : baseEnd_1011322 < baseStart_1011322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011337 : List Nat := [1, 2, 1, 1, 4, 1, 3, 3, 6]
def baseStart_1011337 : Nat := 118140960795 + 1011337 * 2 ^ 59
def prefixEnd_1011337 : Nat := 4983230072969 + 3 ^ 40 * 1011337 * 2
def baseEnd_1011337 : Nat := 115400441039158860674767

theorem tailTrace_1011337 : CollatzResearch.WordTrace tailWord_1011337 prefixEnd_1011337 115400441039158860674767 := by
  unfold tailWord_1011337
  simp only [CollatzResearch.WordTrace]
  refine ⟨36886490737106246453560265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24590993824737497635706843 36886490737106246453560265)
  ·
    refine ⟨27664868052829684840170199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36886490737106246453560265 27664868052829684840170199)
    ·
      refine ⟨41497302079244527260255299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27664868052829684840170199 41497302079244527260255299)
      ·
        refine ⟨62245953118866790890382949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41497302079244527260255299 62245953118866790890382949)
        ·
          refine ⟨11671116209787523291946803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62245953118866790890382949 11671116209787523291946803)
          ·
            refine ⟨17506674314681284937920205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11671116209787523291946803 17506674314681284937920205)
            ·
              refine ⟨6565002868005481851720077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17506674314681284937920205 6565002868005481851720077)
              ·
                refine ⟨2461876075502055694395029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6565002868005481851720077 2461876075502055694395029)
                ·
                  refine ⟨115400441039158860674767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2461876075502055694395029 115400441039158860674767)
                  ·
                    rfl

theorem cell22_1011337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 6].length) (baseStart_1011337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011337 prefixEnd_1011337 := by exact prefixLift 1011337
  have htrace : WordTrace (prefixWord ++ tailWord_1011337) baseStart_1011337 baseEnd_1011337 := by
    simpa [prefixWord, tailWord_1011337, baseEnd_1011337] using wordTrace_append hprefix tailTrace_1011337
  have hstable : (prefixWord ++ tailWord_1011337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011337).length < 2 ^ (prefixWord ++ tailWord_1011337).sum := by decide
  have hdescent : baseEnd_1011337 < baseStart_1011337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011388 : List Nat := [2, 2, 2, 3, 1, 3, 3, 2, 4]
def baseStart_1011388 : Nat := 118140960795 + 1011388 * 2 ^ 59
def prefixEnd_1011388 : Nat := 4983230072969 + 3 ^ 40 * 1011388 * 2
def baseEnd_1011388 : Nat := 115406260486576482999715

theorem tailTrace_1011388 : CollatzResearch.WordTrace tailWord_1011388 prefixEnd_1011388 115406260486576482999715 := by
  unfold tailWord_1011388
  simp only [CollatzResearch.WordTrace]
  refine ⟨18444175429960741081833409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24592233906614321442444545 18444175429960741081833409)
  ·
    refine ⟨13833131572470555811375057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18444175429960741081833409 13833131572470555811375057)
    ·
      refine ⟨10374848679352916858531293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13833131572470555811375057 10374848679352916858531293)
      ·
        refine ⟨3890568254757343821949235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10374848679352916858531293 3890568254757343821949235)
        ·
          refine ⟨5835852382136015732923853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3890568254757343821949235 5835852382136015732923853)
          ·
            refine ⟨2188444643301005899846445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5835852382136015732923853 2188444643301005899846445)
            ·
              refine ⟨820666741237877212442417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2188444643301005899846445 820666741237877212442417)
              ·
                refine ⟨615500055928407909331813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 820666741237877212442417 615500055928407909331813)
                ·
                  refine ⟨115406260486576482999715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 615500055928407909331813 115406260486576482999715)
                  ·
                    rfl

theorem cell22_1011388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 4].length) (baseStart_1011388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011388 prefixEnd_1011388 := by exact prefixLift 1011388
  have htrace : WordTrace (prefixWord ++ tailWord_1011388) baseStart_1011388 baseEnd_1011388 := by
    simpa [prefixWord, tailWord_1011388, baseEnd_1011388] using wordTrace_append hprefix tailTrace_1011388
  have hstable : (prefixWord ++ tailWord_1011388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011388).length < 2 ^ (prefixWord ++ tailWord_1011388).sum := by decide
  have hdescent : baseEnd_1011388 < baseStart_1011388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011394 : List Nat := [3, 5, 1, 2, 2, 1, 2, 1, 5]
def baseStart_1011394 : Nat := 118140960795 + 1011394 * 2 ^ 59
def prefixEnd_1011394 : Nat := 4983230072969 + 3 ^ 40 * 1011394 * 2
def baseEnd_1011394 : Nat := 115406945127449144449709

theorem tailTrace_1011394 : CollatzResearch.WordTrace tailWord_1011394 prefixEnd_1011394 115406945127449144449709 := by
  unfold tailWord_1011394
  simp only [CollatzResearch.WordTrace]
  refine ⟨9222142424474936297096309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24592379798599830125590157 9222142424474936297096309)
  ·
    refine ⟨864575852294525277852779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9222142424474936297096309 864575852294525277852779)
    ·
      refine ⟨1296863778441787916779169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 864575852294525277852779 1296863778441787916779169)
      ·
        refine ⟨972647833831340937584377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1296863778441787916779169 972647833831340937584377)
        ·
          refine ⟨729485875373505703188283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 972647833831340937584377 729485875373505703188283)
          ·
            refine ⟨1094228813060258554782425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729485875373505703188283 1094228813060258554782425)
            ·
              refine ⟨820671609795193916086819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1094228813060258554782425 820671609795193916086819)
              ·
                refine ⟨1231007414692790874130229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 820671609795193916086819 1231007414692790874130229)
                ·
                  refine ⟨115406945127449144449709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1231007414692790874130229 115406945127449144449709)
                  ·
                    rfl

theorem cell22_1011394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_1011394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011394 prefixEnd_1011394 := by exact prefixLift 1011394
  have htrace : WordTrace (prefixWord ++ tailWord_1011394) baseStart_1011394 baseEnd_1011394 := by
    simpa [prefixWord, tailWord_1011394, baseEnd_1011394] using wordTrace_append hprefix tailTrace_1011394
  have hstable : (prefixWord ++ tailWord_1011394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011394).length < 2 ^ (prefixWord ++ tailWord_1011394).sum := by decide
  have hdescent : baseEnd_1011394 < baseStart_1011394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011469 : List Nat := [1, 7, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_1011469 : Nat := 118140960795 + 1011469 * 2 ^ 59
def prefixEnd_1011469 : Nat := 4983230072969 + 3 ^ 40 * 1011469 * 2
def baseEnd_1011469 : Nat := 346246509415072237723897

theorem tailTrace_1011469 : CollatzResearch.WordTrace tailWord_1011469 prefixEnd_1011469 346246509415072237723897 := by
  unfold tailWord_1011469
  simp only [CollatzResearch.WordTrace]
  refine ⟨36891305172628032997365461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24594203448418688664910307 36891305172628032997365461)
  ·
    refine ⟨864639964983469523375753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 36891305172628032997365461 864639964983469523375753)
    ·
      refine ⟨648479973737602142531815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 864639964983469523375753 648479973737602142531815)
      ·
        refine ⟨972719960606403213797723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648479973737602142531815 972719960606403213797723)
        ·
          refine ⟨1459079940909604820696585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972719960606403213797723 1459079940909604820696585)
          ·
            refine ⟨1094309955682203615522439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1459079940909604820696585 1094309955682203615522439)
            ·
              refine ⟨1641464933523305423283659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094309955682203615522439 1641464933523305423283659)
              ·
                refine ⟨2462197400284958134925489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1641464933523305423283659 2462197400284958134925489)
                ·
                  refine ⟨1846648050213718601194117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2462197400284958134925489 1846648050213718601194117)
                  ·
                    refine ⟨346246509415072237723897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1846648050213718601194117 346246509415072237723897)
                    ·
                      rfl

theorem cell22_1011469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_1011469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011469 prefixEnd_1011469 := by exact prefixLift 1011469
  have htrace : WordTrace (prefixWord ++ tailWord_1011469) baseStart_1011469 baseEnd_1011469 := by
    simpa [prefixWord, tailWord_1011469, baseEnd_1011469] using wordTrace_append hprefix tailTrace_1011469
  have hstable : (prefixWord ++ tailWord_1011469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011469).length < 2 ^ (prefixWord ++ tailWord_1011469).sum := by decide
  have hdescent : baseEnd_1011469 < baseStart_1011469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011506 : List Nat := [3, 2, 1, 1, 3, 3, 2, 1, 6]
def baseStart_1011506 : Nat := 118140960795 + 1011506 * 2 ^ 59
def prefixEnd_1011506 : Nat := 4983230072969 + 3 ^ 40 * 1011506 * 2
def baseEnd_1011506 : Nat := 115419725090405491516261

theorem tailTrace_1011506 : CollatzResearch.WordTrace tailWord_1011506 prefixEnd_1011506 115419725090405491516261 := by
  unfold tailWord_1011506
  simp only [CollatzResearch.WordTrace]
  refine ⟨9223163668373497079115593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24595103115662658877641581 9223163668373497079115593)
  ·
    refine ⟨6917372751280122809336695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9223163668373497079115593 6917372751280122809336695)
    ·
      refine ⟨10376059126920184214005043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6917372751280122809336695 10376059126920184214005043)
      ·
        refine ⟨15564088690380276321007565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10376059126920184214005043 15564088690380276321007565)
        ·
          refine ⟨5836533258892603620377837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15564088690380276321007565 5836533258892603620377837)
          ·
            refine ⟨2188699972084726357641689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5836533258892603620377837 2188699972084726357641689)
            ·
              refine ⟨1641524979063544768231267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2188699972084726357641689 1641524979063544768231267)
              ·
                refine ⟨2462287468595317152346901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1641524979063544768231267 2462287468595317152346901)
                ·
                  refine ⟨115419725090405491516261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2462287468595317152346901 115419725090405491516261)
                  ·
                    rfl

theorem cell22_1011506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_1011506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011506 prefixEnd_1011506 := by exact prefixLift 1011506
  have htrace : WordTrace (prefixWord ++ tailWord_1011506) baseStart_1011506 baseEnd_1011506 := by
    simpa [prefixWord, tailWord_1011506, baseEnd_1011506] using wordTrace_append hprefix tailTrace_1011506
  have hstable : (prefixWord ++ tailWord_1011506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011506).length < 2 ^ (prefixWord ++ tailWord_1011506).sum := by decide
  have hdescent : baseEnd_1011506 < baseStart_1011506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011540 : List Nat := [2, 4, 1, 1, 3, 3, 1, 3, 4]
def baseStart_1011540 : Nat := 118140960795 + 1011540 * 2 ^ 59
def prefixEnd_1011540 : Nat := 4983230072969 + 3 ^ 40 * 1011540 * 2
def baseEnd_1011540 : Nat := 115423604722017239732893

theorem tailTrace_1011540 : CollatzResearch.WordTrace tailWord_1011540 prefixEnd_1011540 115423604722017239732893 := by
  unfold tailWord_1011540
  simp only [CollatzResearch.WordTrace]
  refine ⟨18446947377685406061600037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24595929836913874748800049 18446947377685406061600037)
  ·
    refine ⟨3458802633316013636550007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18446947377685406061600037 3458802633316013636550007)
    ·
      refine ⟨5188203949974020454825011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3458802633316013636550007 5188203949974020454825011)
      ·
        refine ⟨7782305924961030682237517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5188203949974020454825011 7782305924961030682237517)
        ·
          refine ⟨2918364721860386505839069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7782305924961030682237517 2918364721860386505839069)
          ·
            refine ⟨1094386770697644939689651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2918364721860386505839069 1094386770697644939689651)
            ·
              refine ⟨1641580156046467409534477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094386770697644939689651 1641580156046467409534477)
              ·
                refine ⟨615592558517425278575429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1641580156046467409534477 615592558517425278575429)
                ·
                  refine ⟨115423604722017239732893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 615592558517425278575429 115423604722017239732893)
                  ·
                    rfl

theorem cell22_1011540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_1011540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011540 prefixEnd_1011540 := by exact prefixLift 1011540
  have htrace : WordTrace (prefixWord ++ tailWord_1011540) baseStart_1011540 baseEnd_1011540 := by
    simpa [prefixWord, tailWord_1011540, baseEnd_1011540] using wordTrace_append hprefix tailTrace_1011540
  have hstable : (prefixWord ++ tailWord_1011540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011540).length < 2 ^ (prefixWord ++ tailWord_1011540).sum := by decide
  have hdescent : baseEnd_1011540 < baseStart_1011540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011613 : List Nat := [1, 4, 2, 1, 2, 3, 2, 2, 5]
def baseStart_1011613 : Nat := 118140960795 + 1011613 * 2 ^ 59
def prefixEnd_1011613 : Nat := 4983230072969 + 3 ^ 40 * 1011613 * 2
def baseEnd_1011613 : Nat := 115431934519301287374485

theorem tailTrace_1011613 : CollatzResearch.WordTrace tailWord_1011613 prefixEnd_1011613 115431934519301287374485 := by
  unfold tailWord_1011613
  simp only [CollatzResearch.WordTrace]
  refine ⟨36896557284106345590607493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24597704856070897060404995 36896557284106345590607493)
  ·
    refine ⟨6918104490769939798238905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36896557284106345590607493 6918104490769939798238905)
    ·
      refine ⟨5188578368077454848679179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6918104490769939798238905 5188578368077454848679179)
      ·
        refine ⟨7782867552116182273018769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5188578368077454848679179 7782867552116182273018769)
        ·
          refine ⟨5837150664087136704764077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7782867552116182273018769 5837150664087136704764077)
          ·
            refine ⟨2188931499032676264286529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5837150664087136704764077 2188931499032676264286529)
            ·
              refine ⟨1641698624274507198214897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2188931499032676264286529 1641698624274507198214897)
              ·
                refine ⟨1231273968205880398661173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1641698624274507198214897 1231273968205880398661173)
                ·
                  refine ⟨115431934519301287374485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1231273968205880398661173 115431934519301287374485)
                  ·
                    rfl

theorem cell22_1011613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_1011613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011613 prefixEnd_1011613 := by exact prefixLift 1011613
  have htrace : WordTrace (prefixWord ++ tailWord_1011613) baseStart_1011613 baseEnd_1011613 := by
    simpa [prefixWord, tailWord_1011613, baseEnd_1011613] using wordTrace_append hprefix tailTrace_1011613
  have hstable : (prefixWord ++ tailWord_1011613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011613).length < 2 ^ (prefixWord ++ tailWord_1011613).sum := by decide
  have hdescent : baseEnd_1011613 < baseStart_1011613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011617 : List Nat := [1, 2, 3, 4, 2, 1, 1, 4, 1, 3]
def baseStart_1011617 : Nat := 118140960795 + 1011617 * 2 ^ 59
def prefixEnd_1011617 : Nat := 4983230072969 + 3 ^ 40 * 1011617 * 2
def baseEnd_1011617 : Nat := 346297172839649185023443

theorem tailTrace_1011617 : CollatzResearch.WordTrace tailWord_1011617 prefixEnd_1011617 346297172839649185023443 := by
  unfold tailWord_1011617
  simp only [CollatzResearch.WordTrace]
  refine ⟨36896703176091854273753105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24597802117394569515835403 36896703176091854273753105)
  ·
    refine ⟨27672527382068890705314829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36896703176091854273753105 27672527382068890705314829)
    ·
      refine ⟨10377197768275834014493061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27672527382068890705314829 10377197768275834014493061)
      ·
        refine ⟨1945724581551718877717449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10377197768275834014493061 1945724581551718877717449)
        ·
          refine ⟨1459293436163789158288087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1945724581551718877717449 1459293436163789158288087)
          ·
            refine ⟨2188940154245683737432131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459293436163789158288087 2188940154245683737432131)
            ·
              refine ⟨3283410231368525606148197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2188940154245683737432131 3283410231368525606148197)
              ·
                refine ⟨615639418381598551152787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3283410231368525606148197 615639418381598551152787)
                ·
                  refine ⟨923459127572397826729181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615639418381598551152787 923459127572397826729181)
                  ·
                    refine ⟨346297172839649185023443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 923459127572397826729181 346297172839649185023443)
                    ·
                      rfl

theorem cell22_1011617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_1011617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011617 prefixEnd_1011617 := by exact prefixLift 1011617
  have htrace : WordTrace (prefixWord ++ tailWord_1011617) baseStart_1011617 baseEnd_1011617 := by
    simpa [prefixWord, tailWord_1011617, baseEnd_1011617] using wordTrace_append hprefix tailTrace_1011617
  have hstable : (prefixWord ++ tailWord_1011617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011617).length < 2 ^ (prefixWord ++ tailWord_1011617).sum := by decide
  have hdescent : baseEnd_1011617 < baseStart_1011617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011641 : List Nat := [1, 2, 1, 4, 2, 1, 3, 2, 6]
def baseStart_1011641 : Nat := 118140960795 + 1011641 * 2 ^ 59
def prefixEnd_1011641 : Nat := 4983230072969 + 3 ^ 40 * 1011641 * 2
def baseEnd_1011641 : Nat := 115435129510040374141123

theorem tailTrace_1011641 : CollatzResearch.WordTrace tailWord_1011641 prefixEnd_1011641 115435129510040374141123 := by
  unfold tailWord_1011641
  simp only [CollatzResearch.WordTrace]
  refine ⟨36897578528004906372626777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24598385685336604248417851 36897578528004906372626777)
  ·
    refine ⟨27673183896003679779470083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36897578528004906372626777 27673183896003679779470083)
    ·
      refine ⟨41509775844005519669205125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27673183896003679779470083 41509775844005519669205125)
      ·
        refine ⟨7783082970751034937975961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41509775844005519669205125 7783082970751034937975961)
        ·
          refine ⟨5837312228063276203481971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7783082970751034937975961 5837312228063276203481971)
          ·
            refine ⟨8755968342094914305222957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5837312228063276203481971 8755968342094914305222957)
            ·
              refine ⟨3283488128285592864458609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8755968342094914305222957 3283488128285592864458609)
              ·
                refine ⟨2462616096214194648343957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3283488128285592864458609 2462616096214194648343957)
                ·
                  refine ⟨115435129510040374141123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2462616096214194648343957 115435129510040374141123)
                  ·
                    rfl

theorem cell22_1011641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 6].length) (baseStart_1011641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011641 prefixEnd_1011641 := by exact prefixLift 1011641
  have htrace : WordTrace (prefixWord ++ tailWord_1011641) baseStart_1011641 baseEnd_1011641 := by
    simpa [prefixWord, tailWord_1011641, baseEnd_1011641] using wordTrace_append hprefix tailTrace_1011641
  have hstable : (prefixWord ++ tailWord_1011641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011641).length < 2 ^ (prefixWord ++ tailWord_1011641).sum := by decide
  have hdescent : baseEnd_1011641 < baseStart_1011641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011658 : List Nat := [3, 1, 2, 1, 2, 1, 3, 5, 4]
def baseStart_1011658 : Nat := 118140960795 + 1011658 * 2 ^ 59
def prefixEnd_1011658 : Nat := 4983230072969 + 3 ^ 40 * 1011658 * 2
def baseEnd_1011658 : Nat := 115437069325846248249439

theorem tailTrace_1011658 : CollatzResearch.WordTrace tailWord_1011658 prefixEnd_1011658 115437069325846248249439 := by
  unfold tailWord_1011658
  simp only [CollatzResearch.WordTrace]
  refine ⟨9224549642235829568998907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24598799045962212183997085 9224549642235829568998907)
  ·
    refine ⟨13836824463353744353498361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9224549642235829568998907 13836824463353744353498361)
    ·
      refine ⟨10377618347515308265123771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13836824463353744353498361 10377618347515308265123771)
      ·
        refine ⟨15566427521272962397685657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10377618347515308265123771 15566427521272962397685657)
        ·
          refine ⟨11674820640954721798264243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15566427521272962397685657 11674820640954721798264243)
          ·
            refine ⟨17512230961432082697396365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11674820640954721798264243 17512230961432082697396365)
            ·
              refine ⟨6567086610537031011523637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17512230961432082697396365 6567086610537031011523637)
              ·
                refine ⟨615664369737846657330341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6567086610537031011523637 615664369737846657330341)
                ·
                  refine ⟨115437069325846248249439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 615664369737846657330341 115437069325846248249439)
                  ·
                    rfl

theorem cell22_1011658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 4].length) (baseStart_1011658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011658 prefixEnd_1011658 := by exact prefixLift 1011658
  have htrace : WordTrace (prefixWord ++ tailWord_1011658) baseStart_1011658 baseEnd_1011658 := by
    simpa [prefixWord, tailWord_1011658, baseEnd_1011658] using wordTrace_append hprefix tailTrace_1011658
  have hstable : (prefixWord ++ tailWord_1011658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011658).length < 2 ^ (prefixWord ++ tailWord_1011658).sum := by decide
  have hdescent : baseEnd_1011658 < baseStart_1011658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011660 : List Nat := [2, 2, 1, 4, 1, 2, 4, 1, 1, 4]
def baseStart_1011660 : Nat := 118140960795 + 1011660 * 2 ^ 59
def prefixEnd_1011660 : Nat := 4983230072969 + 3 ^ 40 * 1011660 * 2
def baseEnd_1011660 : Nat := 346311892618411406198311

theorem tailTrace_1011660 : CollatzResearch.WordTrace tailWord_1011660 prefixEnd_1011660 346311892618411406198311 := by
  unfold tailWord_1011660
  simp only [CollatzResearch.WordTrace]
  refine ⟨18449135757468036308784217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24598847676624048411712289 18449135757468036308784217)
  ·
    refine ⟨13836851818101027231588163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18449135757468036308784217 13836851818101027231588163)
    ·
      refine ⟨20755277727151540847382245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13836851818101027231588163 20755277727151540847382245)
      ·
        refine ⟨3891614573840913908884171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20755277727151540847382245 3891614573840913908884171)
        ·
          refine ⟨5837421860761370863326257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3891614573840913908884171 5837421860761370863326257)
          ·
            refine ⟨4378066395571028147494693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5837421860761370863326257 4378066395571028147494693)
            ·
              refine ⟨820887449169567777655255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4378066395571028147494693 820887449169567777655255)
              ·
                refine ⟨1231331173754351666482883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 820887449169567777655255 1231331173754351666482883)
                ·
                  refine ⟨1846996760631527499724325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231331173754351666482883 1846996760631527499724325)
                  ·
                    refine ⟨346311892618411406198311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1846996760631527499724325 346311892618411406198311)
                    ·
                      rfl

theorem cell22_1011660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 1, 4].length) (baseStart_1011660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011660 prefixEnd_1011660 := by exact prefixLift 1011660
  have htrace : WordTrace (prefixWord ++ tailWord_1011660) baseStart_1011660 baseEnd_1011660 := by
    simpa [prefixWord, tailWord_1011660, baseEnd_1011660] using wordTrace_append hprefix tailTrace_1011660
  have hstable : (prefixWord ++ tailWord_1011660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011660).length < 2 ^ (prefixWord ++ tailWord_1011660).sum := by decide
  have hdescent : baseEnd_1011660 < baseStart_1011660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011671 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 4, 4]
def baseStart_1011671 : Nat := 118140960795 + 1011671 * 2 ^ 59
def prefixEnd_1011671 : Nat := 4983230072969 + 3 ^ 40 * 1011671 * 2
def baseEnd_1011671 : Nat := 346315658143211044173277

theorem tailTrace_1011671 : CollatzResearch.WordTrace tailWord_1011671 prefixEnd_1011671 346315658143211044173277 := by
  unfold tailWord_1011671
  simp only [CollatzResearch.WordTrace]
  refine ⟨36898672717896221496218867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24599115145264147664145911 36898672717896221496218867)
  ·
    refine ⟨55348009076844332244328301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36898672717896221496218867 55348009076844332244328301)
    ·
      refine ⟨20755503403816624591623113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55348009076844332244328301 20755503403816624591623113)
      ·
        refine ⟨15566627552862468443717335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20755503403816624591623113 15566627552862468443717335)
        ·
          refine ⟨23349941329293702665576003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15566627552862468443717335 23349941329293702665576003)
          ·
            refine ⟨35024911993940553998364005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23349941329293702665576003 35024911993940553998364005)
            ·
              refine ⟨6567170998863853874693251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35024911993940553998364005 6567170998863853874693251)
              ·
                refine ⟨9850756498295780812039877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6567170998863853874693251 9850756498295780812039877)
                ·
                  refine ⟨1847016843430458902257477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9850756498295780812039877 1847016843430458902257477)
                  ·
                    refine ⟨346315658143211044173277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1847016843430458902257477 346315658143211044173277)
                    ·
                      rfl

theorem cell22_1011671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_1011671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011671 prefixEnd_1011671 := by exact prefixLift 1011671
  have htrace : WordTrace (prefixWord ++ tailWord_1011671) baseStart_1011671 baseEnd_1011671 := by
    simpa [prefixWord, tailWord_1011671, baseEnd_1011671] using wordTrace_append hprefix tailTrace_1011671
  have hstable : (prefixWord ++ tailWord_1011671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011671).length < 2 ^ (prefixWord ++ tailWord_1011671).sum := by decide
  have hdescent : baseEnd_1011671 < baseStart_1011671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011731 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 7]
def baseStart_1011731 : Nat := 118140960795 + 1011731 * 2 ^ 59
def prefixEnd_1011731 : Nat := 4983230072969 + 3 ^ 40 * 1011731 * 2
def baseEnd_1011731 : Nat := 115445399123130295891031

theorem tailTrace_1011731 : CollatzResearch.WordTrace tailWord_1011731 prefixEnd_1011731 115445399123130295891031 := by
  unfold tailWord_1011731
  simp only [CollatzResearch.WordTrace]
  refine ⟨36900861097678851743403047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24600574065119234495602031 36900861097678851743403047)
  ·
    refine ⟨55351291646518277615104571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36900861097678851743403047 55351291646518277615104571)
    ·
      refine ⟨83026937469777416422656857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55351291646518277615104571 83026937469777416422656857)
      ·
        refine ⟨62270203102333062316992643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83026937469777416422656857 62270203102333062316992643)
        ·
          refine ⟨93405304653499593475488965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62270203102333062316992643 93405304653499593475488965)
          ·
            refine ⟨17513494622531173776654181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93405304653499593475488965 17513494622531173776654181)
            ·
              refine ⟨3283780241724595083122659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17513494622531173776654181 3283780241724595083122659)
              ·
                refine ⟨4925670362586892624683989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3283780241724595083122659 4925670362586892624683989)
                ·
                  refine ⟨115445399123130295891031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4925670362586892624683989 115445399123130295891031)
                  ·
                    rfl

theorem cell22_1011731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 7].length) (baseStart_1011731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011731 prefixEnd_1011731 := by exact prefixLift 1011731
  have htrace : WordTrace (prefixWord ++ tailWord_1011731) baseStart_1011731 baseEnd_1011731 := by
    simpa [prefixWord, tailWord_1011731, baseEnd_1011731] using wordTrace_append hprefix tailTrace_1011731
  have hstable : (prefixWord ++ tailWord_1011731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011731).length < 2 ^ (prefixWord ++ tailWord_1011731).sum := by decide
  have hdescent : baseEnd_1011731 < baseStart_1011731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011782 : List Nat := [6, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_1011782 : Nat := 118140960795 + 1011782 * 2 ^ 59
def prefixEnd_1011782 : Nat := 4983230072969 + 3 ^ 40 * 1011782 * 2
def baseEnd_1011782 : Nat := 115451218570547918215979

theorem tailTrace_1011782 : CollatzResearch.WordTrace tailWord_1011782 prefixEnd_1011782 115451218570547918215979 := by
  unfold tailWord_1011782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1153210038140440232922175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24601814146996058302339733 1153210038140440232922175)
  ·
    refine ⟨1729815057210660349383263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1153210038140440232922175 1729815057210660349383263)
    ·
      refine ⟨2594722585815990524074895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1729815057210660349383263 2594722585815990524074895)
      ·
        refine ⟨3892083878723985786112343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2594722585815990524074895 3892083878723985786112343)
        ·
          refine ⟨5838125818085978679168515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3892083878723985786112343 5838125818085978679168515)
          ·
            refine ⟨8757188727128968018752773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5838125818085978679168515 8757188727128968018752773)
            ·
              refine ⟨1641972886336681503516145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8757188727128968018752773 1641972886336681503516145)
              ·
                refine ⟨1231479664752511127637109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1641972886336681503516145 1231479664752511127637109)
                ·
                  refine ⟨115451218570547918215979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1231479664752511127637109 115451218570547918215979)
                  ·
                    rfl

theorem cell22_1011782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_1011782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011782 prefixEnd_1011782 := by exact prefixLift 1011782
  have htrace : WordTrace (prefixWord ++ tailWord_1011782) baseStart_1011782 baseEnd_1011782 := by
    simpa [prefixWord, tailWord_1011782, baseEnd_1011782] using wordTrace_append hprefix tailTrace_1011782
  have hstable : (prefixWord ++ tailWord_1011782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011782).length < 2 ^ (prefixWord ++ tailWord_1011782).sum := by decide
  have hdescent : baseEnd_1011782 < baseStart_1011782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011808 : List Nat := [2, 1, 1, 3, 2, 3, 1, 3, 1, 5]
def baseStart_1011808 : Nat := 118140960795 + 1011808 * 2 ^ 59
def prefixEnd_1011808 : Nat := 4983230072969 + 3 ^ 40 * 1011808 * 2
def baseEnd_1011808 : Nat := 346362556042988353497857

theorem tailTrace_1011808 : CollatzResearch.WordTrace tailWord_1011808 prefixEnd_1011808 346362556042988353497857 := by
  unfold tailWord_1011808
  simp only [CollatzResearch.WordTrace]
  refine ⟨18451834759199946946978039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24602446345599929262637385 18451834759199946946978039)
  ·
    refine ⟨27677752138799920420467059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18451834759199946946978039 27677752138799920420467059)
    ·
      refine ⟨41516628208199880630700589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27677752138799920420467059 41516628208199880630700589)
      ·
        refine ⟨15568735578074955236512721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41516628208199880630700589 15568735578074955236512721)
        ·
          refine ⟨11676551683556216427384541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15568735578074955236512721 11676551683556216427384541)
          ·
            refine ⟨4378706881333581160269203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11676551683556216427384541 4378706881333581160269203)
            ·
              refine ⟨6568060322000371740403805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4378706881333581160269203 6568060322000371740403805)
              ·
                refine ⟨2463022620750139402651427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6568060322000371740403805 2463022620750139402651427)
                ·
                  refine ⟨3694533931125209103977141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2463022620750139402651427 3694533931125209103977141)
                  ·
                    refine ⟨346362556042988353497857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3694533931125209103977141 346362556042988353497857)
                    ·
                      rfl

theorem cell22_1011808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 1, 5].length) (baseStart_1011808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011808 prefixEnd_1011808 := by exact prefixLift 1011808
  have htrace : WordTrace (prefixWord ++ tailWord_1011808) baseStart_1011808 baseEnd_1011808 := by
    simpa [prefixWord, tailWord_1011808, baseEnd_1011808] using wordTrace_append hprefix tailTrace_1011808
  have hstable : (prefixWord ++ tailWord_1011808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011808).length < 2 ^ (prefixWord ++ tailWord_1011808).sum := by decide
  have hdescent : baseEnd_1011808 < baseStart_1011808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011823 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 1, 6]
def baseStart_1011823 : Nat := 118140960795 + 1011823 * 2 ^ 59
def prefixEnd_1011823 : Nat := 4983230072969 + 3 ^ 40 * 1011823 * 2
def baseEnd_1011823 : Nat := 346367690849533314372811

theorem tailTrace_1011823 : CollatzResearch.WordTrace tailWord_1011823 prefixEnd_1011823 346367690849533314372811 := by
  unfold tailWord_1011823
  simp only [CollatzResearch.WordTrace]
  refine ⟨36904216613345551455752123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24602811075563700970501415 36904216613345551455752123)
  ·
    refine ⟨55356324920018327183628185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36904216613345551455752123 55356324920018327183628185)
    ·
      refine ⟨41517243690013745387721139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55356324920018327183628185 41517243690013745387721139)
      ·
        refine ⟨62275865535020618081581709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41517243690013745387721139 62275865535020618081581709)
        ·
          refine ⟨23353449575632731780593141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62275865535020618081581709 23353449575632731780593141)
          ·
            refine ⟨2189385897715568604430607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23353449575632731780593141 2189385897715568604430607)
            ·
              refine ⟨3284078846573352906645911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189385897715568604430607 3284078846573352906645911)
              ·
                refine ⟨4926118269860029359968867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3284078846573352906645911 4926118269860029359968867)
                ·
                  refine ⟨7389177404790044039953301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4926118269860029359968867 7389177404790044039953301)
                  ·
                    refine ⟨346367690849533314372811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7389177404790044039953301 346367690849533314372811)
                    ·
                      rfl

theorem cell22_1011823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 6].length) (baseStart_1011823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011823 prefixEnd_1011823 := by exact prefixLift 1011823
  have htrace : WordTrace (prefixWord ++ tailWord_1011823) baseStart_1011823 baseEnd_1011823 := by
    simpa [prefixWord, tailWord_1011823, baseEnd_1011823] using wordTrace_append hprefix tailTrace_1011823
  have hstable : (prefixWord ++ tailWord_1011823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011823).length < 2 ^ (prefixWord ++ tailWord_1011823).sum := by decide
  have hdescent : baseEnd_1011823 < baseStart_1011823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011898 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 4, 5]
def baseStart_1011898 : Nat := 118140960795 + 1011898 * 2 ^ 59
def prefixEnd_1011898 : Nat := 4983230072969 + 3 ^ 40 * 1011898 * 2
def baseEnd_1011898 : Nat := 346393364882258118747581

theorem tailTrace_1011898 : CollatzResearch.WordTrace tailWord_1011898 prefixEnd_1011898 346393364882258118747581 := by
  unfold tailWord_1011898
  simp only [CollatzResearch.WordTrace]
  refine ⟨9226738022018459816183087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24604634725382559509821565 9226738022018459816183087)
  ·
    refine ⟨13840107033027689724274631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9226738022018459816183087 13840107033027689724274631)
    ·
      refine ⟨20760160549541534586411947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13840107033027689724274631 20760160549541534586411947)
      ·
        refine ⟨31140240824312301879617921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20760160549541534586411947 31140240824312301879617921)
        ·
          refine ⟨23355180618234226409713441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31140240824312301879617921 23355180618234226409713441)
          ·
            refine ⟨17516385463675669807285081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23355180618234226409713441 17516385463675669807285081)
            ·
              refine ⟨13137289097756752355463811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17516385463675669807285081 13137289097756752355463811)
              ·
                refine ⟨19705933646635128533195717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13137289097756752355463811 19705933646635128533195717)
                ·
                  refine ⟨3694862558744086599974197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19705933646635128533195717 3694862558744086599974197)
                  ·
                    refine ⟨346393364882258118747581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3694862558744086599974197 346393364882258118747581)
                    ·
                      rfl

theorem cell22_1011898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_1011898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011898 prefixEnd_1011898 := by exact prefixLift 1011898
  have htrace : WordTrace (prefixWord ++ tailWord_1011898) baseStart_1011898 baseEnd_1011898 := by
    simpa [prefixWord, tailWord_1011898, baseEnd_1011898] using wordTrace_append hprefix tailTrace_1011898
  have hstable : (prefixWord ++ tailWord_1011898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011898).length < 2 ^ (prefixWord ++ tailWord_1011898).sum := by decide
  have hdescent : baseEnd_1011898 < baseStart_1011898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011947 : List Nat := [1, 1, 1, 1, 2, 5, 5, 1, 1, 4]
def baseStart_1011947 : Nat := 118140960795 + 1011947 * 2 ^ 59
def prefixEnd_1011947 : Nat := 4983230072969 + 3 ^ 40 * 1011947 * 2
def baseEnd_1011947 : Nat := 346410138583638324272431

theorem tailTrace_1011947 : CollatzResearch.WordTrace tailWord_1011947 prefixEnd_1011947 346410138583638324272431 := by
  unfold tailWord_1011947
  simp only [CollatzResearch.WordTrace]
  refine ⟨36908739264896320633266095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24605826176597547088844063 36908739264896320633266095)
  ·
    refine ⟨55363108897344480949899143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36908739264896320633266095 55363108897344480949899143)
    ·
      refine ⟨83044663346016721424848715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55363108897344480949899143 83044663346016721424848715)
      ·
        refine ⟨124566995019025082137273073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83044663346016721424848715 124566995019025082137273073)
        ·
          refine ⟨93425246264268811602954805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124566995019025082137273073 93425246264268811602954805)
          ·
            refine ⟨8758616837275201087777013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93425246264268811602954805 8758616837275201087777013)
            ·
              refine ⟨821120328494550101979095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8758616837275201087777013 821120328494550101979095)
              ·
                refine ⟨1231680492741825152968643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821120328494550101979095 1231680492741825152968643)
                ·
                  refine ⟨1847520739112737729452965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231680492741825152968643 1847520739112737729452965)
                  ·
                    refine ⟨346410138583638324272431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1847520739112737729452965 346410138583638324272431)
                    ·
                      rfl

theorem cell22_1011947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 1, 4].length) (baseStart_1011947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011947 prefixEnd_1011947 := by exact prefixLift 1011947
  have htrace : WordTrace (prefixWord ++ tailWord_1011947) baseStart_1011947 baseEnd_1011947 := by
    simpa [prefixWord, tailWord_1011947, baseEnd_1011947] using wordTrace_append hprefix tailTrace_1011947
  have hstable : (prefixWord ++ tailWord_1011947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011947).length < 2 ^ (prefixWord ++ tailWord_1011947).sum := by decide
  have hdescent : baseEnd_1011947 < baseStart_1011947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011960 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 4, 3]
def baseStart_1011960 : Nat := 118140960795 + 1011960 * 2 ^ 59
def prefixEnd_1011960 : Nat := 4983230072969 + 3 ^ 40 * 1011960 * 2
def baseEnd_1011960 : Nat := 346414588749310623697391

theorem tailTrace_1011960 : CollatzResearch.WordTrace tailWord_1011960 prefixEnd_1011960 346414588749310623697391 := by
  unfold tailWord_1011960
  simp only [CollatzResearch.WordTrace]
  refine ⟨18454606706924611926744667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24606142275899482568992889 18454606706924611926744667)
  ·
    refine ⟨27681910060386917890117001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18454606706924611926744667 27681910060386917890117001)
    ·
      refine ⟨20761432545290188417587751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27681910060386917890117001 20761432545290188417587751)
      ·
        refine ⟨31142148817935282626381627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20761432545290188417587751 31142148817935282626381627)
        ·
          refine ⟨46713223226902923939572441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31142148817935282626381627 46713223226902923939572441)
          ·
            refine ⟨35034917420177192954679331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46713223226902923939572441 35034917420177192954679331)
            ·
              refine ⟨52552376130265789432018997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35034917420177192954679331 52552376130265789432018997)
              ·
                refine ⟨4926785262212417759251781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52552376130265789432018997 4926785262212417759251781)
                ·
                  refine ⟨923772236664828329859709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4926785262212417759251781 923772236664828329859709)
                  ·
                    refine ⟨346414588749310623697391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 923772236664828329859709 346414588749310623697391)
                    ·
                      rfl

theorem cell22_1011960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_1011960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011960 prefixEnd_1011960 := by exact prefixLift 1011960
  have htrace : WordTrace (prefixWord ++ tailWord_1011960) baseStart_1011960 baseEnd_1011960 := by
    simpa [prefixWord, tailWord_1011960, baseEnd_1011960] using wordTrace_append hprefix tailTrace_1011960
  have hstable : (prefixWord ++ tailWord_1011960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011960).length < 2 ^ (prefixWord ++ tailWord_1011960).sum := by decide
  have hdescent : baseEnd_1011960 < baseStart_1011960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011962 : List Nat := [3, 1, 1, 1, 1, 6, 1, 4, 4]
def baseStart_1011962 : Nat := 118140960795 + 1011962 * 2 ^ 59
def prefixEnd_1011962 : Nat := 4983230072969 + 3 ^ 40 * 1011962 * 2
def baseEnd_1011962 : Nat := 115471757796727761715795

theorem tailTrace_1011962 : CollatzResearch.WordTrace tailWord_1011962 prefixEnd_1011962 115471757796727761715795 := by
  unfold tailWord_1011962
  simp only [CollatzResearch.WordTrace]
  refine ⟨9227321589960494548765535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24606190906561318796708093 9227321589960494548765535)
  ·
    refine ⟨13840982384940741823148303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9227321589960494548765535 13840982384940741823148303)
    ·
      refine ⟨20761473577411112734722455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13840982384940741823148303 20761473577411112734722455)
      ·
        refine ⟨31142210366116669102083683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20761473577411112734722455 31142210366116669102083683)
        ·
          refine ⟨46713315549175003653125525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31142210366116669102083683 46713315549175003653125525)
          ·
            refine ⟨2189686666367578296240259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46713315549175003653125525 2189686666367578296240259)
            ·
              refine ⟨3284529999551367444360389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189686666367578296240259 3284529999551367444360389)
              ·
                refine ⟨615849374915881395817573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3284529999551367444360389 615849374915881395817573)
                ·
                  refine ⟨115471757796727761715795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 615849374915881395817573 115471757796727761715795)
                  ·
                    rfl

theorem cell22_1011962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 4].length) (baseStart_1011962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011962 prefixEnd_1011962 := by exact prefixLift 1011962
  have htrace : WordTrace (prefixWord ++ tailWord_1011962) baseStart_1011962 baseEnd_1011962 := by
    simpa [prefixWord, tailWord_1011962, baseEnd_1011962] using wordTrace_append hprefix tailTrace_1011962
  have hstable : (prefixWord ++ tailWord_1011962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011962).length < 2 ^ (prefixWord ++ tailWord_1011962).sum := by decide
  have hdescent : baseEnd_1011962 < baseStart_1011962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011973 : List Nat := [1, 3, 1, 1, 2, 1, 2, 11]
def baseStart_1011973 : Nat := 118140960795 + 1011973 * 2 ^ 59
def prefixEnd_1011973 : Nat := 4983230072969 + 3 ^ 40 * 1011973 * 2
def baseEnd_1011973 : Nat := 38491004323886991458039

theorem tailTrace_1011973 : CollatzResearch.WordTrace tailWord_1011973 prefixEnd_1011973 38491004323886991458039 := by
  unfold tailWord_1011973
  simp only [CollatzResearch.WordTrace]
  refine ⟨36909687562802127073712573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24606458375201418049141715 36909687562802127073712573)
  ·
    refine ⟨13841132836050797652642215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36909687562802127073712573 13841132836050797652642215)
    ·
      refine ⟨20761699254076196478963323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13841132836050797652642215 20761699254076196478963323)
      ·
        refine ⟨31142548881114294718444985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20761699254076196478963323 31142548881114294718444985)
        ·
          refine ⟨23356911660835721038833739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31142548881114294718444985 23356911660835721038833739)
          ·
            refine ⟨35035367491253581558250609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23356911660835721038833739 35035367491253581558250609)
            ·
              refine ⟨26276525618440186168687957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35035367491253581558250609 26276525618440186168687957)
              ·
                refine ⟨38491004323886991458039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 26276525618440186168687957 38491004323886991458039)
                ·
                  rfl

theorem cell22_1011973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 11].length) (baseStart_1011973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011973 prefixEnd_1011973 := by exact prefixLift 1011973
  have htrace : WordTrace (prefixWord ++ tailWord_1011973) baseStart_1011973 baseEnd_1011973 := by
    simpa [prefixWord, tailWord_1011973, baseEnd_1011973] using wordTrace_append hprefix tailTrace_1011973
  have hstable : (prefixWord ++ tailWord_1011973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011973).length < 2 ^ (prefixWord ++ tailWord_1011973).sum := by decide
  have hdescent : baseEnd_1011973 < baseStart_1011973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011977 : List Nat := [1, 2, 1, 1, 3, 4, 2, 3, 2, 3]
def baseStart_1011977 : Nat := 118140960795 + 1011977 * 2 ^ 59
def prefixEnd_1011977 : Nat := 4983230072969 + 3 ^ 40 * 1011977 * 2
def baseEnd_1011977 : Nat := 346420408196728246022339

theorem tailTrace_1011977 : CollatzResearch.WordTrace tailWord_1011977 prefixEnd_1011977 346420408196728246022339 := by
  unfold tailWord_1011977
  simp only [CollatzResearch.WordTrace]
  refine ⟨36909833454787635756858185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24606555636525090504572123 36909833454787635756858185)
  ·
    refine ⟨27682375091090726817643639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36909833454787635756858185 27682375091090726817643639)
    ·
      refine ⟨41523562636636090226465459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27682375091090726817643639 41523562636636090226465459)
      ·
        refine ⟨62285343954954135339698189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41523562636636090226465459 62285343954954135339698189)
        ·
          refine ⟨23357003983107800752386821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62285343954954135339698189 23357003983107800752386821)
          ·
            refine ⟨4379438246832712641072529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23357003983107800752386821 4379438246832712641072529)
            ·
              refine ⟨3284578685124534480804397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4379438246832712641072529 3284578685124534480804397)
              ·
                refine ⟨1231717006921700430301649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3284578685124534480804397 1231717006921700430301649)
                ·
                  refine ⟨923787755191275322726237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1231717006921700430301649 923787755191275322726237)
                  ·
                    refine ⟨346420408196728246022339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 923787755191275322726237 346420408196728246022339)
                    ·
                      rfl

theorem cell22_1011977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 3].length) (baseStart_1011977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011977 prefixEnd_1011977 := by exact prefixLift 1011977
  have htrace : WordTrace (prefixWord ++ tailWord_1011977) baseStart_1011977 baseEnd_1011977 := by
    simpa [prefixWord, tailWord_1011977, baseEnd_1011977] using wordTrace_append hprefix tailTrace_1011977
  have hstable : (prefixWord ++ tailWord_1011977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011977).length < 2 ^ (prefixWord ++ tailWord_1011977).sum := by decide
  have hdescent : baseEnd_1011977 < baseStart_1011977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011998 : List Nat := [4, 3, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_1011998 : Nat := 118140960795 + 1011998 * 2 ^ 59
def prefixEnd_1011998 : Nat := 4983230072969 + 3 ^ 40 * 1011998 * 2
def baseEnd_1011998 : Nat := 346427596925891191247275

theorem tailTrace_1011998 : CollatzResearch.WordTrace tailWord_1011998 prefixEnd_1011998 346427596925891191247275 := by
  unfold tailWord_1011998
  simp only [CollatzResearch.WordTrace]
  refine ⟨4613824923463944542921581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24607066258474370895581765 4613824923463944542921581)
  ·
    refine ⟨1730184346298979203595593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4613824923463944542921581 1730184346298979203595593)
    ·
      refine ⟨1297638259724234402696695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1730184346298979203595593 1297638259724234402696695)
      ·
        refine ⟨1946457389586351604045043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1297638259724234402696695 1946457389586351604045043)
        ·
          refine ⟨2919686084379527406067565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1946457389586351604045043 2919686084379527406067565)
          ·
            refine ⟨1094882281642322777275337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2919686084379527406067565 1094882281642322777275337)
            ·
              refine ⟨821161711231742082956503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1094882281642322777275337 821161711231742082956503)
              ·
                refine ⟨1231742566847613124434755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821161711231742082956503 1231742566847613124434755)
                ·
                  refine ⟨1847613850271419686652133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231742566847613124434755 1847613850271419686652133)
                  ·
                    refine ⟨346427596925891191247275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1847613850271419686652133 346427596925891191247275)
                    ·
                      rfl

theorem cell22_1011998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_1011998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1011998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1011998 prefixEnd_1011998 := by exact prefixLift 1011998
  have htrace : WordTrace (prefixWord ++ tailWord_1011998) baseStart_1011998 baseEnd_1011998 := by
    simpa [prefixWord, tailWord_1011998, baseEnd_1011998] using wordTrace_append hprefix tailTrace_1011998
  have hstable : (prefixWord ++ tailWord_1011998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011998).length < 2 ^ (prefixWord ++ tailWord_1011998).sum := by decide
  have hdescent : baseEnd_1011998 < baseStart_1011998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012035 : List Nat := [1, 1, 1, 3, 1, 3, 2, 5, 5]
def baseStart_1012035 : Nat := 118140960795 + 1012035 * 2 ^ 59
def prefixEnd_1012035 : Nat := 4983230072969 + 3 ^ 40 * 1012035 * 2
def baseEnd_1012035 : Nat := 115480087594011809357387

theorem tailTrace_1012035 : CollatzResearch.WordTrace tailWord_1012035 prefixEnd_1012035 115480087594011809357387 := by
  unfold tailWord_1012035
  simp only [CollatzResearch.WordTrace]
  refine ⟨36911948888577511662469559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24607965925718341108313039 36911948888577511662469559)
  ·
    refine ⟨55367923332866267493704339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36911948888577511662469559 55367923332866267493704339)
    ·
      refine ⟨83051884999299401240556509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55367923332866267493704339 83051884999299401240556509)
      ·
        refine ⟨31144456874737275465208691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83051884999299401240556509 31144456874737275465208691)
        ·
          refine ⟨46716685312105913197813037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31144456874737275465208691 46716685312105913197813037)
          ·
            refine ⟨17518756992039717449179889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46716685312105913197813037 17518756992039717449179889)
            ·
              refine ⟨13139067744029788086884917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17518756992039717449179889 13139067744029788086884917)
              ·
                refine ⟨1231787601002792633145461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13139067744029788086884917 1231787601002792633145461)
                ·
                  refine ⟨115480087594011809357387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1231787601002792633145461 115480087594011809357387)
                  ·
                    rfl

theorem cell22_1012035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 5].length) (baseStart_1012035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012035 prefixEnd_1012035 := by exact prefixLift 1012035
  have htrace : WordTrace (prefixWord ++ tailWord_1012035) baseStart_1012035 baseEnd_1012035 := by
    simpa [prefixWord, tailWord_1012035, baseEnd_1012035] using wordTrace_append hprefix tailTrace_1012035
  have hstable : (prefixWord ++ tailWord_1012035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012035).length < 2 ^ (prefixWord ++ tailWord_1012035).sum := by decide
  have hdescent : baseEnd_1012035 < baseStart_1012035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012050 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_1012050 : Nat := 118140960795 + 1012050 * 2 ^ 59
def prefixEnd_1012050 : Nat := 4983230072969 + 3 ^ 40 * 1012050 * 2
def baseEnd_1012050 : Nat := 346445397588580388947115

theorem tailTrace_1012050 : CollatzResearch.WordTrace tailWord_1012050 prefixEnd_1012050 346445397588580388947115 := by
  unfold tailWord_1012050
  simp only [CollatzResearch.WordTrace]
  refine ⟨9228123995880792306066401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24608330655682112816177069 9228123995880792306066401)
  ·
    refine ⟨6921092996910594229549801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9228123995880792306066401 6921092996910594229549801)
    ·
      refine ⟨5190819747682945672162351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6921092996910594229549801 5190819747682945672162351)
      ·
        refine ⟨7786229621524418508243527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5190819747682945672162351 7786229621524418508243527)
        ·
          refine ⟨11679344432286627762365291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7786229621524418508243527 11679344432286627762365291)
          ·
            refine ⟨17519016648429941643547937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11679344432286627762365291 17519016648429941643547937)
            ·
              refine ⟨13139262486322456232660953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17519016648429941643547937 13139262486322456232660953)
              ·
                refine ⟨9854446864741842174495715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13139262486322456232660953 9854446864741842174495715)
                ·
                  refine ⟨14781670297112763261743573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9854446864741842174495715 14781670297112763261743573)
                  ·
                    refine ⟨346445397588580388947115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14781670297112763261743573 346445397588580388947115)
                    ·
                      rfl

theorem cell22_1012050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_1012050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012050 prefixEnd_1012050 := by exact prefixLift 1012050
  have htrace : WordTrace (prefixWord ++ tailWord_1012050) baseStart_1012050 baseEnd_1012050 := by
    simpa [prefixWord, tailWord_1012050, baseEnd_1012050] using wordTrace_append hprefix tailTrace_1012050
  have hstable : (prefixWord ++ tailWord_1012050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012050).length < 2 ^ (prefixWord ++ tailWord_1012050).sum := by decide
  have hdescent : baseEnd_1012050 < baseStart_1012050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012065 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 7, 4]
def baseStart_1012065 : Nat := 118140960795 + 1012065 * 2 ^ 59
def prefixEnd_1012065 : Nat := 4983230072969 + 3 ^ 40 * 1012065 * 2
def baseEnd_1012065 : Nat := 346450532395125349822069

theorem tailTrace_1012065 : CollatzResearch.WordTrace tailWord_1012065 prefixEnd_1012065 346450532395125349822069 := by
  unfold tailWord_1012065
  simp only [CollatzResearch.WordTrace]
  refine ⟨36913043078468826786061649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24608695385645884524041099 36913043078468826786061649)
  ·
    refine ⟨27684782308851620089546237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36913043078468826786061649 27684782308851620089546237)
    ·
      refine ⟨10381793365819357533579839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27684782308851620089546237 10381793365819357533579839)
      ·
        refine ⟨15572690048729036300369759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10381793365819357533579839 15572690048729036300369759)
        ·
          refine ⟨23359035073093554450554639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15572690048729036300369759 23359035073093554450554639)
          ·
            refine ⟨35038552609640331675831959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23359035073093554450554639 35038552609640331675831959)
            ·
              refine ⟨52557828914460497513747939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35038552609640331675831959 52557828914460497513747939)
              ·
                refine ⟨78836743371690746270621909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52557828914460497513747939 78836743371690746270621909)
                ·
                  refine ⟨1847736172774001865717701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 78836743371690746270621909 1847736172774001865717701)
                  ·
                    refine ⟨346450532395125349822069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1847736172774001865717701 346450532395125349822069)
                    ·
                      rfl

theorem cell22_1012065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_1012065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012065 prefixEnd_1012065 := by exact prefixLift 1012065
  have htrace : WordTrace (prefixWord ++ tailWord_1012065) baseStart_1012065 baseEnd_1012065 := by
    simpa [prefixWord, tailWord_1012065, baseEnd_1012065] using wordTrace_append hprefix tailTrace_1012065
  have hstable : (prefixWord ++ tailWord_1012065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012065).length < 2 ^ (prefixWord ++ tailWord_1012065).sum := by decide
  have hdescent : baseEnd_1012065 < baseStart_1012065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012086 : List Nat := [5, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_1012086 : Nat := 118140960795 + 1012086 * 2 ^ 59
def prefixEnd_1012086 : Nat := 4983230072969 + 3 ^ 40 * 1012086 * 2
def baseEnd_1012086 : Nat := 115485907041429431682335

theorem tailTrace_1012086 : CollatzResearch.WordTrace tailWord_1012086 prefixEnd_1012086 115485907041429431682335 := by
  unfold tailWord_1012086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2307113063212046710786007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24609206007595164915050741 2307113063212046710786007)
  ·
    refine ⟨3460669594818070066179011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2307113063212046710786007 3460669594818070066179011)
    ·
      refine ⟨5191004392227105099268517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3460669594818070066179011 5191004392227105099268517)
      ·
        refine ⟨973313323542582206112847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5191004392227105099268517 973313323542582206112847)
        ·
          refine ⟨1459969985313873309169271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973313323542582206112847 1459969985313873309169271)
          ·
            refine ⟨2189954977970809963753907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459969985313873309169271 2189954977970809963753907)
            ·
              refine ⟨3284932466956214945630861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189954977970809963753907 3284932466956214945630861)
              ·
                refine ⟨1231849675108580604611573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3284932466956214945630861 1231849675108580604611573)
                ·
                  refine ⟨115485907041429431682335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1231849675108580604611573 115485907041429431682335)
                  ·
                    rfl

theorem cell22_1012086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_1012086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012086 prefixEnd_1012086 := by exact prefixLift 1012086
  have htrace : WordTrace (prefixWord ++ tailWord_1012086) baseStart_1012086 baseEnd_1012086 := by
    simpa [prefixWord, tailWord_1012086, baseEnd_1012086] using wordTrace_append hprefix tailTrace_1012086
  have hstable : (prefixWord ++ tailWord_1012086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012086).length < 2 ^ (prefixWord ++ tailWord_1012086).sum := by decide
  have hdescent : baseEnd_1012086 < baseStart_1012086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012125 : List Nat := [1, 4, 2, 1, 14]
def baseStart_1012125 : Nat := 118140960795 + 1012125 * 2 ^ 59
def prefixEnd_1012125 : Nat := 4983230072969 + 3 ^ 40 * 1012125 * 2
def baseEnd_1012125 : Nat := 1425806879100021371695

theorem tailTrace_1012125 : CollatzResearch.WordTrace tailWord_1012125 prefixEnd_1012125 1425806879100021371695 := by
  unfold tailWord_1012125
  simp only [CollatzResearch.WordTrace]
  refine ⟨36915231458251457033245829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24610154305500971355497219 36915231458251457033245829)
  ·
    refine ⟨6921605898422148193733593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36915231458251457033245829 6921605898422148193733593)
    ·
      refine ⟨5191204423816611145300195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6921605898422148193733593 5191204423816611145300195)
      ·
        refine ⟨7786806635724916717950293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5191204423816611145300195 7786806635724916717950293)
        ·
          refine ⟨1425806879100021371695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 7786806635724916717950293 1425806879100021371695)
          ·
            rfl

theorem cell22_1012125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 14].length) (baseStart_1012125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012125 prefixEnd_1012125 := by exact prefixLift 1012125
  have htrace : WordTrace (prefixWord ++ tailWord_1012125) baseStart_1012125 baseEnd_1012125 := by
    simpa [prefixWord, tailWord_1012125, baseEnd_1012125] using wordTrace_append hprefix tailTrace_1012125
  have hstable : (prefixWord ++ tailWord_1012125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012125).length < 2 ^ (prefixWord ++ tailWord_1012125).sum := by decide
  have hdescent : baseEnd_1012125 < baseStart_1012125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012127 : List Nat := [1, 1, 2, 5, 1, 1, 1, 4, 2, 4]
def baseStart_1012127 : Nat := 118140960795 + 1012127 * 2 ^ 59
def prefixEnd_1012127 : Nat := 4983230072969 + 3 ^ 40 * 1012127 * 2
def baseEnd_1012127 : Nat := 346471756262177854771879

theorem tailTrace_1012127 : CollatzResearch.WordTrace tailWord_1012127 prefixEnd_1012127 346471756262177854771879 := by
  unfold tailWord_1012127
  simp only [CollatzResearch.WordTrace]
  refine ⟨36915304404244211374818635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24610202936162807583212423 36915304404244211374818635)
  ·
    refine ⟨55372956606366317062227953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36915304404244211374818635 55372956606366317062227953)
    ·
      refine ⟨41529717454774737796670965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55372956606366317062227953 41529717454774737796670965)
      ·
        refine ⟨3893411011385131668437903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41529717454774737796670965 3893411011385131668437903)
        ·
          refine ⟨5840116517077697502656855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3893411011385131668437903 5840116517077697502656855)
          ·
            refine ⟨8760174775616546253985283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5840116517077697502656855 8760174775616546253985283)
            ·
              refine ⟨13140262163424819380977925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8760174775616546253985283 13140262163424819380977925)
              ·
                refine ⟨2463799155642153633933361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13140262163424819380977925 2463799155642153633933361)
                ·
                  refine ⟨1847849366731615225450021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2463799155642153633933361 1847849366731615225450021)
                  ·
                    refine ⟨346471756262177854771879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1847849366731615225450021 346471756262177854771879)
                    ·
                      rfl

theorem cell22_1012127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 4].length) (baseStart_1012127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012127 prefixEnd_1012127 := by exact prefixLift 1012127
  have htrace : WordTrace (prefixWord ++ tailWord_1012127) baseStart_1012127 baseEnd_1012127 := by
    simpa [prefixWord, tailWord_1012127, baseEnd_1012127] using wordTrace_append hprefix tailTrace_1012127
  have hstable : (prefixWord ++ tailWord_1012127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012127).length < 2 ^ (prefixWord ++ tailWord_1012127).sum := by decide
  have hdescent : baseEnd_1012127 < baseStart_1012127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012131 : List Nat := [1, 1, 1, 4, 1, 6, 2, 2, 4]
def baseStart_1012131 : Nat := 118140960795 + 1012131 * 2 ^ 59
def prefixEnd_1012131 : Nat := 4983230072969 + 3 ^ 40 * 1012131 * 2
def baseEnd_1012131 : Nat := 115491041847974392557289

theorem tailTrace_1012131 : CollatzResearch.WordTrace tailWord_1012131 prefixEnd_1012131 115491041847974392557289 := by
  unfold tailWord_1012131
  simp only [CollatzResearch.WordTrace]
  refine ⟨36915450296229720057964247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24610300197486480038642831 36915450296229720057964247)
  ·
    refine ⟨55373175444344580086946371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36915450296229720057964247 55373175444344580086946371)
    ·
      refine ⟨83059763166516870130419557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55373175444344580086946371 83059763166516870130419557)
      ·
        refine ⟨15573705593721913149453667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83059763166516870130419557 15573705593721913149453667)
        ·
          refine ⟨23360558390582869724180501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15573705593721913149453667 23360558390582869724180501)
          ·
            refine ⟨1095026174558572018320961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23360558390582869724180501 1095026174558572018320961)
            ·
              refine ⟨821269630918929013740721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1095026174558572018320961 821269630918929013740721)
              ·
                refine ⟨615952223189196760305541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 821269630918929013740721 615952223189196760305541)
                ·
                  refine ⟨115491041847974392557289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 615952223189196760305541 115491041847974392557289)
                  ·
                    rfl

theorem cell22_1012131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 4].length) (baseStart_1012131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012131 prefixEnd_1012131 := by exact prefixLift 1012131
  have htrace : WordTrace (prefixWord ++ tailWord_1012131) baseStart_1012131 baseEnd_1012131 := by
    simpa [prefixWord, tailWord_1012131, baseEnd_1012131] using wordTrace_append hprefix tailTrace_1012131
  have hstable : (prefixWord ++ tailWord_1012131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012131).length < 2 ^ (prefixWord ++ tailWord_1012131).sum := by decide
  have hdescent : baseEnd_1012131 < baseStart_1012131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012140 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 2, 7]
def baseStart_1012140 : Nat := 118140960795 + 1012140 * 2 ^ 59
def prefixEnd_1012140 : Nat := 4983230072969 + 3 ^ 40 * 1012140 * 2
def baseEnd_1012140 : Nat := 346476206427850154196839

theorem tailTrace_1012140 : CollatzResearch.WordTrace tailWord_1012140 prefixEnd_1012140 346476206427850154196839 := by
  unfold tailWord_1012140
  simp only [CollatzResearch.WordTrace]
  refine ⟨18457889276598557297520937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24610519035464743063361249 18457889276598557297520937)
  ·
    refine ⟨13843416957448917973140703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18457889276598557297520937 13843416957448917973140703)
    ·
      refine ⟨20765125436173376959711055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13843416957448917973140703 20765125436173376959711055)
      ·
        refine ⟨31147688154260065439566583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20765125436173376959711055 31147688154260065439566583)
        ·
          refine ⟨46721532231390098159349875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31147688154260065439566583 46721532231390098159349875)
          ·
            refine ⟨70082298347085147239024813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46721532231390098159349875 70082298347085147239024813)
            ·
              refine ⟨26280861880156930214634305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70082298347085147239024813 26280861880156930214634305)
              ·
                refine ⟨19710646410117697660975729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26280861880156930214634305 19710646410117697660975729)
                ·
                  refine ⟨14782984807588273245731797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19710646410117697660975729 14782984807588273245731797)
                  ·
                    refine ⟨346476206427850154196839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14782984807588273245731797 346476206427850154196839)
                    ·
                      rfl

theorem cell22_1012140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_1012140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012140 prefixEnd_1012140 := by exact prefixLift 1012140
  have htrace : WordTrace (prefixWord ++ tailWord_1012140) baseStart_1012140 baseEnd_1012140 := by
    simpa [prefixWord, tailWord_1012140, baseEnd_1012140] using wordTrace_append hprefix tailTrace_1012140
  have hstable : (prefixWord ++ tailWord_1012140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012140).length < 2 ^ (prefixWord ++ tailWord_1012140).sum := by decide
  have hdescent : baseEnd_1012140 < baseStart_1012140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012191 : List Nat := [1, 1, 2, 3, 3, 2, 2, 4, 1, 3]
def baseStart_1012191 : Nat := 118140960795 + 1012191 * 2 ^ 59
def prefixEnd_1012191 : Nat := 4983230072969 + 3 ^ 40 * 1012191 * 2
def baseEnd_1012191 : Nat := 346493664770103021171683

theorem tailTrace_1012191 : CollatzResearch.WordTrace tailWord_1012191 prefixEnd_1012191 346493664770103021171683 := by
  unfold tailWord_1012191
  simp only [CollatzResearch.WordTrace]
  refine ⟨36917638676012350305148427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24611759117341566870098951 36917638676012350305148427)
  ·
    refine ⟨55376458014018525457722641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36917638676012350305148427 55376458014018525457722641)
    ·
      refine ⟨41532343510513894093291981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55376458014018525457722641 41532343510513894093291981)
      ·
        refine ⟨15574628816442710284984493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41532343510513894093291981 15574628816442710284984493)
        ·
          refine ⟨5840485806166016356869185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15574628816442710284984493 5840485806166016356869185)
          ·
            refine ⟨4380364354624512267651889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5840485806166016356869185 4380364354624512267651889)
            ·
              refine ⟨3285273265968384200738917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4380364354624512267651889 3285273265968384200738917)
              ·
                refine ⟨615988737369072037638547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3285273265968384200738917 615988737369072037638547)
                ·
                  refine ⟨923983106053608056457821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615988737369072037638547 923983106053608056457821)
                  ·
                    refine ⟨346493664770103021171683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 923983106053608056457821 346493664770103021171683)
                    ·
                      rfl

theorem cell22_1012191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 1, 3].length) (baseStart_1012191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012191 prefixEnd_1012191 := by exact prefixLift 1012191
  have htrace : WordTrace (prefixWord ++ tailWord_1012191) baseStart_1012191 baseEnd_1012191 := by
    simpa [prefixWord, tailWord_1012191, baseEnd_1012191] using wordTrace_append hprefix tailTrace_1012191
  have hstable : (prefixWord ++ tailWord_1012191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012191).length < 2 ^ (prefixWord ++ tailWord_1012191).sum := by decide
  have hdescent : baseEnd_1012191 < baseStart_1012191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012204 : List Nat := [2, 2, 1, 1, 2, 1, 7, 1, 5]
def baseStart_1012204 : Nat := 118140960795 + 1012204 * 2 ^ 59
def prefixEnd_1012204 : Nat := 4983230072969 + 3 ^ 40 * 1012204 * 2
def baseEnd_1012204 : Nat := 115499371645258440198881

theorem tailTrace_1012204 : CollatzResearch.WordTrace tailWord_1012204 prefixEnd_1012204 115499371645258440198881 := by
  unfold tailWord_1012204
  simp only [CollatzResearch.WordTrace]
  refine ⟨18459056412482626762685833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24612075216643502350247777 18459056412482626762685833)
  ·
    refine ⟨13844292309361970072014375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18459056412482626762685833 13844292309361970072014375)
    ·
      refine ⟨20766438464042955108021563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13844292309361970072014375 20766438464042955108021563)
      ·
        refine ⟨31149657696064432662032345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20766438464042955108021563 31149657696064432662032345)
        ·
          refine ⟨23362243272048324496524259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31149657696064432662032345 23362243272048324496524259)
          ·
            refine ⟨35043364908072486744786389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23362243272048324496524259 35043364908072486744786389)
            ·
              refine ⟨821328865032948908080931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35043364908072486744786389 821328865032948908080931)
              ·
                refine ⟨1231993297549423362121397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821328865032948908080931 1231993297549423362121397)
                ·
                  refine ⟨115499371645258440198881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1231993297549423362121397 115499371645258440198881)
                  ·
                    rfl

theorem cell22_1012204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 5].length) (baseStart_1012204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012204 prefixEnd_1012204 := by exact prefixLift 1012204
  have htrace : WordTrace (prefixWord ++ tailWord_1012204) baseStart_1012204 baseEnd_1012204 := by
    simpa [prefixWord, tailWord_1012204, baseEnd_1012204] using wordTrace_append hprefix tailTrace_1012204
  have hstable : (prefixWord ++ tailWord_1012204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012204).length < 2 ^ (prefixWord ++ tailWord_1012204).sum := by decide
  have hdescent : baseEnd_1012204 < baseStart_1012204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012217 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 3, 4]
def baseStart_1012217 : Nat := 118140960795 + 1012217 * 2 ^ 59
def prefixEnd_1012217 : Nat := 4983230072969 + 3 ^ 40 * 1012217 * 2
def baseEnd_1012217 : Nat := 346502565101447620021603

theorem tailTrace_1012217 : CollatzResearch.WordTrace tailWord_1012217 prefixEnd_1012217 346502565101447620021603 := by
  unfold tailWord_1012217
  simp only [CollatzResearch.WordTrace]
  refine ⟨36918586973918156745594905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24612391315945437830396603 36918586973918156745594905)
  ·
    refine ⟨27688940230438617559196179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36918586973918156745594905 27688940230438617559196179)
    ·
      refine ⟨41533410345657926338794269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27688940230438617559196179 41533410345657926338794269)
      ·
        refine ⟨15575028879621722377047851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41533410345657926338794269 15575028879621722377047851)
        ·
          refine ⟨23362543319432583565571777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15575028879621722377047851 23362543319432583565571777)
          ·
            refine ⟨17521907489574437674178833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23362543319432583565571777 17521907489574437674178833)
            ·
              refine ⟨13141430617180828255634125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17521907489574437674178833 13141430617180828255634125)
              ·
                refine ⟨4928036481442810595862797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13141430617180828255634125 4928036481442810595862797)
                ·
                  refine ⟨1848013680541053973448549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4928036481442810595862797 1848013680541053973448549)
                  ·
                    refine ⟨346502565101447620021603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1848013680541053973448549 346502565101447620021603)
                    ·
                      rfl

theorem cell22_1012217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 4].length) (baseStart_1012217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012217 prefixEnd_1012217 := by exact prefixLift 1012217
  have htrace : WordTrace (prefixWord ++ tailWord_1012217) baseStart_1012217 baseEnd_1012217 := by
    simpa [prefixWord, tailWord_1012217, baseEnd_1012217] using wordTrace_append hprefix tailTrace_1012217
  have hstable : (prefixWord ++ tailWord_1012217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012217).length < 2 ^ (prefixWord ++ tailWord_1012217).sum := by decide
  have hdescent : baseEnd_1012217 < baseStart_1012217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012234 : List Nat := [3, 1, 2, 2, 2, 1, 1, 5, 1, 4]
def baseStart_1012234 : Nat := 118140960795 + 1012234 * 2 ^ 59
def prefixEnd_1012234 : Nat := 4983230072969 + 3 ^ 40 * 1012234 * 2
def baseEnd_1012234 : Nat := 346508384548865242346551

theorem tailTrace_1012234 : CollatzResearch.WordTrace tailWord_1012234 prefixEnd_1012234 346508384548865242346551 := by
  unfold tailWord_1012234
  simp only [CollatzResearch.WordTrace]
  refine ⟨9229801753714142162240939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24612804676571045765975837 9229801753714142162240939)
  ·
    refine ⟨13844702630571213243361409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9229801753714142162240939 13844702630571213243361409)
    ·
      refine ⟨10383526972928409932521057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13844702630571213243361409 10383526972928409932521057)
      ·
        refine ⟨7787645229696307449390793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10383526972928409932521057 7787645229696307449390793)
        ·
          refine ⟨5840733922272230587043095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7787645229696307449390793 5840733922272230587043095)
          ·
            refine ⟨8761100883408345880564643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5840733922272230587043095 8761100883408345880564643)
            ·
              refine ⟨13141651325112518820846965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8761100883408345880564643 13141651325112518820846965)
              ·
                refine ⟨1232029811729298639454403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13141651325112518820846965 1232029811729298639454403)
                ·
                  refine ⟨1848044717593947959181605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1232029811729298639454403 1848044717593947959181605)
                  ·
                    refine ⟨346508384548865242346551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1848044717593947959181605 346508384548865242346551)
                    ·
                      rfl

theorem cell22_1012234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_1012234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012234 prefixEnd_1012234 := by exact prefixLift 1012234
  have htrace : WordTrace (prefixWord ++ tailWord_1012234) baseStart_1012234 baseEnd_1012234 := by
    simpa [prefixWord, tailWord_1012234, baseEnd_1012234] using wordTrace_append hprefix tailTrace_1012234
  have hstable : (prefixWord ++ tailWord_1012234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012234).length < 2 ^ (prefixWord ++ tailWord_1012234).sum := by decide
  have hdescent : baseEnd_1012234 < baseStart_1012234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012277 : List Nat := [1, 3, 3, 1, 1, 2, 1, 10]
def baseStart_1012277 : Nat := 118140960795 + 1012277 * 2 ^ 59
def prefixEnd_1012277 : Nat := 4983230072969 + 3 ^ 40 * 1012277 * 2
def baseEnd_1012277 : Nat := 38502567147514162613491

theorem tailTrace_1012277 : CollatzResearch.WordTrace tailWord_1012277 prefixEnd_1012277 38502567147514162613491 := by
  unfold tailWord_1012277
  simp only [CollatzResearch.WordTrace]
  refine ⟨36920775353700786992779085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24613850235800524661852723 36920775353700786992779085)
  ·
    refine ⟨13845290757637795122292157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36920775353700786992779085 13845290757637795122292157)
    ·
      refine ⟨5191984034114173170859559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13845290757637795122292157 5191984034114173170859559)
      ·
        refine ⟨7787976051171259756289339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5191984034114173170859559 7787976051171259756289339)
        ·
          refine ⟨11681964076756889634434009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7787976051171259756289339 11681964076756889634434009)
          ·
            refine ⟨8761473057567667225825507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11681964076756889634434009 8761473057567667225825507)
            ·
              refine ⟨13142209586351500838738261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8761473057567667225825507 13142209586351500838738261)
              ·
                refine ⟨38502567147514162613491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13142209586351500838738261 38502567147514162613491)
                ·
                  rfl

theorem cell22_1012277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 10].length) (baseStart_1012277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012277 prefixEnd_1012277 := by exact prefixLift 1012277
  have htrace : WordTrace (prefixWord ++ tailWord_1012277) baseStart_1012277 baseEnd_1012277 := by
    simpa [prefixWord, tailWord_1012277, baseEnd_1012277] using wordTrace_append hprefix tailTrace_1012277
  have hstable : (prefixWord ++ tailWord_1012277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012277).length < 2 ^ (prefixWord ++ tailWord_1012277).sum := by decide
  have hdescent : baseEnd_1012277 < baseStart_1012277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012279 : List Nat := [1, 1, 3, 1, 2, 3, 4, 1, 2, 4]
def baseStart_1012279 : Nat := 118140960795 + 1012279 * 2 ^ 59
def prefixEnd_1012279 : Nat := 4983230072969 + 3 ^ 40 * 1012279 * 2
def baseEnd_1012279 : Nat := 346523788968500124971413

theorem tailTrace_1012279 : CollatzResearch.WordTrace tailWord_1012279 prefixEnd_1012279 346523788968500124971413 := by
  unfold tailWord_1012279
  simp only [CollatzResearch.WordTrace]
  refine ⟨36920848299693541334351891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24613898866462360889567927 36920848299693541334351891)
  ·
    refine ⟨55381272449540312001527837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36920848299693541334351891 55381272449540312001527837)
    ·
      refine ⟨20767977168577617000572939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55381272449540312001527837 20767977168577617000572939)
      ·
        refine ⟨31151965752866425500859409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20767977168577617000572939 31151965752866425500859409)
        ·
          refine ⟨23363974314649819125644557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31151965752866425500859409 23363974314649819125644557)
          ·
            refine ⟨8761490367993682172116709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23363974314649819125644557 8761490367993682172116709)
            ·
              refine ⟨1642779443998815407271883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8761490367993682172116709 1642779443998815407271883)
              ·
                refine ⟨2464169165998223110907825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642779443998815407271883 2464169165998223110907825)
                ·
                  refine ⟨1848126874498667333180869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2464169165998223110907825 1848126874498667333180869)
                  ·
                    refine ⟨346523788968500124971413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1848126874498667333180869 346523788968500124971413)
                    ·
                      rfl

theorem cell22_1012279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_1012279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012279 prefixEnd_1012279 := by exact prefixLift 1012279
  have htrace : WordTrace (prefixWord ++ tailWord_1012279) baseStart_1012279 baseEnd_1012279 := by
    simpa [prefixWord, tailWord_1012279, baseEnd_1012279] using wordTrace_append hprefix tailTrace_1012279
  have hstable : (prefixWord ++ tailWord_1012279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012279).length < 2 ^ (prefixWord ++ tailWord_1012279).sum := by decide
  have hdescent : baseEnd_1012279 < baseStart_1012279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012356 : List Nat := [2, 3, 2, 1, 3, 1, 3, 2, 5]
def baseStart_1012356 : Nat := 118140960795 + 1012356 * 2 ^ 59
def prefixEnd_1012356 : Nat := 4983230072969 + 3 ^ 40 * 1012356 * 2
def baseEnd_1012356 : Nat := 115516715880699196932059

theorem tailTrace_1012356 : CollatzResearch.WordTrace tailWord_1012356 prefixEnd_1012356 115516715880699196932059 := by
  unfold tailWord_1012356
  simp only [CollatzResearch.WordTrace]
  refine ⟨18461828360207291742452461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24615771146943055656603281 18461828360207291742452461)
  ·
    refine ⟨6923185635077734403419673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18461828360207291742452461 6923185635077734403419673)
    ·
      refine ⟨5192389226308300802564755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6923185635077734403419673 5192389226308300802564755)
      ·
        refine ⟨7788583839462451203847133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5192389226308300802564755 7788583839462451203847133)
        ·
          refine ⟨2920718939798419201442675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7788583839462451203847133 2920718939798419201442675)
          ·
            refine ⟨4381078409697628802164013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2920718939798419201442675 4381078409697628802164013)
            ·
              refine ⟨1642904403636610800811505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4381078409697628802164013 1642904403636610800811505)
              ·
                refine ⟨1232178302727458100608629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1642904403636610800811505 1232178302727458100608629)
                ·
                  refine ⟨115516715880699196932059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1232178302727458100608629 115516715880699196932059)
                  ·
                    rfl

theorem cell22_1012356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_1012356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012356 prefixEnd_1012356 := by exact prefixLift 1012356
  have htrace : WordTrace (prefixWord ++ tailWord_1012356) baseStart_1012356 baseEnd_1012356 := by
    simpa [prefixWord, tailWord_1012356, baseEnd_1012356] using wordTrace_append hprefix tailTrace_1012356
  have hstable : (prefixWord ++ tailWord_1012356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012356).length < 2 ^ (prefixWord ++ tailWord_1012356).sum := by decide
  have hdescent : baseEnd_1012356 < baseStart_1012356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012367 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 10]
def baseStart_1012367 : Nat := 118140960795 + 1012367 * 2 ^ 59
def prefixEnd_1012367 : Nat := 4983230072969 + 3 ^ 40 * 1012367 * 2
def baseEnd_1012367 : Nat := 115517971055632409590381

theorem tailTrace_1012367 : CollatzResearch.WordTrace tailWord_1012367 prefixEnd_1012367 115517971055632409590381 := by
  unfold tailWord_1012367
  simp only [CollatzResearch.WordTrace]
  refine ⟨36924057923374732363555355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24616038615583154909036903 36924057923374732363555355)
  ·
    refine ⟨55386086885062098545333033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36924057923374732363555355 55386086885062098545333033)
    ·
      refine ⟨41539565163796573908999775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55386086885062098545333033 41539565163796573908999775)
      ·
        refine ⟨62309347745694860863499663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41539565163796573908999775 62309347745694860863499663)
        ·
          refine ⟨93464021618542291295249495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62309347745694860863499663 93464021618542291295249495)
          ·
            refine ⟨140196032427813436942874243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93464021618542291295249495 140196032427813436942874243)
            ·
              refine ⟨210294048641720155414311365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140196032427813436942874243 210294048641720155414311365)
              ·
                refine ⟨39430134120322529140183381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210294048641720155414311365 39430134120322529140183381)
                ·
                  refine ⟨115517971055632409590381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 39430134120322529140183381 115517971055632409590381)
                  ·
                    rfl

theorem cell22_1012367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 10].length) (baseStart_1012367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012367 prefixEnd_1012367 := by exact prefixLift 1012367
  have htrace : WordTrace (prefixWord ++ tailWord_1012367) baseStart_1012367 baseEnd_1012367 := by
    simpa [prefixWord, tailWord_1012367, baseEnd_1012367] using wordTrace_append hprefix tailTrace_1012367
  have hstable : (prefixWord ++ tailWord_1012367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012367).length < 2 ^ (prefixWord ++ tailWord_1012367).sum := by decide
  have hdescent : baseEnd_1012367 < baseStart_1012367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012394 : List Nat := [3, 1, 5, 2, 1, 2, 1, 3, 1, 3]
def baseStart_1012394 : Nat := 118140960795 + 1012394 * 2 ^ 59
def prefixEnd_1012394 : Nat := 4983230072969 + 3 ^ 40 * 1012394 * 2
def baseEnd_1012394 : Nat := 346563155818678158346061

theorem tailTrace_1012394 : CollatzResearch.WordTrace tailWord_1012394 prefixEnd_1012394 346563155818678158346061 := by
  unfold tailWord_1012394
  simp only [CollatzResearch.WordTrace]
  refine ⟨9231260673569228993697059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24616695129517943983192157 9231260673569228993697059)
  ·
    refine ⟨13846891010353843490545589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9231260673569228993697059 13846891010353843490545589)
    ·
      refine ⟨1298146032220672827238649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13846891010353843490545589 1298146032220672827238649)
      ·
        refine ⟨973609524165504620428987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1298146032220672827238649 973609524165504620428987)
        ·
          refine ⟨1460414286248256930643481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973609524165504620428987 1460414286248256930643481)
          ·
            refine ⟨1095310714686192697982611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1460414286248256930643481 1095310714686192697982611)
            ·
              refine ⟨1642966072029289046973917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095310714686192697982611 1642966072029289046973917)
              ·
                refine ⟨616112277010983392615219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1642966072029289046973917 616112277010983392615219)
                ·
                  refine ⟨924168415516475088922829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 616112277010983392615219 924168415516475088922829)
                  ·
                    refine ⟨346563155818678158346061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 924168415516475088922829 346563155818678158346061)
                    ·
                      rfl

theorem cell22_1012394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_1012394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012394 prefixEnd_1012394 := by exact prefixLift 1012394
  have htrace : WordTrace (prefixWord ++ tailWord_1012394) baseStart_1012394 baseEnd_1012394 := by
    simpa [prefixWord, tailWord_1012394, baseEnd_1012394] using wordTrace_append hprefix tailTrace_1012394
  have hstable : (prefixWord ++ tailWord_1012394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012394).length < 2 ^ (prefixWord ++ tailWord_1012394).sum := by decide
  have hdescent : baseEnd_1012394 < baseStart_1012394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012416 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 4, 3]
def baseStart_1012416 : Nat := 118140960795 + 1012416 * 2 ^ 59
def prefixEnd_1012416 : Nat := 4983230072969 + 3 ^ 40 * 1012416 * 2
def baseEnd_1012416 : Nat := 346570686868277434295993

theorem tailTrace_1012416 : CollatzResearch.WordTrace tailWord_1012416 prefixEnd_1012416 346570686868277434295993 := by
  unfold tailWord_1012416
  simp only [CollatzResearch.WordTrace]
  refine ⟨18462922550098606866044551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24617230066798142488059401 18462922550098606866044551)
  ·
    refine ⟨27694383825147910299066827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18462922550098606866044551 27694383825147910299066827)
    ·
      refine ⟨41541575737721865448600241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27694383825147910299066827 41541575737721865448600241)
      ·
        refine ⟨31156181803291399086450181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41541575737721865448600241 31156181803291399086450181)
        ·
          refine ⟨5841784088117137328709409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31156181803291399086450181 5841784088117137328709409)
          ·
            refine ⟨4381338066087852996532057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5841784088117137328709409 4381338066087852996532057)
            ·
              refine ⟨3286003549565889747399043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4381338066087852996532057 3286003549565889747399043)
              ·
                refine ⟨4929005324348834621098565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3286003549565889747399043 4929005324348834621098565)
                ·
                  refine ⟨924188498315406491455981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4929005324348834621098565 924188498315406491455981)
                  ·
                    refine ⟨346570686868277434295993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 924188498315406491455981 346570686868277434295993)
                    ·
                      rfl

theorem cell22_1012416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 4, 3].length) (baseStart_1012416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012416 prefixEnd_1012416 := by exact prefixLift 1012416
  have htrace : WordTrace (prefixWord ++ tailWord_1012416) baseStart_1012416 baseEnd_1012416 := by
    simpa [prefixWord, tailWord_1012416, baseEnd_1012416] using wordTrace_append hprefix tailTrace_1012416
  have hstable : (prefixWord ++ tailWord_1012416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012416).length < 2 ^ (prefixWord ++ tailWord_1012416).sum := by decide
  have hdescent : baseEnd_1012416 < baseStart_1012416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012437 : List Nat := [1, 3, 2, 5, 2, 1, 1, 2, 1, 4]
def baseStart_1012437 : Nat := 118140960795 + 1012437 * 2 ^ 59
def prefixEnd_1012437 : Nat := 4983230072969 + 3 ^ 40 * 1012437 * 2
def baseEnd_1012437 : Nat := 346577875597440379520929

theorem tailTrace_1012437 : CollatzResearch.WordTrace tailWord_1012437 prefixEnd_1012437 346577875597440379520929 := by
  unfold tailWord_1012437
  simp only [CollatzResearch.WordTrace]
  refine ⟨36926611033121134318603565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24617740688747422879069043 36926611033121134318603565)
  ·
    refine ⟨13847479137420425369476337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36926611033121134318603565 13847479137420425369476337)
    ·
      refine ⟨10385609353065319027107253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13847479137420425369476337 10385609353065319027107253)
      ·
        refine ⟨973650876849873658791305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10385609353065319027107253 973650876849873658791305)
        ·
          refine ⟨730238157637405244093479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 973650876849873658791305 730238157637405244093479)
          ·
            refine ⟨1095357236456107866140219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730238157637405244093479 1095357236456107866140219)
            ·
              refine ⟨1643035854684161799210329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095357236456107866140219 1643035854684161799210329)
              ·
                refine ⟨1232276891013121349407747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1643035854684161799210329 1232276891013121349407747)
                ·
                  refine ⟨1848415336519682024111621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1232276891013121349407747 1848415336519682024111621)
                  ·
                    refine ⟨346577875597440379520929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1848415336519682024111621 346577875597440379520929)
                    ·
                      rfl

theorem cell22_1012437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_1012437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012437 prefixEnd_1012437 := by exact prefixLift 1012437
  have htrace : WordTrace (prefixWord ++ tailWord_1012437) baseStart_1012437 baseEnd_1012437 := by
    simpa [prefixWord, tailWord_1012437, baseEnd_1012437] using wordTrace_append hprefix tailTrace_1012437
  have hstable : (prefixWord ++ tailWord_1012437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012437).length < 2 ^ (prefixWord ++ tailWord_1012437).sum := by decide
  have hdescent : baseEnd_1012437 < baseStart_1012437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012474 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 7]
def baseStart_1012474 : Nat := 118140960795 + 1012474 * 2 ^ 59
def prefixEnd_1012474 : Nat := 4983230072969 + 3 ^ 40 * 1012474 * 2
def baseEnd_1012474 : Nat := 115530180484528205448605

theorem tailTrace_1012474 : CollatzResearch.WordTrace tailWord_1012474 prefixEnd_1012474 115530180484528205448605 := by
  unfold tailWord_1012474
  simp only [CollatzResearch.WordTrace]
  refine ⟨9231990133496772409425119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24618640355991393091800317 9231990133496772409425119)
  ·
    refine ⟨13847985200245158614137679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9231990133496772409425119 13847985200245158614137679)
    ·
      refine ⟨20771977800367737921206519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13847985200245158614137679 20771977800367737921206519)
      ·
        refine ⟨31157966700551606881809779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20771977800367737921206519 31157966700551606881809779)
        ·
          refine ⟨46736950050827410322714669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31157966700551606881809779 46736950050827410322714669)
          ·
            refine ⟨17526356269060278871018001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46736950050827410322714669 17526356269060278871018001)
            ·
              refine ⟨13144767201795209153263501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17526356269060278871018001 13144767201795209153263501)
              ·
                refine ⟨4929287700673203432473813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13144767201795209153263501 4929287700673203432473813)
                ·
                  refine ⟨115530180484528205448605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4929287700673203432473813 115530180484528205448605)
                  ·
                    rfl

theorem cell22_1012474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_1012474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012474 prefixEnd_1012474 := by exact prefixLift 1012474
  have htrace : WordTrace (prefixWord ++ tailWord_1012474) baseStart_1012474 baseEnd_1012474 := by
    simpa [prefixWord, tailWord_1012474, baseEnd_1012474] using wordTrace_append hprefix tailTrace_1012474
  have hstable : (prefixWord ++ tailWord_1012474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012474).length < 2 ^ (prefixWord ++ tailWord_1012474).sum := by decide
  have hdescent : baseEnd_1012474 < baseStart_1012474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012489 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 1, 7]
def baseStart_1012489 : Nat := 118140960795 + 1012489 * 2 ^ 59
def prefixEnd_1012489 : Nat := 4983230072969 + 3 ^ 40 * 1012489 * 2
def baseEnd_1012489 : Nat := 346595676260129577220769

theorem tailTrace_1012489 : CollatzResearch.WordTrace tailWord_1012489 prefixEnd_1012489 346595676260129577220769 := by
  unfold tailWord_1012489
  simp only [CollatzResearch.WordTrace]
  refine ⟨36928507628932747199496521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24619005085955164799664347 36928507628932747199496521)
  ·
    refine ⟨27696380721699560399622391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36928507628932747199496521 27696380721699560399622391)
    ·
      refine ⟨41544571082549340599433587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27696380721699560399622391 41544571082549340599433587)
      ·
        refine ⟨62316856623824010899150381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41544571082549340599433587 62316856623824010899150381)
        ·
          refine ⟨23368821233934004087181393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62316856623824010899150381 23368821233934004087181393)
          ·
            refine ⟨17526615925450503065386045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23368821233934004087181393 17526615925450503065386045)
            ·
              refine ⟨6572480972043938649519767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17526615925450503065386045 6572480972043938649519767)
              ·
                refine ⟨9858721458065907974279651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6572480972043938649519767 9858721458065907974279651)
                ·
                  refine ⟨14788082187098861961419477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9858721458065907974279651 14788082187098861961419477)
                  ·
                    refine ⟨346595676260129577220769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14788082187098861961419477 346595676260129577220769)
                    ·
                      rfl

theorem cell22_1012489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_1012489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012489 prefixEnd_1012489 := by exact prefixLift 1012489
  have htrace : WordTrace (prefixWord ++ tailWord_1012489) baseStart_1012489 baseEnd_1012489 := by
    simpa [prefixWord, tailWord_1012489, baseEnd_1012489] using wordTrace_append hprefix tailTrace_1012489
  have hstable : (prefixWord ++ tailWord_1012489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012489).length < 2 ^ (prefixWord ++ tailWord_1012489).sum := by decide
  have hdescent : baseEnd_1012489 < baseStart_1012489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012521 : List Nat := [1, 2, 1, 1, 1, 1, 1, 9, 1, 4]
def baseStart_1012521 : Nat := 118140960795 + 1012521 * 2 ^ 59
def prefixEnd_1012521 : Nat := 4983230072969 + 3 ^ 40 * 1012521 * 2
def baseEnd_1012521 : Nat := 346606630514092160420671

theorem tailTrace_1012521 : CollatzResearch.WordTrace tailWord_1012521 prefixEnd_1012521 346606630514092160420671 := by
  unfold tailWord_1012521
  simp only [CollatzResearch.WordTrace]
  refine ⟨36929674764816816664661417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24619783176544544443107611 36929674764816816664661417)
  ·
    refine ⟨27697256073612612498496063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36929674764816816664661417 27697256073612612498496063)
    ·
      refine ⟨41545884110418918747744095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27697256073612612498496063 41545884110418918747744095)
      ·
        refine ⟨62318826165628378121616143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41545884110418918747744095 62318826165628378121616143)
        ·
          refine ⟨93478239248442567182424215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62318826165628378121616143 93478239248442567182424215)
          ·
            refine ⟨140217358872663850773636323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93478239248442567182424215 140217358872663850773636323)
            ·
              refine ⟨210326038308995776160454485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140217358872663850773636323 210326038308995776160454485)
              ·
                refine ⟨1232379130716772125940163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 210326038308995776160454485 1232379130716772125940163)
                ·
                  refine ⟨1848568696075158188910245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1232379130716772125940163 1848568696075158188910245)
                  ·
                    refine ⟨346606630514092160420671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1848568696075158188910245 346606630514092160420671)
                    ·
                      rfl

theorem cell22_1012521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 4].length) (baseStart_1012521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012521 prefixEnd_1012521 := by exact prefixLift 1012521
  have htrace : WordTrace (prefixWord ++ tailWord_1012521) baseStart_1012521 baseEnd_1012521 := by
    simpa [prefixWord, tailWord_1012521, baseEnd_1012521] using wordTrace_append hprefix tailTrace_1012521
  have hstable : (prefixWord ++ tailWord_1012521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012521).length < 2 ^ (prefixWord ++ tailWord_1012521).sum := by decide
  have hdescent : baseEnd_1012521 < baseStart_1012521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012525 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 7]
def baseStart_1012525 : Nat := 118140960795 + 1012525 * 2 ^ 59
def prefixEnd_1012525 : Nat := 4983230072969 + 3 ^ 40 * 1012525 * 2
def baseEnd_1012525 : Nat := 115535999931945827773553

theorem tailTrace_1012525 : CollatzResearch.WordTrace tailWord_1012525 prefixEnd_1012525 115535999931945827773553 := by
  unfold tailWord_1012525
  simp only [CollatzResearch.WordTrace]
  refine ⟨36929820656802325347807029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24619880437868216898538019 36929820656802325347807029)
  ·
    refine ⟨3462170686575218001356909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36929820656802325347807029 3462170686575218001356909)
    ·
      refine ⟨1298314007465706750508841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3462170686575218001356909 1298314007465706750508841)
      ·
        refine ⟨973735505599280062881631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1298314007465706750508841 973735505599280062881631)
        ·
          refine ⟨1460603258398920094322447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973735505599280062881631 1460603258398920094322447)
          ·
            refine ⟨2190904887598380141483671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460603258398920094322447 2190904887598380141483671)
            ·
              refine ⟨3286357331397570212225507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2190904887598380141483671 3286357331397570212225507)
              ·
                refine ⟨4929535997096355318338261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3286357331397570212225507 4929535997096355318338261)
                ·
                  refine ⟨115535999931945827773553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4929535997096355318338261 115535999931945827773553)
                  ·
                    rfl

theorem cell22_1012525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_1012525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012525 prefixEnd_1012525 := by exact prefixLift 1012525
  have htrace : WordTrace (prefixWord ++ tailWord_1012525) baseStart_1012525 baseEnd_1012525 := by
    simpa [prefixWord, tailWord_1012525, baseEnd_1012525] using wordTrace_append hprefix tailTrace_1012525
  have hstable : (prefixWord ++ tailWord_1012525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012525).length < 2 ^ (prefixWord ++ tailWord_1012525).sum := by decide
  have hdescent : baseEnd_1012525 < baseStart_1012525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012536 : List Nat := [2, 1, 2, 1, 3, 2, 4, 1, 6]
def baseStart_1012536 : Nat := 118140960795 + 1012536 * 2 ^ 59
def prefixEnd_1012536 : Nat := 4983230072969 + 3 ^ 40 * 1012536 * 2
def baseEnd_1012536 : Nat := 115537255106879040431875

theorem tailTrace_1012536 : CollatzResearch.WordTrace tailWord_1012536 prefixEnd_1012536 115537255106879040431875 := by
  unfold tailWord_1012536
  simp only [CollatzResearch.WordTrace]
  refine ⟨18465110929881237113228731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24620147906508316150971641 18465110929881237113228731)
  ·
    refine ⟨27697666394821855669843097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18465110929881237113228731 27697666394821855669843097)
    ·
      refine ⟨20773249796116391752382323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27697666394821855669843097 20773249796116391752382323)
      ·
        refine ⟨31159874694174587628573485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20773249796116391752382323 31159874694174587628573485)
        ·
          refine ⟨11684953010315470360715057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31159874694174587628573485 11684953010315470360715057)
          ·
            refine ⟨8763714757736602770536293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11684953010315470360715057 8763714757736602770536293)
            ·
              refine ⟨1643196517075613019475555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8763714757736602770536293 1643196517075613019475555)
              ·
                refine ⟨2464794775613419529213333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643196517075613019475555 2464794775613419529213333)
                ·
                  refine ⟨115537255106879040431875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2464794775613419529213333 115537255106879040431875)
                  ·
                    rfl

theorem cell22_1012536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 6].length) (baseStart_1012536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012536 prefixEnd_1012536 := by exact prefixLift 1012536
  have htrace : WordTrace (prefixWord ++ tailWord_1012536) baseStart_1012536 baseEnd_1012536 := by
    simpa [prefixWord, tailWord_1012536, baseEnd_1012536] using wordTrace_append hprefix tailTrace_1012536
  have hstable : (prefixWord ++ tailWord_1012536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012536).length < 2 ^ (prefixWord ++ tailWord_1012536).sum := by decide
  have hdescent : baseEnd_1012536 < baseStart_1012536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012570 : List Nat := [3, 1, 1, 2, 1, 6, 1, 3, 4]
def baseStart_1012570 : Nat := 118140960795 + 1012570 * 2 ^ 59
def prefixEnd_1012570 : Nat := 4983230072969 + 3 ^ 40 * 1012570 * 2
def baseEnd_1012570 : Nat := 115541134738490788648507

theorem tailTrace_1012570 : CollatzResearch.WordTrace tailWord_1012570 prefixEnd_1012570 115541134738490788648507 := by
  unfold tailWord_1012570
  simp only [CollatzResearch.WordTrace]
  refine ⟨9232865485409824508298791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24620974627759532022130109 9232865485409824508298791)
  ·
    refine ⟨13849298228114736762448187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9232865485409824508298791 13849298228114736762448187)
    ·
      refine ⟨20773947342172105143672281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13849298228114736762448187 20773947342172105143672281)
      ·
        refine ⟨15580460506629078857754211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20773947342172105143672281 15580460506629078857754211)
        ·
          refine ⟨23370690759943618286631317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15580460506629078857754211 23370690759943618286631317)
          ·
            refine ⟨1095501129372357107185843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23370690759943618286631317 1095501129372357107185843)
            ·
              refine ⟨1643251694058535660778765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095501129372357107185843 1643251694058535660778765)
              ·
                refine ⟨616219385271950872792037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1643251694058535660778765 616219385271950872792037)
                ·
                  refine ⟨115541134738490788648507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 616219385271950872792037 115541134738490788648507)
                  ·
                    rfl

theorem cell22_1012570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 4].length) (baseStart_1012570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012570 prefixEnd_1012570 := by exact prefixLift 1012570
  have htrace : WordTrace (prefixWord ++ tailWord_1012570) baseStart_1012570 baseEnd_1012570 := by
    simpa [prefixWord, tailWord_1012570, baseEnd_1012570] using wordTrace_append hprefix tailTrace_1012570
  have hstable : (prefixWord ++ tailWord_1012570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012570).length < 2 ^ (prefixWord ++ tailWord_1012570).sum := by decide
  have hdescent : baseEnd_1012570 < baseStart_1012570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012583 : List Nat := [1, 1, 5, 1, 2, 3, 1, 2, 2, 4]
def baseStart_1012583 : Nat := 118140960795 + 1012583 * 2 ^ 59
def prefixEnd_1012583 : Nat := 4983230072969 + 3 ^ 40 * 1012583 * 2
def baseEnd_1012583 : Nat := 346627854381144665370481

theorem tailTrace_1012583 : CollatzResearch.WordTrace tailWord_1012583 prefixEnd_1012583 346627854381144665370481 := by
  unfold tailWord_1012583
  simp only [CollatzResearch.WordTrace]
  refine ⟨36931936090592201253418403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24621290727061467502278935 36931936090592201253418403)
  ·
    refine ⟨55397904135888301880127605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36931936090592201253418403 55397904135888301880127605)
    ·
      refine ⟨5193553512739528301261963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55397904135888301880127605 5193553512739528301261963)
      ·
        refine ⟨7790330269109292451892945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5193553512739528301261963 7790330269109292451892945)
        ·
          refine ⟨5842747701831969338919709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7790330269109292451892945 5842747701831969338919709)
          ·
            refine ⟨2191030388186988502094891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5842747701831969338919709 2191030388186988502094891)
            ·
              refine ⟨3286545582280482753142337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2191030388186988502094891 3286545582280482753142337)
              ·
                refine ⟨2464909186710362064856753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3286545582280482753142337 2464909186710362064856753)
                ·
                  refine ⟨1848681890032771548642565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2464909186710362064856753 1848681890032771548642565)
                  ·
                    refine ⟨346627854381144665370481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1848681890032771548642565 346627854381144665370481)
                    ·
                      rfl

theorem cell22_1012583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_1012583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012583 prefixEnd_1012583 := by exact prefixLift 1012583
  have htrace : WordTrace (prefixWord ++ tailWord_1012583) baseStart_1012583 baseEnd_1012583 := by
    simpa [prefixWord, tailWord_1012583, baseEnd_1012583] using wordTrace_append hprefix tailTrace_1012583
  have hstable : (prefixWord ++ tailWord_1012583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012583).length < 2 ^ (prefixWord ++ tailWord_1012583).sum := by decide
  have hdescent : baseEnd_1012583 < baseStart_1012583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012598 : List Nat := [5, 1, 1, 3, 1, 1, 1, 9]
def baseStart_1012598 : Nat := 118140960795 + 1012598 * 2 ^ 59
def prefixEnd_1012598 : Nat := 4983230072969 + 3 ^ 40 * 1012598 * 2
def baseEnd_1012598 : Nat := 38514776576409958471715

theorem tailTrace_1012598 : CollatzResearch.WordTrace tailWord_1012598 prefixEnd_1012598 38514776576409958471715 := by
  unfold tailWord_1012598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2308280199096116175950903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24621655457025239210142965 2308280199096116175950903)
  ·
    refine ⟨3462420298644174263926355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2308280199096116175950903 3462420298644174263926355)
    ·
      refine ⟨5193630447966261395889533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3462420298644174263926355 5193630447966261395889533)
      ·
        refine ⟨1947611417987348023458575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5193630447966261395889533 1947611417987348023458575)
        ·
          refine ⟨2921417126981022035187863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1947611417987348023458575 2921417126981022035187863)
          ·
            refine ⟨4382125690471533052781795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2921417126981022035187863 4382125690471533052781795)
            ·
              refine ⟨6573188535707299579172693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4382125690471533052781795 6573188535707299579172693)
              ·
                refine ⟨38514776576409958471715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6573188535707299579172693 38514776576409958471715)
                ·
                  rfl

theorem cell22_1012598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_1012598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012598 prefixEnd_1012598 := by exact prefixLift 1012598
  have htrace : WordTrace (prefixWord ++ tailWord_1012598) baseStart_1012598 baseEnd_1012598 := by
    simpa [prefixWord, tailWord_1012598, baseEnd_1012598] using wordTrace_append hprefix tailTrace_1012598
  have hstable : (prefixWord ++ tailWord_1012598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012598).length < 2 ^ (prefixWord ++ tailWord_1012598).sum := by decide
  have hdescent : baseEnd_1012598 < baseStart_1012598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012731 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 1, 9]
def baseStart_1012731 : Nat := 118140960795 + 1012731 * 2 ^ 59
def prefixEnd_1012731 : Nat := 4983230072969 + 3 ^ 40 * 1012731 * 2
def baseEnd_1012731 : Nat := 346678517805721612670027

theorem tailTrace_1012731 : CollatzResearch.WordTrace tailWord_1012731 prefixEnd_1012731 346678517805721612670027 := by
  unfold tailWord_1012731
  simp only [CollatzResearch.WordTrace]
  refine ⟨36937334094056022529806047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24624889396037348353204031 36937334094056022529806047)
  ·
    refine ⟨55406001141084033794709071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36937334094056022529806047 55406001141084033794709071)
    ·
      refine ⟨83109001711626050692063607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55406001141084033794709071 83109001711626050692063607)
      ·
        refine ⟨124663502567439076038095411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83109001711626050692063607 124663502567439076038095411)
        ·
          refine ⟨186995253851158614057143117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124663502567439076038095411 186995253851158614057143117)
          ·
            refine ⟨70123220194184480271428669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186995253851158614057143117 70123220194184480271428669)
            ·
              refine ⟨26296207572819180101785751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70123220194184480271428669 26296207572819180101785751)
              ·
                refine ⟨39444311359228770152678627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26296207572819180101785751 39444311359228770152678627)
                ·
                  refine ⟨59166467038843155229017941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39444311359228770152678627 59166467038843155229017941)
                  ·
                    refine ⟨346678517805721612670027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 59166467038843155229017941 346678517805721612670027)
                    ·
                      rfl

theorem cell22_1012731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 9].length) (baseStart_1012731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012731 prefixEnd_1012731 := by exact prefixLift 1012731
  have htrace : WordTrace (prefixWord ++ tailWord_1012731) baseStart_1012731 baseEnd_1012731 := by
    simpa [prefixWord, tailWord_1012731, baseEnd_1012731] using wordTrace_append hprefix tailTrace_1012731
  have hstable : (prefixWord ++ tailWord_1012731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012731).length < 2 ^ (prefixWord ++ tailWord_1012731).sum := by decide
  have hdescent : baseEnd_1012731 < baseStart_1012731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012823 : List Nat := [1, 1, 3, 2, 2, 1, 1, 5, 6]
def baseStart_1012823 : Nat := 118140960795 + 1012823 * 2 ^ 59
def prefixEnd_1012823 : Nat := 4983230072969 + 3 ^ 40 * 1012823 * 2
def baseEnd_1012823 : Nat := 115570003761954679789915

theorem tailTrace_1012823 : CollatzResearch.WordTrace tailWord_1012823 prefixEnd_1012823 115570003761954679789915 := by
  unfold tailWord_1012823
  simp only [CollatzResearch.WordTrace]
  refine ⟨36940689609722722242155123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24627126406481814828103415 36940689609722722242155123)
  ·
    refine ⟨55411034414584083363232685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36940689609722722242155123 55411034414584083363232685)
    ·
      refine ⟨20779137905469031261212257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55411034414584083363232685 20779137905469031261212257)
      ·
        refine ⟨15584353429101773445909193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20779137905469031261212257 15584353429101773445909193)
        ·
          refine ⟨11688265071826330084431895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15584353429101773445909193 11688265071826330084431895)
          ·
            refine ⟨17532397607739495126647843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11688265071826330084431895 17532397607739495126647843)
            ·
              refine ⟨26298596411609242689971765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17532397607739495126647843 26298596411609242689971765)
              ·
                refine ⟨2465493413588366502184853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26298596411609242689971765 2465493413588366502184853)
                ·
                  refine ⟨115570003761954679789915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2465493413588366502184853 115570003761954679789915)
                  ·
                    rfl

theorem cell22_1012823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 6].length) (baseStart_1012823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012823 prefixEnd_1012823 := by exact prefixLift 1012823
  have htrace : WordTrace (prefixWord ++ tailWord_1012823) baseStart_1012823 baseEnd_1012823 := by
    simpa [prefixWord, tailWord_1012823, baseEnd_1012823] using wordTrace_append hprefix tailTrace_1012823
  have hstable : (prefixWord ++ tailWord_1012823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012823).length < 2 ^ (prefixWord ++ tailWord_1012823).sum := by decide
  have hdescent : baseEnd_1012823 < baseStart_1012823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012855 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 4, 3]
def baseStart_1012855 : Nat := 118140960795 + 1012855 * 2 ^ 59
def prefixEnd_1012855 : Nat := 4983230072969 + 3 ^ 40 * 1012855 * 2
def baseEnd_1012855 : Nat := 346720965539826622569647

theorem tailTrace_1012855 : CollatzResearch.WordTrace tailWord_1012855 prefixEnd_1012855 346720965539826622569647 := by
  unfold tailWord_1012855
  simp only [CollatzResearch.WordTrace]
  refine ⟨36941856745606791707320019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24627904497071194471546679 36941856745606791707320019)
  ·
    refine ⟨55412785118410187560980029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36941856745606791707320019 55412785118410187560980029)
    ·
      refine ⟨20779794419403820335367511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55412785118410187560980029 20779794419403820335367511)
      ·
        refine ⟨31169691629105730503051267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20779794419403820335367511 31169691629105730503051267)
        ·
          refine ⟨46754537443658595754576901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31169691629105730503051267 46754537443658595754576901)
          ·
            refine ⟨8766475770685986703983169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46754537443658595754576901 8766475770685986703983169)
            ·
              refine ⟨6574856828014490027987377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8766475770685986703983169 6574856828014490027987377)
              ·
                refine ⟨4931142621010867520990533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6574856828014490027987377 4931142621010867520990533)
                ·
                  refine ⟨924589241439537660185725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4931142621010867520990533 924589241439537660185725)
                  ·
                    refine ⟨346720965539826622569647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 924589241439537660185725 346720965539826622569647)
                    ·
                      rfl

theorem cell22_1012855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_1012855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1012855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1012855 prefixEnd_1012855 := by exact prefixLift 1012855
  have htrace : WordTrace (prefixWord ++ tailWord_1012855) baseStart_1012855 baseEnd_1012855 := by
    simpa [prefixWord, tailWord_1012855, baseEnd_1012855] using wordTrace_append hprefix tailTrace_1012855
  have hstable : (prefixWord ++ tailWord_1012855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012855).length < 2 ^ (prefixWord ++ tailWord_1012855).sum := by decide
  have hdescent : baseEnd_1012855 < baseStart_1012855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013020 : List Nat := [2, 2, 3, 1, 1, 1, 2, 10]
def baseStart_1013020 : Nat := 118140960795 + 1013020 * 2 ^ 59
def prefixEnd_1013020 : Nat := 4983230072969 + 3 ^ 40 * 1013020 * 2
def baseEnd_1013020 : Nat := 38530827601313465799349

theorem tailTrace_1013020 : CollatzResearch.WordTrace tailWord_1013020 prefixEnd_1013020 38530827601313465799349 := by
  unfold tailWord_1013020
  simp only [CollatzResearch.WordTrace]
  refine ⟨18473937395004512443538257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24631916526672683258051009 18473937395004512443538257)
  ·
    refine ⟨13855453046253384332653693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18473937395004512443538257 13855453046253384332653693)
    ·
      refine ⟨5195794892345019124745135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13855453046253384332653693 5195794892345019124745135)
      ·
        refine ⟨7793692338517528687117703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5195794892345019124745135 7793692338517528687117703)
        ·
          refine ⟨11690538507776293030676555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7793692338517528687117703 11690538507776293030676555)
          ·
            refine ⟨17535807761664439546014833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11690538507776293030676555 17535807761664439546014833)
            ·
              refine ⟨13151855821248329659511125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17535807761664439546014833 13151855821248329659511125)
              ·
                refine ⟨38530827601313465799349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13151855821248329659511125 38530827601313465799349)
                ·
                  rfl

theorem cell22_1013020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 10].length) (baseStart_1013020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013020 prefixEnd_1013020 := by exact prefixLift 1013020
  have htrace : WordTrace (prefixWord ++ tailWord_1013020) baseStart_1013020 baseEnd_1013020 := by
    simpa [prefixWord, tailWord_1013020, baseEnd_1013020] using wordTrace_append hprefix tailTrace_1013020
  have hstable : (prefixWord ++ tailWord_1013020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013020).length < 2 ^ (prefixWord ++ tailWord_1013020).sum := by decide
  have hdescent : baseEnd_1013020 < baseStart_1013020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013026 : List Nat := [3, 3, 1, 1, 4, 1, 2, 3, 4]
def baseStart_1013026 : Nat := 118140960795 + 1013026 * 2 ^ 59
def prefixEnd_1013026 : Nat := 4983230072969 + 3 ^ 40 * 1013026 * 2
def baseEnd_1013026 : Nat := 115593167444813058848041

theorem tailTrace_1013026 : CollatzResearch.WordTrace tailWord_1013026 prefixEnd_1013026 115593167444813058848041 := by
  unfold tailWord_1013026
  simp only [CollatzResearch.WordTrace]
  refine ⟨9237023406996821977948733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24632062418658191941196621 9237023406996821977948733)
  ·
    refine ⟨3463883777623808241730775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9237023406996821977948733 3463883777623808241730775)
    ·
      refine ⟨5195825666435712362596163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3463883777623808241730775 5195825666435712362596163)
      ·
        refine ⟨7793738499653568543894245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5195825666435712362596163 7793738499653568543894245)
        ·
          refine ⟨1461325968685044101980171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7793738499653568543894245 1461325968685044101980171)
          ·
            refine ⟨2191988953027566152970257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461325968685044101980171 2191988953027566152970257)
            ·
              refine ⟨1643991714770674614727693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2191988953027566152970257 1643991714770674614727693)
              ·
                refine ⟨616496893039002980522885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1643991714770674614727693 616496893039002980522885)
                ·
                  refine ⟨115593167444813058848041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 616496893039002980522885 115593167444813058848041)
                  ·
                    rfl

theorem cell22_1013026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_1013026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013026 prefixEnd_1013026 := by exact prefixLift 1013026
  have htrace : WordTrace (prefixWord ++ tailWord_1013026) baseStart_1013026 baseEnd_1013026 := by
    simpa [prefixWord, tailWord_1013026, baseEnd_1013026] using wordTrace_append hprefix tailTrace_1013026
  have hstable : (prefixWord ++ tailWord_1013026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013026).length < 2 ^ (prefixWord ++ tailWord_1013026).sum := by decide
  have hdescent : baseEnd_1013026 < baseStart_1013026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013041 : List Nat := [1, 2, 2, 3, 3, 3, 1, 2, 2, 3]
def baseStart_1013041 : Nat := 118140960795 + 1013041 * 2 ^ 59
def prefixEnd_1013041 : Nat := 4983230072969 + 3 ^ 40 * 1013041 * 2
def baseEnd_1013041 : Nat := 346784637140984137419077

theorem tailTrace_1013041 : CollatzResearch.WordTrace tailWord_1013041 prefixEnd_1013041 346784637140984137419077 := by
  unfold tailWord_1013041
  simp only [CollatzResearch.WordTrace]
  refine ⟨36948640722932945473590977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24632427148621963649060651 36948640722932945473590977)
  ·
    refine ⟨27711480542199709105193233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36948640722932945473590977 27711480542199709105193233)
    ·
      refine ⟨20783610406649781828894925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27711480542199709105193233 20783610406649781828894925)
      ·
        refine ⟨7793853902493668185835597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20783610406649781828894925 7793853902493668185835597)
        ·
          refine ⟨2922695213435125569688349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7793853902493668185835597 2922695213435125569688349)
          ·
            refine ⟨1096010705038172088633131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2922695213435125569688349 1096010705038172088633131)
            ·
              refine ⟨1644016057557258132949697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096010705038172088633131 1644016057557258132949697)
              ·
                refine ⟨1233012043167943599712273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1644016057557258132949697 1233012043167943599712273)
                ·
                  refine ⟨924759032375957699784205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1233012043167943599712273 924759032375957699784205)
                  ·
                    refine ⟨346784637140984137419077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 924759032375957699784205 346784637140984137419077)
                    ·
                      rfl

theorem cell22_1013041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_1013041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013041 prefixEnd_1013041 := by exact prefixLift 1013041
  have htrace : WordTrace (prefixWord ++ tailWord_1013041) baseStart_1013041 baseEnd_1013041 := by
    simpa [prefixWord, tailWord_1013041, baseEnd_1013041] using wordTrace_append hprefix tailTrace_1013041
  have hstable : (prefixWord ++ tailWord_1013041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013041).length < 2 ^ (prefixWord ++ tailWord_1013041).sum := by decide
  have hdescent : baseEnd_1013041 < baseStart_1013041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
