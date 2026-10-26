import V185TrunkScan22Chunk380

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3397265 : List Nat := [1, 2, 2, 1, 1, 1, 1, 7, 3, 3]
def baseStart_3397265 : Nat := 118140960795 + 3397265 * 2 ^ 59
def prefixEnd_3397265 : Nat := 4983230072969 + 3 ^ 40 * 3397265 * 2
def baseEnd_3397265 : Nat := 1162953237131170612509179

theorem tailTrace_3397265 : CollatzResearch.WordTrace tailWord_3397265 prefixEnd_3397265 1162953237131170612509179 := by
  unfold tailWord_3397265
  simp only [CollatzResearch.WordTrace]
  refine ⟨123908434037296586514497249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82605622691531057676331499 123908434037296586514497249)
  ·
    refine ⟨92931325527972439885872937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123908434037296586514497249 92931325527972439885872937)
    ·
      refine ⟨69698494145979329914404703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92931325527972439885872937 69698494145979329914404703)
      ·
        refine ⟨104547741218968994871607055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69698494145979329914404703 104547741218968994871607055)
        ·
          refine ⟨156821611828453492307410583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104547741218968994871607055 156821611828453492307410583)
          ·
            refine ⟨235232417742680238461115875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156821611828453492307410583 235232417742680238461115875)
            ·
              refine ⟨352848626614020357691673813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235232417742680238461115875 352848626614020357691673813)
              ·
                refine ⟨8269889686266102133398605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 352848626614020357691673813 8269889686266102133398605)
                ·
                  refine ⟨3101208632349788300024477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8269889686266102133398605 3101208632349788300024477)
                  ·
                    refine ⟨1162953237131170612509179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3101208632349788300024477 1162953237131170612509179)
                    ·
                      rfl

theorem cell22_3397265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_3397265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397265 prefixEnd_3397265 := by exact prefixLift 3397265
  have htrace : WordTrace (prefixWord ++ tailWord_3397265) baseStart_3397265 baseEnd_3397265 := by
    simpa [prefixWord, tailWord_3397265, baseEnd_3397265] using wordTrace_append hprefix tailTrace_3397265
  have hstable : (prefixWord ++ tailWord_3397265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397265).length < 2 ^ (prefixWord ++ tailWord_3397265).sum := by decide
  have hdescent : baseEnd_3397265 < baseStart_3397265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397323 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 10]
def baseStart_3397323 : Nat := 118140960795 + 3397323 * 2 ^ 59
def prefixEnd_3397323 : Nat := 4983230072969 + 3 ^ 40 * 3397323 * 2
def baseEnd_3397323 : Nat := 387657697238825931519667

theorem tailTrace_3397323 : CollatzResearch.WordTrace tailWord_3397323 prefixEnd_3397323 387657697238825931519667 := by
  unfold tailWord_3397323
  simp only [CollatzResearch.WordTrace]
  refine ⟨123910549471086462420108623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82607032980724308280072415 123910549471086462420108623)
  ·
    refine ⟨185865824206629693630162935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123910549471086462420108623 185865824206629693630162935)
    ·
      refine ⟨278798736309944540445244403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185865824206629693630162935 278798736309944540445244403)
      ·
        refine ⟨418198104464916810667866605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278798736309944540445244403 418198104464916810667866605)
        ·
          refine ⟨156824289174343804000449977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418198104464916810667866605 156824289174343804000449977)
          ·
            refine ⟨117618216880757853000337483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156824289174343804000449977 117618216880757853000337483)
            ·
              refine ⟨176427325321136779500506225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117618216880757853000337483 176427325321136779500506225)
              ·
                refine ⟨132320493990852584625379669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176427325321136779500506225 132320493990852584625379669)
                ·
                  refine ⟨387657697238825931519667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 132320493990852584625379669 387657697238825931519667)
                  ·
                    rfl

theorem cell22_3397323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 10].length) (baseStart_3397323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397323 prefixEnd_3397323 := by exact prefixLift 3397323
  have htrace : WordTrace (prefixWord ++ tailWord_3397323) baseStart_3397323 baseEnd_3397323 := by
    simpa [prefixWord, tailWord_3397323, baseEnd_3397323] using wordTrace_append hprefix tailTrace_3397323
  have hstable : (prefixWord ++ tailWord_3397323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397323).length < 2 ^ (prefixWord ++ tailWord_3397323).sum := by decide
  have hdescent : baseEnd_3397323 < baseStart_3397323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397355 : List Nat := [1, 1, 1, 1, 2, 4, 4, 2, 1, 5]
def baseStart_3397355 : Nat := 118140960795 + 3397355 * 2 ^ 59
def prefixEnd_3397355 : Nat := 4983230072969 + 3 ^ 40 * 3397355 * 2
def baseEnd_3397355 : Nat := 1162984045970440377758903

theorem tailTrace_3397355 : CollatzResearch.WordTrace tailWord_3397355 prefixEnd_3397355 1162984045970440377758903 := by
  unfold tailWord_3397355
  simp only [CollatzResearch.WordTrace]
  refine ⟨123911716606970531885273519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82607811071313687923515679 123911716606970531885273519)
  ·
    refine ⟨185867574910455797827910279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123911716606970531885273519 185867574910455797827910279)
    ·
      refine ⟨278801362365683696741865419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185867574910455797827910279 278801362365683696741865419)
      ·
        refine ⟨418202043548525545112798129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278801362365683696741865419 418202043548525545112798129)
        ·
          refine ⟨313651532661394158834598597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418202043548525545112798129 313651532661394158834598597)
          ·
            refine ⟨58809662374011404781487237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 313651532661394158834598597 58809662374011404781487237)
            ·
              refine ⟨11026811695127138396528857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58809662374011404781487237 11026811695127138396528857)
              ·
                refine ⟨8270108771345353797396643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11026811695127138396528857 8270108771345353797396643)
                ·
                  refine ⟨12405163157018030696094965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8270108771345353797396643 12405163157018030696094965)
                  ·
                    refine ⟨1162984045970440377758903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12405163157018030696094965 1162984045970440377758903)
                    ·
                      rfl

theorem cell22_3397355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 5].length) (baseStart_3397355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397355 prefixEnd_3397355 := by exact prefixLift 3397355
  have htrace : WordTrace (prefixWord ++ tailWord_3397355) baseStart_3397355 baseEnd_3397355 := by
    simpa [prefixWord, tailWord_3397355, baseEnd_3397355] using wordTrace_append hprefix tailTrace_3397355
  have hstable : (prefixWord ++ tailWord_3397355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397355).length < 2 ^ (prefixWord ++ tailWord_3397355).sum := by decide
  have hdescent : baseEnd_3397355 < baseStart_3397355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397370 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 4, 4]
def baseStart_3397370 : Nat := 118140960795 + 3397370 * 2 ^ 59
def prefixEnd_3397370 : Nat := 4983230072969 + 3 ^ 40 * 3397370 * 2
def baseEnd_3397370 : Nat := 1162989180776985338633857

theorem tailTrace_3397370 : CollatzResearch.WordTrace tailWord_3397370 prefixEnd_3397370 1162989180776985338633857 := by
  unfold tailWord_3397370
  simp only [CollatzResearch.WordTrace]
  refine ⟨30978065925479047361767391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82608175801277459631379709 30978065925479047361767391)
  ·
    refine ⟨46467098888218571042651087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30978065925479047361767391 46467098888218571042651087)
    ·
      refine ⟨69700648332327856563976631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46467098888218571042651087 69700648332327856563976631)
      ·
        refine ⟨104550972498491784845964947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69700648332327856563976631 104550972498491784845964947)
        ·
          refine ⟨156826458747737677268947421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104550972498491784845964947 156826458747737677268947421)
          ·
            refine ⟨58809922030401628975855283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156826458747737677268947421 58809922030401628975855283)
            ·
              refine ⟨88214883045602443463782925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58809922030401628975855283 88214883045602443463782925)
              ·
                refine ⟨33080581142100916298918597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88214883045602443463782925 33080581142100916298918597)
                ·
                  refine ⟨6202608964143921806047237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33080581142100916298918597 6202608964143921806047237)
                  ·
                    refine ⟨1162989180776985338633857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6202608964143921806047237 1162989180776985338633857)
                    ·
                      rfl

theorem cell22_3397370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_3397370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397370 prefixEnd_3397370 := by exact prefixLift 3397370
  have htrace : WordTrace (prefixWord ++ tailWord_3397370) baseStart_3397370 baseEnd_3397370 := by
    simpa [prefixWord, tailWord_3397370, baseEnd_3397370] using wordTrace_append hprefix tailTrace_3397370
  have hstable : (prefixWord ++ tailWord_3397370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397370).length < 2 ^ (prefixWord ++ tailWord_3397370).sum := by decide
  have hdescent : baseEnd_3397370 < baseStart_3397370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397372 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 4, 3]
def baseStart_3397372 : Nat := 118140960795 + 3397372 * 2 ^ 59
def prefixEnd_3397372 : Nat := 4983230072969 + 3 ^ 40 * 3397372 * 2
def baseEnd_3397372 : Nat := 1162989865417858000083851

theorem tailTrace_3397372 : CollatzResearch.WordTrace tailWord_3397372 prefixEnd_3397372 1162989865417858000083851 := by
  unfold tailWord_3397372
  simp only [CollatzResearch.WordTrace]
  refine ⟨61956168323954471894321185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82608224431939295859094913 61956168323954471894321185)
  ·
    refine ⟨46467126242965853920740889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61956168323954471894321185 46467126242965853920740889)
    ·
      refine ⟨34850344682224390440555667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46467126242965853920740889 34850344682224390440555667)
      ·
        refine ⟨52275517023336585660833501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34850344682224390440555667 52275517023336585660833501)
        ·
          refine ⟨19603318883751219622812563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52275517023336585660833501 19603318883751219622812563)
          ·
            refine ⟨29404978325626829434218845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19603318883751219622812563 29404978325626829434218845)
            ·
              refine ⟨11026866872110061037832067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29404978325626829434218845 11026866872110061037832067)
              ·
                refine ⟨16540300308165091556748101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11026866872110061037832067 16540300308165091556748101)
                ·
                  refine ⟨3101306307780954666890269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16540300308165091556748101 3101306307780954666890269)
                  ·
                    refine ⟨1162989865417858000083851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3101306307780954666890269 1162989865417858000083851)
                    ·
                      rfl

theorem cell22_3397372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_3397372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397372 prefixEnd_3397372 := by exact prefixLift 3397372
  have htrace : WordTrace (prefixWord ++ tailWord_3397372) baseStart_3397372 baseEnd_3397372 := by
    simpa [prefixWord, tailWord_3397372, baseEnd_3397372] using wordTrace_append hprefix tailTrace_3397372
  have hstable : (prefixWord ++ tailWord_3397372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397372).length < 2 ^ (prefixWord ++ tailWord_3397372).sum := by decide
  have hdescent : baseEnd_3397372 < baseStart_3397372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397374 : List Nat := [4, 2, 2, 1, 3, 1, 2, 1, 6]
def baseStart_3397374 : Nat := 118140960795 + 3397374 * 2 ^ 59
def prefixEnd_3397374 : Nat := 4983230072969 + 3 ^ 40 * 3397374 * 2
def baseEnd_3397374 : Nat := 387663516686243553844615

theorem tailTrace_3397374 : CollatzResearch.WordTrace tailWord_3397374 prefixEnd_3397374 387663516686243553844615 := by
  unfold tailWord_3397374
  simp only [CollatzResearch.WordTrace]
  refine ⟨15489051199237712266276897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82608273062601132086810117 15489051199237712266276897)
  ·
    refine ⟨11616788399428284199707673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15489051199237712266276897 11616788399428284199707673)
    ·
      refine ⟨8712591299571213149780755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11616788399428284199707673 8712591299571213149780755)
      ·
        refine ⟨13068886949356819724671133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8712591299571213149780755 13068886949356819724671133)
        ·
          refine ⟨4900832606008807396751675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13068886949356819724671133 4900832606008807396751675)
          ·
            refine ⟨7351248909013211095127513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4900832606008807396751675 7351248909013211095127513)
            ·
              refine ⟨5513436681759908321345635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7351248909013211095127513 5513436681759908321345635)
              ·
                refine ⟨8270155022639862482018453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5513436681759908321345635 8270155022639862482018453)
                ·
                  refine ⟨387663516686243553844615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8270155022639862482018453 387663516686243553844615)
                  ·
                    rfl

theorem cell22_3397374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_3397374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397374 prefixEnd_3397374 := by exact prefixLift 3397374
  have htrace : WordTrace (prefixWord ++ tailWord_3397374) baseStart_3397374 baseEnd_3397374 := by
    simpa [prefixWord, tailWord_3397374, baseEnd_3397374] using wordTrace_append hprefix tailTrace_3397374
  have hstable : (prefixWord ++ tailWord_3397374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397374).length < 2 ^ (prefixWord ++ tailWord_3397374).sum := by decide
  have hdescent : baseEnd_3397374 < baseStart_3397374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397402 : List Nat := [3, 1, 1, 3, 2, 2, 4, 6]
def baseStart_3397402 : Nat := 118140960795 + 3397402 * 2 ^ 59
def prefixEnd_3397402 : Nat := 4983230072969 + 3 ^ 40 * 3397402 * 2
def baseEnd_3397402 : Nat := 129222237225660880203751

theorem tailTrace_3397402 : CollatzResearch.WordTrace tailWord_3397402 prefixEnd_3397402 129222237225660880203751 := by
  unfold tailWord_3397402
  simp only [CollatzResearch.WordTrace]
  refine ⟨30978357709450064728058615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82608953891866839274822973 30978357709450064728058615)
  ·
    refine ⟨46467536564175097092087923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30978357709450064728058615 46467536564175097092087923)
    ·
      refine ⟨69701304846262645638131885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46467536564175097092087923 69701304846262645638131885)
      ·
        refine ⟨26137989317348492114299457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69701304846262645638131885 26137989317348492114299457)
        ·
          refine ⟨19603491988011369085724593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26137989317348492114299457 19603491988011369085724593)
          ·
            refine ⟨14702618991008526814293445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19603491988011369085724593 14702618991008526814293445)
            ·
              refine ⟨2756741060814098777680021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14702618991008526814293445 2756741060814098777680021)
              ·
                refine ⟨129222237225660880203751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2756741060814098777680021 129222237225660880203751)
                ·
                  rfl

theorem cell22_3397402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 6].length) (baseStart_3397402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397402 prefixEnd_3397402 := by exact prefixLift 3397402
  have htrace : WordTrace (prefixWord ++ tailWord_3397402) baseStart_3397402 baseEnd_3397402 := by
    simpa [prefixWord, tailWord_3397402, baseEnd_3397402] using wordTrace_append hprefix tailTrace_3397402
  have hstable : (prefixWord ++ tailWord_3397402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397402).length < 2 ^ (prefixWord ++ tailWord_3397402).sum := by decide
  have hdescent : baseEnd_3397402 < baseStart_3397402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397434 : List Nat := [3, 1, 1, 1, 5, 1, 3, 1, 3, 3]
def baseStart_3397434 : Nat := 118140960795 + 3397434 * 2 ^ 59
def prefixEnd_3397434 : Nat := 4983230072969 + 3 ^ 40 * 3397434 * 2
def baseEnd_3397434 : Nat := 1163011089284910505033661

theorem tailTrace_3397434 : CollatzResearch.WordTrace tailWord_3397434 prefixEnd_3397434 1163011089284910505033661 := by
  unfold tailWord_3397434
  simp only [CollatzResearch.WordTrace]
  refine ⟨30978649493421082094349839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82609731982456218918266237 30978649493421082094349839)
  ·
    refine ⟨46467974240131623141524759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30978649493421082094349839 46467974240131623141524759)
    ·
      refine ⟨69701961360197434712287139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46467974240131623141524759 69701961360197434712287139)
      ·
        refine ⟨104552942040296152068430709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69701961360197434712287139 104552942040296152068430709)
        ·
          refine ⟨9801838316277764256415379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104552942040296152068430709 9801838316277764256415379)
          ·
            refine ⟨14702757474416646384623069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9801838316277764256415379 14702757474416646384623069)
            ·
              refine ⟨5513534052906242394233651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14702757474416646384623069 5513534052906242394233651)
              ·
                refine ⟨8270301079359363591350477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5513534052906242394233651 8270301079359363591350477)
                ·
                  refine ⟨3101362904759761346756429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8270301079359363591350477 3101362904759761346756429)
                  ·
                    refine ⟨1163011089284910505033661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3101362904759761346756429 1163011089284910505033661)
                    ·
                      rfl

theorem cell22_3397434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_3397434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397434 prefixEnd_3397434 := by exact prefixLift 3397434
  have htrace : WordTrace (prefixWord ++ tailWord_3397434) baseStart_3397434 baseEnd_3397434 := by
    simpa [prefixWord, tailWord_3397434, baseEnd_3397434] using wordTrace_append hprefix tailTrace_3397434
  have hstable : (prefixWord ++ tailWord_3397434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397434).length < 2 ^ (prefixWord ++ tailWord_3397434).sum := by decide
  have hdescent : baseEnd_3397434 < baseStart_3397434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397445 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 1, 7]
def baseStart_3397445 : Nat := 118140960795 + 3397445 * 2 ^ 59
def prefixEnd_3397445 : Nat := 4983230072969 + 3 ^ 40 * 3397445 * 2
def baseEnd_3397445 : Nat := 1163014854809710143008627

theorem tailTrace_3397445 : CollatzResearch.WordTrace tailWord_3397445 prefixEnd_3397445 1163014854809710143008627 := by
  unfold tailWord_3397445
  simp only [CollatzResearch.WordTrace]
  refine ⟨123914999176644477256049789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82609999451096318170699859 123914999176644477256049789)
  ·
    refine ⟨46468124691241678971018671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123914999176644477256049789 46468124691241678971018671)
    ·
      refine ⟨69702187036862518456528007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46468124691241678971018671 69702187036862518456528007)
      ·
        refine ⟨104553280555293777684792011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69702187036862518456528007 104553280555293777684792011)
        ·
          refine ⟨156829920832940666527188017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104553280555293777684792011 156829920832940666527188017)
          ·
            refine ⟨117622440624705499895391013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156829920832940666527188017 117622440624705499895391013)
            ·
              refine ⟨22054207617132281230385815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117622440624705499895391013 22054207617132281230385815)
              ·
                refine ⟨33081311425698421845578723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22054207617132281230385815 33081311425698421845578723)
                ·
                  refine ⟨49621967138547632768368085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33081311425698421845578723 49621967138547632768368085)
                  ·
                    refine ⟨1163014854809710143008627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49621967138547632768368085 1163014854809710143008627)
                    ·
                      rfl

theorem cell22_3397445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_3397445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397445 prefixEnd_3397445 := by exact prefixLift 3397445
  have htrace : WordTrace (prefixWord ++ tailWord_3397445) baseStart_3397445 baseEnd_3397445 := by
    simpa [prefixWord, tailWord_3397445, baseEnd_3397445] using wordTrace_append hprefix tailTrace_3397445
  have hstable : (prefixWord ++ tailWord_3397445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397445).length < 2 ^ (prefixWord ++ tailWord_3397445).sum := by decide
  have hdescent : baseEnd_3397445 < baseStart_3397445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397507 : List Nat := [1, 1, 1, 3, 4, 2, 1, 3, 1, 5]
def baseStart_3397507 : Nat := 118140960795 + 3397507 * 2 ^ 59
def prefixEnd_3397507 : Nat := 4983230072969 + 3 ^ 40 * 3397507 * 2
def baseEnd_3397507 : Nat := 1163036078676762647958437

theorem tailTrace_3397507 : CollatzResearch.WordTrace tailWord_3397507 prefixEnd_3397507 1163036078676762647958437 := by
  unfold tailWord_3397507
  simp only [CollatzResearch.WordTrace]
  refine ⟨123917260502419861844806775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82611507001613241229871183 123917260502419861844806775)
  ·
    refine ⟨185875890753629792767210163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123917260502419861844806775 185875890753629792767210163)
    ·
      refine ⟨278813836130444689150815245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185875890753629792767210163 278813836130444689150815245)
      ·
        refine ⟨104555188548916758431555717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278813836130444689150815245 104555188548916758431555717)
        ·
          refine ⟨19604097852921892205916697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104555188548916758431555717 19604097852921892205916697)
          ·
            refine ⟨14703073389691419154437523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19604097852921892205916697 14703073389691419154437523)
            ·
              refine ⟨22054610084537128731656285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14703073389691419154437523 22054610084537128731656285)
              ·
                refine ⟨8270478781701423274371107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22054610084537128731656285 8270478781701423274371107)
                ·
                  refine ⟨12405718172552134911556661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8270478781701423274371107 12405718172552134911556661)
                  ·
                    refine ⟨1163036078676762647958437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12405718172552134911556661 1163036078676762647958437)
                    ·
                      rfl

theorem cell22_3397507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 5].length) (baseStart_3397507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397507 prefixEnd_3397507 := by exact prefixLift 3397507
  have htrace : WordTrace (prefixWord ++ tailWord_3397507) baseStart_3397507 baseEnd_3397507 := by
    simpa [prefixWord, tailWord_3397507, baseEnd_3397507] using wordTrace_append hprefix tailTrace_3397507
  have hstable : (prefixWord ++ tailWord_3397507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397507).length < 2 ^ (prefixWord ++ tailWord_3397507).sum := by decide
  have hdescent : baseEnd_3397507 < baseStart_3397507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397524 : List Nat := [2, 4, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_3397524 : Nat := 118140960795 + 3397524 * 2 ^ 59
def prefixEnd_3397524 : Nat := 4983230072969 + 3 ^ 40 * 3397524 * 2
def baseEnd_3397524 : Nat := 1163041898124180270283385

theorem tailTrace_3397524 : CollatzResearch.WordTrace tailWord_3397524 prefixEnd_3397524 1163041898124180270283385 := by
  unfold tailWord_3397524
  simp only [CollatzResearch.WordTrace]
  refine ⟨61958940271679136874087813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82611920362238849165450417 61958940271679136874087813)
  ·
    refine ⟨11617301300939838163891465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61958940271679136874087813 11617301300939838163891465)
    ·
      refine ⟨8712975975704878622918599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11617301300939838163891465 8712975975704878622918599)
      ·
        refine ⟨13069463963557317934377899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8712975975704878622918599 13069463963557317934377899)
        ·
          refine ⟨19604195945335976901566849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13069463963557317934377899 19604195945335976901566849)
          ·
            refine ⟨14703146959001982676175137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19604195945335976901566849 14703146959001982676175137)
            ·
              refine ⟨11027360219251487007131353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14703146959001982676175137 11027360219251487007131353)
              ·
                refine ⟨8270520164438615255348515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11027360219251487007131353 8270520164438615255348515)
                ·
                  refine ⟨12405780246657922883022773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8270520164438615255348515 12405780246657922883022773)
                  ·
                    refine ⟨1163041898124180270283385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12405780246657922883022773 1163041898124180270283385)
                    ·
                      rfl

theorem cell22_3397524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_3397524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397524 prefixEnd_3397524 := by exact prefixLift 3397524
  have htrace : WordTrace (prefixWord ++ tailWord_3397524) baseStart_3397524 baseEnd_3397524 := by
    simpa [prefixWord, tailWord_3397524, baseEnd_3397524] using wordTrace_append hprefix tailTrace_3397524
  have hstable : (prefixWord ++ tailWord_3397524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397524).length < 2 ^ (prefixWord ++ tailWord_3397524).sum := by decide
  have hdescent : baseEnd_3397524 < baseStart_3397524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397582 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 9]
def baseStart_3397582 : Nat := 118140960795 + 3397582 * 2 ^ 59
def prefixEnd_3397582 : Nat := 4983230072969 + 3 ^ 40 * 3397582 * 2
def baseEnd_3397582 : Nat := 387687250903162484111069

theorem tailTrace_3397582 : CollatzResearch.WordTrace tailWord_3397582 prefixEnd_3397582 387687250903162484111069 := by
  unfold tailWord_3397582
  simp only [CollatzResearch.WordTrace]
  refine ⟨15489999497143518706723375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82613330651432099769191333 15489999497143518706723375)
  ·
    refine ⟨23234999245715278060085063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15489999497143518706723375 23234999245715278060085063)
    ·
      refine ⟨34852498868572917090127595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23234999245715278060085063 34852498868572917090127595)
      ·
        refine ⟨52278748302859375635191393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34852498868572917090127595 52278748302859375635191393)
        ·
          refine ⟨39209061227144531726393545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52278748302859375635191393 39209061227144531726393545)
          ·
            refine ⟨29406795920358398794795159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39209061227144531726393545 29406795920358398794795159)
            ·
              refine ⟨44110193880537598192192739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29406795920358398794795159 44110193880537598192192739)
              ·
                refine ⟨66165290820806397288289109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44110193880537598192192739 66165290820806397288289109)
                ·
                  refine ⟨387687250903162484111069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66165290820806397288289109 387687250903162484111069)
                  ·
                    rfl

theorem cell22_3397582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_3397582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397582 prefixEnd_3397582 := by exact prefixLift 3397582
  have htrace : WordTrace (prefixWord ++ tailWord_3397582) baseStart_3397582 baseEnd_3397582 := by
    simpa [prefixWord, tailWord_3397582, baseEnd_3397582] using wordTrace_append hprefix tailTrace_3397582
  have hstable : (prefixWord ++ tailWord_3397582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397582).length < 2 ^ (prefixWord ++ tailWord_3397582).sum := by decide
  have hdescent : baseEnd_3397582 < baseStart_3397582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397627 : List Nat := [1, 1, 1, 1, 1, 3, 4, 4, 6]
def baseStart_3397627 : Nat := 118140960795 + 3397627 * 2 ^ 59
def prefixEnd_3397627 : Nat := 4983230072969 + 3 ^ 40 * 3397627 * 2
def baseEnd_3397627 : Nat := 387692385709707444986023

theorem tailTrace_3397627 : CollatzResearch.WordTrace tailWord_3397627 prefixEnd_3397627 387692385709707444986023 := by
  unfold tailWord_3397627
  simp only [CollatzResearch.WordTrace]
  refine ⟨123921637261985122339175135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82614424841323414892783423 123921637261985122339175135)
  ·
    refine ⟨185882455892977683508762703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123921637261985122339175135 185882455892977683508762703)
    ·
      refine ⟨278823683839466525263144055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185882455892977683508762703 278823683839466525263144055)
      ·
        refine ⟨418235525759199787894716083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278823683839466525263144055 418235525759199787894716083)
        ·
          refine ⟨627353288638799681842074125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418235525759199787894716083 627353288638799681842074125)
          ·
            refine ⟨235257483239549880690777797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 627353288638799681842074125 235257483239549880690777797)
            ·
              refine ⟨44110778107415602629520837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 235257483239549880690777797 44110778107415602629520837)
              ·
                refine ⟨8270770895140425493035157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44110778107415602629520837 8270770895140425493035157)
                ·
                  refine ⟨387692385709707444986023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8270770895140425493035157 387692385709707444986023)
                  ·
                    rfl

theorem cell22_3397627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 6].length) (baseStart_3397627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397627 prefixEnd_3397627 := by exact prefixLift 3397627
  have htrace : WordTrace (prefixWord ++ tailWord_3397627) baseStart_3397627 baseEnd_3397627 := by
    simpa [prefixWord, tailWord_3397627, baseEnd_3397627] using wordTrace_append hprefix tailTrace_3397627
  have hstable : (prefixWord ++ tailWord_3397627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397627).length < 2 ^ (prefixWord ++ tailWord_3397627).sum := by decide
  have hdescent : baseEnd_3397627 < baseStart_3397627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397657 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 3, 6]
def baseStart_3397657 : Nat := 118140960795 + 3397657 * 2 ^ 59
def prefixEnd_3397657 : Nat := 4983230072969 + 3 ^ 40 * 3397657 * 2
def baseEnd_3397657 : Nat := 1163087426742212256707977

theorem tailTrace_3397657 : CollatzResearch.WordTrace tailWord_3397657 prefixEnd_3397657 1163087426742212256707977 := by
  unfold tailWord_3397657
  simp only [CollatzResearch.WordTrace]
  refine ⟨123922731451876437462767225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82615154301250958308511483 123922731451876437462767225)
  ·
    refine ⟨92942048588907328097075419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123922731451876437462767225 92942048588907328097075419)
    ·
      refine ⟨139413072883360992145613129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92942048588907328097075419 139413072883360992145613129)
      ·
        refine ⟨104559804662520744109209847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139413072883360992145613129 104559804662520744109209847)
        ·
          refine ⟨156839706993781116163814771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104559804662520744109209847 156839706993781116163814771)
          ·
            refine ⟨235259560490671674245722157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156839706993781116163814771 235259560490671674245722157)
            ·
              refine ⟨88222335184001877842145809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235259560490671674245722157 88222335184001877842145809)
              ·
                refine ⟨66166751388001408381609357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88222335184001877842145809 66166751388001408381609357)
                ·
                  refine ⟨24812531770500528143103509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66166751388001408381609357 24812531770500528143103509)
                  ·
                    refine ⟨1163087426742212256707977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24812531770500528143103509 1163087426742212256707977)
                    ·
                      rfl

theorem cell22_3397657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_3397657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397657 prefixEnd_3397657 := by exact prefixLift 3397657
  have htrace : WordTrace (prefixWord ++ tailWord_3397657) baseStart_3397657 baseEnd_3397657 := by
    simpa [prefixWord, tailWord_3397657, baseEnd_3397657] using wordTrace_append hprefix tailTrace_3397657
  have hstable : (prefixWord ++ tailWord_3397657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397657).length < 2 ^ (prefixWord ++ tailWord_3397657).sum := by decide
  have hdescent : baseEnd_3397657 < baseStart_3397657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397721 : List Nat := [1, 2, 1, 2, 2, 1, 6, 1, 3, 3]
def baseStart_3397721 : Nat := 118140960795 + 3397721 * 2 ^ 59
def prefixEnd_3397721 : Nat := 4983230072969 + 3 ^ 40 * 3397721 * 2
def baseEnd_3397721 : Nat := 1163109335250137423107781

theorem tailTrace_3397721 : CollatzResearch.WordTrace tailWord_3397721 prefixEnd_3397721 1163109335250137423107781 := by
  unfold tailWord_3397721
  simp only [CollatzResearch.WordTrace]
  refine ⟨123925065723644576393097017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82616710482429717595398011 123925065723644576393097017)
  ·
    refine ⟨92943799292733432294822763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123925065723644576393097017 92943799292733432294822763)
    ·
      refine ⟨139415698939100148442234145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92943799292733432294822763 139415698939100148442234145)
      ·
        refine ⟨104561774204325111331675609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139415698939100148442234145 104561774204325111331675609)
        ·
          refine ⟨78421330653243833498756707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104561774204325111331675609 78421330653243833498756707)
          ·
            refine ⟨117631995979865750248135061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78421330653243833498756707 117631995979865750248135061)
            ·
              refine ⟨5513999811556207042881331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117631995979865750248135061 5513999811556207042881331)
              ·
                refine ⟨8270999717334310564321997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5513999811556207042881331 8270999717334310564321997)
                ·
                  refine ⟨3101624894000366461620749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8270999717334310564321997 3101624894000366461620749)
                  ·
                    refine ⟨1163109335250137423107781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3101624894000366461620749 1163109335250137423107781)
                    ·
                      rfl

theorem cell22_3397721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 3].length) (baseStart_3397721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397721 prefixEnd_3397721 := by exact prefixLift 3397721
  have htrace : WordTrace (prefixWord ++ tailWord_3397721) baseStart_3397721 baseEnd_3397721 := by
    simpa [prefixWord, tailWord_3397721, baseEnd_3397721] using wordTrace_append hprefix tailTrace_3397721
  have hstable : (prefixWord ++ tailWord_3397721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397721).length < 2 ^ (prefixWord ++ tailWord_3397721).sum := by decide
  have hdescent : baseEnd_3397721 < baseStart_3397721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397824 : List Nat := [2, 1, 1, 2, 5, 11]
def baseStart_3397824 : Nat := 118140960795 + 3397824 * 2 ^ 59
def prefixEnd_3397824 : Nat := 4983230072969 + 3 ^ 40 * 3397824 * 2
def baseEnd_3397824 : Nat := 14359809805618265281265

theorem tailTrace_3397824 : CollatzResearch.WordTrace tailWord_3397824 prefixEnd_3397824 14359809805618265281265 := by
  unfold tailWord_3397824
  simp only [CollatzResearch.WordTrace]
  refine ⟨61964411221135712492048263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82619214961514283322731017 61964411221135712492048263)
  ·
    refine ⟨92946616831703568738072395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61964411221135712492048263 92946616831703568738072395)
    ·
      refine ⟨139419925247555353107108593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92946616831703568738072395 139419925247555353107108593)
      ·
        refine ⟨104564943935666514830331445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139419925247555353107108593 104564943935666514830331445)
        ·
          refine ⟨9802963493968735765343573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104564943935666514830331445 9802963493968735765343573)
          ·
            refine ⟨14359809805618265281265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9802963493968735765343573 14359809805618265281265)
            ·
              rfl

theorem cell22_3397824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 11].length) (baseStart_3397824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397824 prefixEnd_3397824 := by exact prefixLift 3397824
  have htrace : WordTrace (prefixWord ++ tailWord_3397824) baseStart_3397824 baseEnd_3397824 := by
    simpa [prefixWord, tailWord_3397824, baseEnd_3397824] using wordTrace_append hprefix tailTrace_3397824
  have hstable : (prefixWord ++ tailWord_3397824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397824).length < 2 ^ (prefixWord ++ tailWord_3397824).sum := by decide
  have hdescent : baseEnd_3397824 < baseStart_3397824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397890 : List Nat := [3, 4, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_3397890 : Nat := 118140960795 + 3397890 * 2 ^ 59
def prefixEnd_3397890 : Nat := 4983230072969 + 3 ^ 40 * 3397890 * 2
def baseEnd_3397890 : Nat := 1163167187403877315632263

theorem tailTrace_3397890 : CollatzResearch.WordTrace tailWord_3397890 prefixEnd_3397890 1163167187403877315632263 := by
  unfold tailWord_3397890
  simp only [CollatzResearch.WordTrace]
  refine ⟨30982807415008079563999781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82620819773354878837332749 30982807415008079563999781)
  ·
    refine ⟨5809276390314014918249959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30982807415008079563999781 5809276390314014918249959)
    ·
      refine ⟨8713914585471022377374939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5809276390314014918249959 8713914585471022377374939)
      ·
        refine ⟨13070871878206533566062409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8713914585471022377374939 13070871878206533566062409)
        ·
          refine ⟨9803153908654900174546807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13070871878206533566062409 9803153908654900174546807)
          ·
            refine ⟨14704730862982350261820211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9803153908654900174546807 14704730862982350261820211)
            ·
              refine ⟨22057096294473525392730317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14704730862982350261820211 22057096294473525392730317)
              ·
                refine ⟨8271411110427572022273869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22057096294473525392730317 8271411110427572022273869)
                ·
                  refine ⟨3101779166410339508352701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8271411110427572022273869 3101779166410339508352701)
                  ·
                    refine ⟨1163167187403877315632263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3101779166410339508352701 1163167187403877315632263)
                    ·
                      rfl

theorem cell22_3397890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_3397890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397890 prefixEnd_3397890 := by exact prefixLift 3397890
  have htrace : WordTrace (prefixWord ++ tailWord_3397890) baseStart_3397890 baseEnd_3397890 := by
    simpa [prefixWord, tailWord_3397890, baseEnd_3397890] using wordTrace_append hprefix tailTrace_3397890
  have hstable : (prefixWord ++ tailWord_3397890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397890).length < 2 ^ (prefixWord ++ tailWord_3397890).sum := by decide
  have hdescent : baseEnd_3397890 < baseStart_3397890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397961 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 6, 4]
def baseStart_3397961 : Nat := 118140960795 + 3397961 * 2 ^ 59
def prefixEnd_3397961 : Nat := 4983230072969 + 3 ^ 40 * 3397961 * 2
def baseEnd_3397961 : Nat := 1163191492154856797107045

theorem tailTrace_3397961 : CollatzResearch.WordTrace tailWord_3397961 prefixEnd_3397961 1163191492154856797107045 := by
  unfold tailWord_3397961
  simp only [CollatzResearch.WordTrace]
  refine ⟨123933819242775097381833737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82622546161850064921222491 123933819242775097381833737)
  ·
    refine ⟨92950364432081323036375303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123933819242775097381833737 92950364432081323036375303)
    ·
      refine ⟨139425546648121984554562955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92950364432081323036375303 139425546648121984554562955)
      ·
        refine ⟨209138319972182976831844433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139425546648121984554562955 209138319972182976831844433)
        ·
          refine ⟨156853739979137232623883325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209138319972182976831844433 156853739979137232623883325)
          ·
            refine ⟨58820152492176462233956247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156853739979137232623883325 58820152492176462233956247)
            ·
              refine ⟨88230228738264693350934371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58820152492176462233956247 88230228738264693350934371)
              ·
                refine ⟨132345343107397040026401557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88230228738264693350934371 132345343107397040026401557)
                ·
                  refine ⟨6203687958159236251237573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132345343107397040026401557 6203687958159236251237573)
                  ·
                    refine ⟨1163191492154856797107045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6203687958159236251237573 1163191492154856797107045)
                    ·
                      rfl

theorem cell22_3397961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 4].length) (baseStart_3397961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397961 prefixEnd_3397961 := by exact prefixLift 3397961
  have htrace : WordTrace (prefixWord ++ tailWord_3397961) baseStart_3397961 baseEnd_3397961 := by
    simpa [prefixWord, tailWord_3397961, baseEnd_3397961] using wordTrace_append hprefix tailTrace_3397961
  have hstable : (prefixWord ++ tailWord_3397961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397961).length < 2 ^ (prefixWord ++ tailWord_3397961).sum := by decide
  have hdescent : baseEnd_3397961 < baseStart_3397961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398021 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 9]
def baseStart_3398021 : Nat := 118140960795 + 3398021 * 2 ^ 59
def prefixEnd_3398021 : Nat := 4983230072969 + 3 ^ 40 * 3398021 * 2
def baseEnd_3398021 : Nat := 387737343793678880202287

theorem tailTrace_3398021 : CollatzResearch.WordTrace tailWord_3398021 prefixEnd_3398021 387737343793678880202287 := by
  unfold tailWord_3398021
  simp only [CollatzResearch.WordTrace]
  refine ⟨123936007622557727629017917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82624005081705151752678611 123936007622557727629017917)
  ·
    refine ⟨46476002858459147860881719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123936007622557727629017917 46476002858459147860881719)
    ·
      refine ⟨69714004287688721791322579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46476002858459147860881719 69714004287688721791322579)
      ·
        refine ⟨104571006431533082686983869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69714004287688721791322579 104571006431533082686983869)
        ·
          refine ⟨39214127411824906007618951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104571006431533082686983869 39214127411824906007618951)
          ·
            refine ⟨58821191117737359011428427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39214127411824906007618951 58821191117737359011428427)
            ·
              refine ⟨88231786676606038517142641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58821191117737359011428427 88231786676606038517142641)
              ·
                refine ⟨66173840007454528887856981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88231786676606038517142641 66173840007454528887856981)
                ·
                  refine ⟨387737343793678880202287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66173840007454528887856981 387737343793678880202287)
                  ·
                    rfl

theorem cell22_3398021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_3398021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398021 prefixEnd_3398021 := by exact prefixLift 3398021
  have htrace : WordTrace (prefixWord ++ tailWord_3398021) baseStart_3398021 baseEnd_3398021 := by
    simpa [prefixWord, tailWord_3398021, baseEnd_3398021] using wordTrace_append hprefix tailTrace_3398021
  have hstable : (prefixWord ++ tailWord_3398021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398021).length < 2 ^ (prefixWord ++ tailWord_3398021).sum := by decide
  have hdescent : baseEnd_3398021 < baseStart_3398021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398025 : List Nat := [1, 2, 1, 1, 6, 2, 1, 2, 3, 3]
def baseStart_3398025 : Nat := 118140960795 + 3398025 * 2 ^ 59
def prefixEnd_3398025 : Nat := 4983230072969 + 3 ^ 40 * 3398025 * 2
def baseEnd_3398025 : Nat := 1163213400662781963506849

theorem tailTrace_3398025 : CollatzResearch.WordTrace tailWord_3398025 prefixEnd_3398025 1163213400662781963506849 := by
  unfold tailWord_3398025
  simp only [CollatzResearch.WordTrace]
  refine ⟨123936153514543236312163529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82624102343028824208109019 123936153514543236312163529)
  ·
    refine ⟨92952115135907427234122647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123936153514543236312163529 92952115135907427234122647)
    ·
      refine ⟨139428172703861140851183971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92952115135907427234122647 139428172703861140851183971)
      ·
        refine ⟨209142259055791711276775957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139428172703861140851183971 209142259055791711276775957)
        ·
          refine ⟨9803543393240236466098873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 209142259055791711276775957 9803543393240236466098873)
          ·
            refine ⟨7352657544930177349574155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9803543393240236466098873 7352657544930177349574155)
            ·
              refine ⟨11028986317395266024361233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7352657544930177349574155 11028986317395266024361233)
              ·
                refine ⟨8271739738046449518270925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11028986317395266024361233 8271739738046449518270925)
                ·
                  refine ⟨3101902401767418569351597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8271739738046449518270925 3101902401767418569351597)
                  ·
                    refine ⟨1163213400662781963506849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3101902401767418569351597 1163213400662781963506849)
                    ·
                      rfl

theorem cell22_3398025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 3].length) (baseStart_3398025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398025 prefixEnd_3398025 := by exact prefixLift 3398025
  have htrace : WordTrace (prefixWord ++ tailWord_3398025) baseStart_3398025 baseEnd_3398025 := by
    simpa [prefixWord, tailWord_3398025, baseEnd_3398025] using wordTrace_append hprefix tailTrace_3398025
  have hstable : (prefixWord ++ tailWord_3398025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398025).length < 2 ^ (prefixWord ++ tailWord_3398025).sum := by decide
  have hdescent : baseEnd_3398025 < baseStart_3398025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398042 : List Nat := [3, 1, 1, 4, 1, 2, 1, 5, 1, 3]
def baseStart_3398042 : Nat := 118140960795 + 3398042 * 2 ^ 59
def prefixEnd_3398042 : Nat := 4983230072969 + 3 ^ 40 * 3398042 * 2
def baseEnd_3398042 : Nat := 1163219220110199585831797

theorem tailTrace_3398042 : CollatzResearch.WordTrace tailWord_3398042 prefixEnd_3398042 1163219220110199585831797 := by
  unfold tailWord_3398042
  simp only [CollatzResearch.WordTrace]
  refine ⟨30984193388870412053883095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82624515703654432143688253 30984193388870412053883095)
  ·
    refine ⟨46476290083305618080824643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30984193388870412053883095 46476290083305618080824643)
    ·
      refine ⟨69714435124958427121236965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46476290083305618080824643 69714435124958427121236965)
      ·
        refine ⟨13071456585929705085231931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69714435124958427121236965 13071456585929705085231931)
        ·
          refine ⟨19607184878894557627847897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13071456585929705085231931 19607184878894557627847897)
          ·
            refine ⟨14705388659170918220885923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19607184878894557627847897 14705388659170918220885923)
            ·
              refine ⟨22058082988756377331328885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14705388659170918220885923 22058082988756377331328885)
              ·
                refine ⟨2067945280195910374812083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22058082988756377331328885 2067945280195910374812083)
                ·
                  refine ⟨3101917920293865562218125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2067945280195910374812083 3101917920293865562218125)
                  ·
                    refine ⟨1163219220110199585831797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3101917920293865562218125 1163219220110199585831797)
                    ·
                      rfl

theorem cell22_3398042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 1, 3].length) (baseStart_3398042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398042 prefixEnd_3398042 := by exact prefixLift 3398042
  have htrace : WordTrace (prefixWord ++ tailWord_3398042) baseStart_3398042 baseEnd_3398042 := by
    simpa [prefixWord, tailWord_3398042, baseEnd_3398042] using wordTrace_append hprefix tailTrace_3398042
  have hstable : (prefixWord ++ tailWord_3398042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398042).length < 2 ^ (prefixWord ++ tailWord_3398042).sum := by decide
  have hdescent : baseEnd_3398042 < baseStart_3398042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398055 : List Nat := [1, 1, 6, 1, 1, 2, 3, 2, 5]
def baseStart_3398055 : Nat := 118140960795 + 3398055 * 2 ^ 59
def prefixEnd_3398055 : Nat := 4983230072969 + 3 ^ 40 * 3398055 * 2
def baseEnd_3398055 : Nat := 387741223425290628418919

theorem tailTrace_3398055 : CollatzResearch.WordTrace tailWord_3398055 prefixEnd_3398055 387741223425290628418919 := by
  unfold tailWord_3398055
  simp only [CollatzResearch.WordTrace]
  refine ⟨123937247704434551435755619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82624831802956367623837079 123937247704434551435755619)
  ·
    refine ⟨185905871556651827153633429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123937247704434551435755619 185905871556651827153633429)
    ·
      refine ⟨8714337729218054397826567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 185905871556651827153633429 8714337729218054397826567)
      ·
        refine ⟨13071506593827081596739851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8714337729218054397826567 13071506593827081596739851)
        ·
          refine ⟨19607259890740622395109777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13071506593827081596739851 19607259890740622395109777)
          ·
            refine ⟨14705444918055466796332333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19607259890740622395109777 14705444918055466796332333)
            ·
              refine ⟨5514541844270800048624625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14705444918055466796332333 5514541844270800048624625)
              ·
                refine ⟨4135906383203100036468469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5514541844270800048624625 4135906383203100036468469)
                ·
                  refine ⟨387741223425290628418919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4135906383203100036468469 387741223425290628418919)
                  ·
                    rfl

theorem cell22_3398055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 5].length) (baseStart_3398055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398055 prefixEnd_3398055 := by exact prefixLift 3398055
  have htrace : WordTrace (prefixWord ++ tailWord_3398055) baseStart_3398055 baseEnd_3398055 := by
    simpa [prefixWord, tailWord_3398055, baseEnd_3398055] using wordTrace_append hprefix tailTrace_3398055
  have hstable : (prefixWord ++ tailWord_3398055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398055).length < 2 ^ (prefixWord ++ tailWord_3398055).sum := by decide
  have hdescent : baseEnd_3398055 < baseStart_3398055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398102 : List Nat := [5, 2, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_3398102 : Nat := 118140960795 + 3398102 * 2 ^ 59
def prefixEnd_3398102 : Nat := 4983230072969 + 3 ^ 40 * 3398102 * 2
def baseEnd_3398102 : Nat := 1163239759336379429331613

theorem tailTrace_3398102 : CollatzResearch.WordTrace tailWord_3398102 prefixEnd_3398102 1163239759336379429331613 := by
  unfold tailWord_3398102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7746185120954017403919785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82625974623509518975144373 7746185120954017403919785)
  ·
    refine ⟨5809638840715513052939839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7746185120954017403919785 5809638840715513052939839)
    ·
      refine ⟨8714458261073269579409759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5809638840715513052939839 8714458261073269579409759)
      ·
        refine ⟨13071687391609904369114639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8714458261073269579409759 13071687391609904369114639)
        ·
          refine ⟨19607531087414856553671959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13071687391609904369114639 19607531087414856553671959)
          ·
            refine ⟨29411296631122284830507939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19607531087414856553671959 29411296631122284830507939)
            ·
              refine ⟨44116944946683427245761909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29411296631122284830507939 44116944946683427245761909)
              ·
                refine ⟨4135963588751571304290179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44116944946683427245761909 4135963588751571304290179)
                ·
                  refine ⟨6203945383127356956435269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4135963588751571304290179 6203945383127356956435269)
                  ·
                    refine ⟨1163239759336379429331613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6203945383127356956435269 1163239759336379429331613)
                    ·
                      rfl

theorem cell22_3398102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_3398102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398102 prefixEnd_3398102 := by exact prefixLift 3398102
  have htrace : WordTrace (prefixWord ++ tailWord_3398102) baseStart_3398102 baseEnd_3398102 := by
    simpa [prefixWord, tailWord_3398102, baseEnd_3398102] using wordTrace_append hprefix tailTrace_3398102
  have hstable : (prefixWord ++ tailWord_3398102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398102).length < 2 ^ (prefixWord ++ tailWord_3398102).sum := by decide
  have hdescent : baseEnd_3398102 < baseStart_3398102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398117 : List Nat := [1, 3, 1, 5, 2, 2, 1, 1, 6]
def baseStart_3398117 : Nat := 118140960795 + 3398117 * 2 ^ 59
def prefixEnd_3398117 : Nat := 4983230072969 + 3 ^ 40 * 3398117 * 2
def baseEnd_3398117 : Nat := 387748298047641463402189

theorem tailTrace_3398117 : CollatzResearch.WordTrace tailWord_3398117 prefixEnd_3398117 387748298047641463402189 := by
  unfold tailWord_3398117
  simp only [CollatzResearch.WordTrace]
  refine ⟨123939509030209936024512605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82626339353473290683008403 123939509030209936024512605)
  ·
    refine ⟨46477315886328726009192227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123939509030209936024512605 46477315886328726009192227)
    ·
      refine ⟨69715973829493089013788341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46477315886328726009192227 69715973829493089013788341)
      ·
        refine ⟨6535872546514977095042657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69715973829493089013788341 6535872546514977095042657)
        ·
          refine ⟨4901904409886232821281993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6535872546514977095042657 4901904409886232821281993)
          ·
            refine ⟨3676428307414674615961495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4901904409886232821281993 3676428307414674615961495)
            ·
              refine ⟨5514642461122011923942243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3676428307414674615961495 5514642461122011923942243)
              ·
                refine ⟨8271963691683017885913365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5514642461122011923942243 8271963691683017885913365)
                ·
                  refine ⟨387748298047641463402189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8271963691683017885913365 387748298047641463402189)
                  ·
                    rfl

theorem cell22_3398117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_3398117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398117 prefixEnd_3398117 := by exact prefixLift 3398117
  have htrace : WordTrace (prefixWord ++ tailWord_3398117) baseStart_3398117 baseEnd_3398117 := by
    simpa [prefixWord, tailWord_3398117, baseEnd_3398117] using wordTrace_append hprefix tailTrace_3398117
  have hstable : (prefixWord ++ tailWord_3398117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398117).length < 2 ^ (prefixWord ++ tailWord_3398117).sum := by decide
  have hdescent : baseEnd_3398117 < baseStart_3398117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398128 : List Nat := [2, 1, 1, 1, 3, 3, 4, 7]
def baseStart_3398128 : Nat := 118140960795 + 3398128 * 2 ^ 59
def prefixEnd_3398128 : Nat := 4983230072969 + 3 ^ 40 * 3398128 * 2
def baseEnd_3398128 : Nat := 129249851074191558686837

theorem tailTrace_3398128 : CollatzResearch.WordTrace tailWord_3398128 prefixEnd_3398128 129249851074191558686837 := by
  unfold tailWord_3398128
  simp only [CollatzResearch.WordTrace]
  refine ⟨61969955116585042451581519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82626606822113389935442025 61969955116585042451581519)
  ·
    refine ⟨92954932674877563677372279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61969955116585042451581519 92954932674877563677372279)
    ·
      refine ⟨139432399012316345516058419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92954932674877563677372279 139432399012316345516058419)
      ·
        refine ⟨209148598518474518274087629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139432399012316345516058419 209148598518474518274087629)
        ·
          refine ⟨78430724444427944352782861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209148598518474518274087629 78430724444427944352782861)
          ·
            refine ⟨29411521666660479132293573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78430724444427944352782861 29411521666660479132293573)
            ·
              refine ⟨5514660312498839837305045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29411521666660479132293573 5514660312498839837305045)
              ·
                refine ⟨129249851074191558686837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5514660312498839837305045 129249851074191558686837)
                ·
                  rfl

theorem cell22_3398128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 7].length) (baseStart_3398128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398128 prefixEnd_3398128 := by exact prefixLift 3398128
  have htrace : WordTrace (prefixWord ++ tailWord_3398128) baseStart_3398128 baseEnd_3398128 := by
    simpa [prefixWord, tailWord_3398128, baseEnd_3398128] using wordTrace_append hprefix tailTrace_3398128
  have hstable : (prefixWord ++ tailWord_3398128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398128).length < 2 ^ (prefixWord ++ tailWord_3398128).sum := by decide
  have hdescent : baseEnd_3398128 < baseStart_3398128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398233 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 2, 9]
def baseStart_3398233 : Nat := 118140960795 + 3398233 * 2 ^ 59
def prefixEnd_3398233 : Nat := 4983230072969 + 3 ^ 40 * 3398233 * 2
def baseEnd_3398233 : Nat := 1163284603313538754306211

theorem tailTrace_3398233 : CollatzResearch.WordTrace tailWord_3398233 prefixEnd_3398233 1163284603313538754306211 := by
  unfold tailWord_3398233
  simp only [CollatzResearch.WordTrace]
  refine ⟨123943739897789687835735353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82629159931859791890490235 123943739897789687835735353)
  ·
    refine ⟨92957804923342265876801515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123943739897789687835735353 92957804923342265876801515)
    ·
      refine ⟨139436707385013398815202273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92957804923342265876801515 139436707385013398815202273)
      ·
        refine ⟨104577530538760049111401705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139436707385013398815202273 104577530538760049111401705)
        ·
          refine ⟨78433147904070036833551279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104577530538760049111401705 78433147904070036833551279)
          ·
            refine ⟨117649721856105055250326919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78433147904070036833551279 117649721856105055250326919)
            ·
              refine ⟨176474582784157582875490379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117649721856105055250326919 176474582784157582875490379)
              ·
                refine ⟨264711874176236374313235569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176474582784157582875490379 264711874176236374313235569)
                ·
                  refine ⟨198533905632177280734926677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264711874176236374313235569 198533905632177280734926677)
                  ·
                    refine ⟨1163284603313538754306211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 198533905632177280734926677 1163284603313538754306211)
                    ·
                      rfl

theorem cell22_3398233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_3398233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398233 prefixEnd_3398233 := by exact prefixLift 3398233
  have htrace : WordTrace (prefixWord ++ tailWord_3398233) baseStart_3398233 baseEnd_3398233 := by
    simpa [prefixWord, tailWord_3398233, baseEnd_3398233] using wordTrace_append hprefix tailTrace_3398233
  have hstable : (prefixWord ++ tailWord_3398233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398233).length < 2 ^ (prefixWord ++ tailWord_3398233).sum := by decide
  have hdescent : baseEnd_3398233 < baseStart_3398233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398254 : List Nat := [4, 1, 2, 2, 2, 2, 2, 2, 1, 4]
def baseStart_3398254 : Nat := 118140960795 + 3398254 * 2 ^ 59
def prefixEnd_3398254 : Nat := 4983230072969 + 3 ^ 40 * 3398254 * 2
def baseEnd_3398254 : Nat := 1163291792042701699531147

theorem tailTrace_3398254 : CollatzResearch.WordTrace tailWord_3398254 prefixEnd_3398254 1163291792042701699531147 := by
  unfold tailWord_3398254
  simp only [CollatzResearch.WordTrace]
  refine ⟨15493063228839201052781227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82629670553809072281499877 15493063228839201052781227)
  ·
    refine ⟨23239594843258801579171841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15493063228839201052781227 23239594843258801579171841)
    ·
      refine ⟨17429696132444101184378881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23239594843258801579171841 17429696132444101184378881)
      ·
        refine ⟨13072272099333075888284161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17429696132444101184378881 13072272099333075888284161)
        ·
          refine ⟨9804204074499806916213121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13072272099333075888284161 9804204074499806916213121)
          ·
            refine ⟨7353153055874855187159841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9804204074499806916213121 7353153055874855187159841)
            ·
              refine ⟨5514864791906141390369881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7353153055874855187159841 5514864791906141390369881)
              ·
                refine ⟨4136148593929606042777411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5514864791906141390369881 4136148593929606042777411)
                ·
                  refine ⟨6204222890894409064166117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4136148593929606042777411 6204222890894409064166117)
                  ·
                    refine ⟨1163291792042701699531147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6204222890894409064166117 1163291792042701699531147)
                    ·
                      rfl

theorem cell22_3398254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_3398254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398254 prefixEnd_3398254 := by exact prefixLift 3398254
  have htrace : WordTrace (prefixWord ++ tailWord_3398254) baseStart_3398254 baseEnd_3398254 := by
    simpa [prefixWord, tailWord_3398254, baseEnd_3398254] using wordTrace_append hprefix tailTrace_3398254
  have hstable : (prefixWord ++ tailWord_3398254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398254).length < 2 ^ (prefixWord ++ tailWord_3398254).sum := by decide
  have hdescent : baseEnd_3398254 < baseStart_3398254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398265 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 1, 6]
def baseStart_3398265 : Nat := 118140960795 + 3398265 * 2 ^ 59
def prefixEnd_3398265 : Nat := 4983230072969 + 3 ^ 40 * 3398265 * 2
def baseEnd_3398265 : Nat := 1163295557567501337506113

theorem tailTrace_3398265 : CollatzResearch.WordTrace tailWord_3398265 prefixEnd_3398265 1163295557567501337506113 := by
  unfold tailWord_3398265
  simp only [CollatzResearch.WordTrace]
  refine ⟨123944907033673757300900249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82629938022449171533933499 123944907033673757300900249)
  ·
    refine ⟨92958680275255317975675187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123944907033673757300900249 92958680275255317975675187)
    ·
      refine ⟨139438020412882976963512781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92958680275255317975675187 139438020412882976963512781)
      ·
        refine ⟨52289257654831116361317293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139438020412882976963512781 52289257654831116361317293)
        ·
          refine ⟨19608471620561668635493985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52289257654831116361317293 19608471620561668635493985)
          ·
            refine ⟨14706353715421251476620489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19608471620561668635493985 14706353715421251476620489)
            ·
              refine ⟨11029765286565938607465367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14706353715421251476620489 11029765286565938607465367)
              ·
                refine ⟨16544647929848907911198051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11029765286565938607465367 16544647929848907911198051)
                ·
                  refine ⟨24816971894773361866797077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16544647929848907911198051 24816971894773361866797077)
                  ·
                    refine ⟨1163295557567501337506113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24816971894773361866797077 1163295557567501337506113)
                    ·
                      rfl

theorem cell22_3398265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_3398265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398265 prefixEnd_3398265 := by exact prefixLift 3398265
  have htrace : WordTrace (prefixWord ++ tailWord_3398265) baseStart_3398265 baseEnd_3398265 := by
    simpa [prefixWord, tailWord_3398265, baseEnd_3398265] using wordTrace_append hprefix tailTrace_3398265
  have hstable : (prefixWord ++ tailWord_3398265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398265).length < 2 ^ (prefixWord ++ tailWord_3398265).sum := by decide
  have hdescent : baseEnd_3398265 < baseStart_3398265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398329 : List Nat := [1, 2, 1, 4, 1, 1, 1, 7, 1, 3]
def baseStart_3398329 : Nat := 118140960795 + 3398329 * 2 ^ 59
def prefixEnd_3398329 : Nat := 4983230072969 + 3 ^ 40 * 3398329 * 2
def baseEnd_3398329 : Nat := 1163317466075426503905917

theorem tailTrace_3398329 : CollatzResearch.WordTrace tailWord_3398329 prefixEnd_3398329 1163317466075426503905917 := by
  unfold tailWord_3398329
  simp only [CollatzResearch.WordTrace]
  refine ⟨123947241305441896231230041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82631494203627930820820027 123947241305441896231230041)
  ·
    refine ⟨92960430979081422173422531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123947241305441896231230041 92960430979081422173422531)
    ·
      refine ⟨139440646468622133260133797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92960430979081422173422531 139440646468622133260133797)
      ·
        refine ⟨26145121212866649986275087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139440646468622133260133797 26145121212866649986275087)
        ·
          refine ⟨39217681819299974979412631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26145121212866649986275087 39217681819299974979412631)
          ·
            refine ⟨58826522728949962469118947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39217681819299974979412631 58826522728949962469118947)
            ·
              refine ⟨88239784093424943703678421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58826522728949962469118947 88239784093424943703678421)
              ·
                refine ⟨2068119939689647118054963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 88239784093424943703678421 2068119939689647118054963)
                ·
                  refine ⟨3102179909534470677082445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2068119939689647118054963 3102179909534470677082445)
                  ·
                    refine ⟨1163317466075426503905917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3102179909534470677082445 1163317466075426503905917)
                    ·
                      rfl

theorem cell22_3398329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 1, 3].length) (baseStart_3398329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398329 prefixEnd_3398329 := by exact prefixLift 3398329
  have htrace : WordTrace (prefixWord ++ tailWord_3398329) baseStart_3398329 baseEnd_3398329 := by
    simpa [prefixWord, tailWord_3398329, baseEnd_3398329] using wordTrace_append hprefix tailTrace_3398329
  have hstable : (prefixWord ++ tailWord_3398329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398329).length < 2 ^ (prefixWord ++ tailWord_3398329).sum := by decide
  have hdescent : baseEnd_3398329 < baseStart_3398329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398346 : List Nat := [3, 1, 2, 1, 4, 2, 1, 4, 1, 3]
def baseStart_3398346 : Nat := 118140960795 + 3398346 * 2 ^ 59
def prefixEnd_3398346 : Nat := 4983230072969 + 3 ^ 40 * 3398346 * 2
def baseEnd_3398346 : Nat := 1163323285522844126230865

theorem tailTrace_3398346 : CollatzResearch.WordTrace tailWord_3398346 prefixEnd_3398346 1163323285522844126230865 := by
  unfold tailWord_3398346
  simp only [CollatzResearch.WordTrace]
  refine ⟨30986965336595077033649723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82631907564253538756399261 30986965336595077033649723)
  ·
    refine ⟨46480448004892615550474585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30986965336595077033649723 46480448004892615550474585)
    ·
      refine ⟨34860336003669461662855939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46480448004892615550474585 34860336003669461662855939)
      ·
        refine ⟨52290504005504192494283909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34860336003669461662855939 52290504005504192494283909)
        ·
          refine ⟨9804469501032036092678233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52290504005504192494283909 9804469501032036092678233)
          ·
            refine ⟨7353352125774027069508675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9804469501032036092678233 7353352125774027069508675)
            ·
              refine ⟨11030028188661040604263013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7353352125774027069508675 11030028188661040604263013)
              ·
                refine ⟨2068130285373945113299315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11030028188661040604263013 2068130285373945113299315)
                ·
                  refine ⟨3102195428060917669948973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2068130285373945113299315 3102195428060917669948973)
                  ·
                    refine ⟨1163323285522844126230865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3102195428060917669948973 1163323285522844126230865)
                    ·
                      rfl

theorem cell22_3398346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_3398346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398346 prefixEnd_3398346 := by exact prefixLift 3398346
  have htrace : WordTrace (prefixWord ++ tailWord_3398346) baseStart_3398346 baseEnd_3398346 := by
    simpa [prefixWord, tailWord_3398346, baseEnd_3398346] using wordTrace_append hprefix tailTrace_3398346
  have hstable : (prefixWord ++ tailWord_3398346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398346).length < 2 ^ (prefixWord ++ tailWord_3398346).sum := by decide
  have hdescent : baseEnd_3398346 < baseStart_3398346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398372 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_3398372 : Nat := 118140960795 + 3398372 * 2 ^ 59
def prefixEnd_3398372 : Nat := 4983230072969 + 3 ^ 40 * 3398372 * 2
def baseEnd_3398372 : Nat := 1163332185854188725080785

theorem tailTrace_3398372 : CollatzResearch.WordTrace tailWord_3398372 prefixEnd_3398372 1163332185854188725080785 := by
  unfold tailWord_3398372
  simp only [CollatzResearch.WordTrace]
  refine ⟨61974404822143057287522685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82632539762857409716696913 61974404822143057287522685)
  ·
    refine ⟨23240401808303646482821007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61974404822143057287522685 23240401808303646482821007)
    ·
      refine ⟨34860602712455469724231511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23240401808303646482821007 34860602712455469724231511)
      ·
        refine ⟨52290904068683204586347267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34860602712455469724231511 52290904068683204586347267)
        ·
          refine ⟨78436356103024806879520901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52290904068683204586347267 78436356103024806879520901)
          ·
            refine ⟨14706816769317151289910169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78436356103024806879520901 14706816769317151289910169)
            ·
              refine ⟨11030112576987863467432627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14706816769317151289910169 11030112576987863467432627)
              ·
                refine ⟨16545168865481795201148941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11030112576987863467432627 16545168865481795201148941)
                ·
                  refine ⟨6204438324555673200430853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16545168865481795201148941 6204438324555673200430853)
                  ·
                    refine ⟨1163332185854188725080785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6204438324555673200430853 1163332185854188725080785)
                    ·
                      rfl

theorem cell22_3398372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_3398372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398372 prefixEnd_3398372 := by exact prefixLift 3398372
  have htrace : WordTrace (prefixWord ++ tailWord_3398372) baseStart_3398372 baseEnd_3398372 := by
    simpa [prefixWord, tailWord_3398372, baseEnd_3398372] using wordTrace_append hprefix tailTrace_3398372
  have hstable : (prefixWord ++ tailWord_3398372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398372).length < 2 ^ (prefixWord ++ tailWord_3398372).sum := by decide
  have hdescent : baseEnd_3398372 < baseStart_3398372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398400 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 5, 6]
def baseStart_3398400 : Nat := 118140960795 + 3398400 * 2 ^ 59
def prefixEnd_3398400 : Nat := 4983230072969 + 3 ^ 40 * 3398400 * 2
def baseEnd_3398400 : Nat := 1163341770826405985380699

theorem tailTrace_3398400 : CollatzResearch.WordTrace tailWord_3398400 prefixEnd_3398400 1163341770826405985380699 := by
  unfold tailWord_3398400
  simp only [CollatzResearch.WordTrace]
  refine ⟨61974915444092337678532327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82633220592123116904709769 61974915444092337678532327)
  ·
    refine ⟨92962373166138506517798491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61974915444092337678532327 92962373166138506517798491)
    ·
      refine ⟨139443559749207759776697737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92962373166138506517798491 139443559749207759776697737)
      ·
        refine ⟨104582669811905819832523303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139443559749207759776697737 104582669811905819832523303)
        ·
          refine ⟨156874004717858729748784955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104582669811905819832523303 156874004717858729748784955)
          ·
            refine ⟨235311007076788094623177433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156874004717858729748784955 235311007076788094623177433)
            ·
              refine ⟨176483255307591070967383075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235311007076788094623177433 176483255307591070967383075)
              ·
                refine ⟨264724882961386606451074613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176483255307591070967383075 264724882961386606451074613)
                ·
                  refine ⟨24817957777629994354788245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 264724882961386606451074613 24817957777629994354788245)
                  ·
                    refine ⟨1163341770826405985380699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24817957777629994354788245 1163341770826405985380699)
                    ·
                      rfl

theorem cell22_3398400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_3398400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398400 prefixEnd_3398400 := by exact prefixLift 3398400
  have htrace : WordTrace (prefixWord ++ tailWord_3398400) baseStart_3398400 baseEnd_3398400 := by
    simpa [prefixWord, tailWord_3398400, baseEnd_3398400] using wordTrace_append hprefix tailTrace_3398400
  have hstable : (prefixWord ++ tailWord_3398400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398400).length < 2 ^ (prefixWord ++ tailWord_3398400).sum := by decide
  have hdescent : baseEnd_3398400 < baseStart_3398400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398404 : List Nat := [2, 3, 2, 2, 1, 1, 1, 6, 4]
def baseStart_3398404 : Nat := 118140960795 + 3398404 * 2 ^ 59
def prefixEnd_3398404 : Nat := 4983230072969 + 3 ^ 40 * 3398404 * 2
def baseEnd_3398404 : Nat := 387781046702717102760229

theorem tailTrace_3398404 : CollatzResearch.WordTrace tailWord_3398404 prefixEnd_3398404 387781046702717102760229 := by
  unfold tailWord_3398404
  simp only [CollatzResearch.WordTrace]
  refine ⟨61974988390085092020105133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82633317853446789360140177 61974988390085092020105133)
  ·
    refine ⟨23240620646281909507539425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61974988390085092020105133 23240620646281909507539425)
    ·
      refine ⟨17430465484711432130654569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23240620646281909507539425 17430465484711432130654569)
      ·
        refine ⟨13072849113533574097990927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17430465484711432130654569 13072849113533574097990927)
        ·
          refine ⟨19609273670300361146986391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13072849113533574097990927 19609273670300361146986391)
          ·
            refine ⟨29413910505450541720479587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19609273670300361146986391 29413910505450541720479587)
            ·
              refine ⟨44120865758175812580719381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29413910505450541720479587 44120865758175812580719381)
              ·
                refine ⟨2068165582414491214721221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44120865758175812580719381 2068165582414491214721221)
                ·
                  refine ⟨387781046702717102760229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2068165582414491214721221 387781046702717102760229)
                  ·
                    rfl

theorem cell22_3398404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_3398404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398404 prefixEnd_3398404 := by exact prefixLift 3398404
  have htrace : WordTrace (prefixWord ++ tailWord_3398404) baseStart_3398404 baseEnd_3398404 := by
    simpa [prefixWord, tailWord_3398404, baseEnd_3398404] using wordTrace_append hprefix tailTrace_3398404
  have hstable : (prefixWord ++ tailWord_3398404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398404).length < 2 ^ (prefixWord ++ tailWord_3398404).sum := by decide
  have hdescent : baseEnd_3398404 < baseStart_3398404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398415 : List Nat := [1, 1, 2, 1, 1, 1, 6, 9]
def baseStart_3398415 : Nat := 118140960795 + 3398415 * 2 ^ 59
def prefixEnd_3398415 : Nat := 4983230072969 + 3 ^ 40 * 3398415 * 2
def baseEnd_3398415 : Nat := 129260767292550105139517

theorem tailTrace_3398415 : CollatzResearch.WordTrace tailWord_3398415 prefixEnd_3398415 129260767292550105139517 := by
  unfold tailWord_3398415
  simp only [CollatzResearch.WordTrace]
  refine ⟨123950377983130332918860699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82633585322086888612573799 123950377983130332918860699)
  ·
    refine ⟨185925566974695499378291049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123950377983130332918860699 185925566974695499378291049)
    ·
      refine ⟨139444175231021624533718287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185925566974695499378291049 139444175231021624533718287)
      ·
        refine ⟨209166262846532436800577431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139444175231021624533718287 209166262846532436800577431)
        ·
          refine ⟨313749394269798655200866147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209166262846532436800577431 313749394269798655200866147)
          ·
            refine ⟨470624091404697982801299221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313749394269798655200866147 470624091404697982801299221)
            ·
              refine ⟨22060504284595217943810901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 470624091404697982801299221 22060504284595217943810901)
              ·
                refine ⟨129260767292550105139517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22060504284595217943810901 129260767292550105139517)
                ·
                  rfl

theorem cell22_3398415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 9].length) (baseStart_3398415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398415 prefixEnd_3398415 := by exact prefixLift 3398415
  have htrace : WordTrace (prefixWord ++ tailWord_3398415) baseStart_3398415 baseEnd_3398415 := by
    simpa [prefixWord, tailWord_3398415, baseEnd_3398415] using wordTrace_append hprefix tailTrace_3398415
  have hstable : (prefixWord ++ tailWord_3398415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398415).length < 2 ^ (prefixWord ++ tailWord_3398415).sum := by decide
  have hdescent : baseEnd_3398415 < baseStart_3398415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398432 : List Nat := [2, 1, 1, 5, 1, 3, 1, 8]
def baseStart_3398432 : Nat := 118140960795 + 3398432 * 2 ^ 59
def prefixEnd_3398432 : Nat := 4983230072969 + 3 ^ 40 * 3398432 * 2
def baseEnd_3398432 : Nat := 129261413897818729842289

theorem tailTrace_3398432 : CollatzResearch.WordTrace tailWord_3398432 prefixEnd_3398432 129261413897818729842289 := by
  unfold tailWord_3398432
  simp only [CollatzResearch.WordTrace]
  refine ⟨61975499012034372411114775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82633998682712496548153033 61975499012034372411114775)
  ·
    refine ⟨92963248518051558616672163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61975499012034372411114775 92963248518051558616672163)
    ·
      refine ⟨139444872777077337925008245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92963248518051558616672163 139444872777077337925008245)
      ·
        refine ⟨13072956822851000430469523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139444872777077337925008245 13072956822851000430469523)
        ·
          refine ⟨19609435234276500645704285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13072956822851000430469523 19609435234276500645704285)
          ·
            refine ⟨7353538212853687742139107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19609435234276500645704285 7353538212853687742139107)
            ·
              refine ⟨11030307319280531613208661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7353538212853687742139107 11030307319280531613208661)
              ·
                refine ⟨129261413897818729842289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11030307319280531613208661 129261413897818729842289)
                ·
                  rfl

theorem cell22_3398432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 8].length) (baseStart_3398432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398432 prefixEnd_3398432 := by exact prefixLift 3398432
  have htrace : WordTrace (prefixWord ++ tailWord_3398432) baseStart_3398432 baseEnd_3398432 := by
    simpa [prefixWord, tailWord_3398432, baseEnd_3398432] using wordTrace_append hprefix tailTrace_3398432
  have hstable : (prefixWord ++ tailWord_3398432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398432).length < 2 ^ (prefixWord ++ tailWord_3398432).sum := by decide
  have hdescent : baseEnd_3398432 < baseStart_3398432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398470 : List Nat := [6, 1, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_3398470 : Nat := 118140960795 + 3398470 * 2 ^ 59
def prefixEnd_3398470 : Nat := 4983230072969 + 3 ^ 40 * 3398470 * 2
def baseEnd_3398470 : Nat := 1163365733256949136130485

theorem tailTrace_3398470 : CollatzResearch.WordTrace tailWord_3398470 prefixEnd_3398470 1163365733256949136130485 := by
  unfold tailWord_3398470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3873511999935346166003527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82634922665287384874741909 3873511999935346166003527)
  ·
    refine ⟨5810267999903019249005291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3873511999935346166003527 5810267999903019249005291)
    ·
      refine ⟨8715401999854528873507937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5810267999903019249005291 8715401999854528873507937)
      ·
        refine ⟨6536551499890896655130953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8715401999854528873507937 6536551499890896655130953)
        ·
          refine ⟨4902413624918172491348215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6536551499890896655130953 4902413624918172491348215)
          ·
            refine ⟨7353620437377258737022323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4902413624918172491348215 7353620437377258737022323)
            ·
              refine ⟨11030430656065888105533485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7353620437377258737022323 11030430656065888105533485)
              ·
                refine ⟨4136411496024708039575057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11030430656065888105533485 4136411496024708039575057)
                ·
                  refine ⟨3102308622018531029681293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4136411496024708039575057 3102308622018531029681293)
                  ·
                    refine ⟨1163365733256949136130485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3102308622018531029681293 1163365733256949136130485)
                    ·
                      rfl

theorem cell22_3398470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_3398470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398470 prefixEnd_3398470 := by exact prefixLift 3398470
  have htrace : WordTrace (prefixWord ++ tailWord_3398470) baseStart_3398470 baseEnd_3398470 := by
    simpa [prefixWord, tailWord_3398470, baseEnd_3398470] using wordTrace_append hprefix tailTrace_3398470
  have hstable : (prefixWord ++ tailWord_3398470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398470).length < 2 ^ (prefixWord ++ tailWord_3398470).sum := by decide
  have hdescent : baseEnd_3398470 < baseStart_3398470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398522 : List Nat := [3, 1, 1, 1, 1, 1, 3, 5, 6]
def baseStart_3398522 : Nat := 118140960795 + 3398522 * 2 ^ 59
def prefixEnd_3398522 : Nat := 4983230072969 + 3 ^ 40 * 3398522 * 2
def baseEnd_3398522 : Nat := 387794511306546111276775

theorem tailTrace_3398522 : CollatzResearch.WordTrace tailWord_3398522 prefixEnd_3398522 387794511306546111276775 := by
  unfold tailWord_3398522
  simp only [CollatzResearch.WordTrace]
  refine ⟨30988570148435672548251455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82636187062495126795337213 30988570148435672548251455)
  ·
    refine ⟨46482855222653508822377183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30988570148435672548251455 46482855222653508822377183)
    ·
      refine ⟨69724282833980263233565775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46482855222653508822377183 69724282833980263233565775)
      ·
        refine ⟨104586424250970394850348663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69724282833980263233565775 104586424250970394850348663)
        ·
          refine ⟨156879636376455592275522995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104586424250970394850348663 156879636376455592275522995)
          ·
            refine ⟨235319454564683388413284493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156879636376455592275522995 235319454564683388413284493)
            ·
              refine ⟨88244795461756270654981685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235319454564683388413284493 88244795461756270654981685)
              ·
                refine ⟨8272949574539650373904533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88244795461756270654981685 8272949574539650373904533)
                ·
                  refine ⟨387794511306546111276775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8272949574539650373904533 387794511306546111276775)
                  ·
                    rfl

theorem cell22_3398522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_3398522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398522 prefixEnd_3398522 := by exact prefixLift 3398522
  have htrace : WordTrace (prefixWord ++ tailWord_3398522) baseStart_3398522 baseEnd_3398522 := by
    simpa [prefixWord, tailWord_3398522, baseEnd_3398522] using wordTrace_append hprefix tailTrace_3398522
  have hstable : (prefixWord ++ tailWord_3398522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398522).length < 2 ^ (prefixWord ++ tailWord_3398522).sum := by decide
  have hdescent : baseEnd_3398522 < baseStart_3398522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398573 : List Nat := [1, 5, 2, 3, 1, 1, 2, 1, 6]
def baseStart_3398573 : Nat := 118140960795 + 3398573 * 2 ^ 59
def prefixEnd_3398573 : Nat := 4983230072969 + 3 ^ 40 * 3398573 * 2
def baseEnd_3398573 : Nat := 387800330753963733601723

theorem tailTrace_3398573 : CollatzResearch.WordTrace tailWord_3398573 prefixEnd_3398573 387800330753963733601723 := by
  unfold tailWord_3398573
  simp only [CollatzResearch.WordTrace]
  refine ⟨123956140716557925903112373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82637427144371950602074915 123956140716557925903112373)
  ·
    refine ⟨11620888192177305553416785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123956140716557925903112373 11620888192177305553416785)
    ·
      refine ⟨8715666144132979165062589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11620888192177305553416785 8715666144132979165062589)
      ·
        refine ⟨3268374804049867186898471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8715666144132979165062589 3268374804049867186898471)
        ·
          refine ⟨4902562206074800780347707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3268374804049867186898471 4902562206074800780347707)
          ·
            refine ⟨7353843309112201170521561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4902562206074800780347707 7353843309112201170521561)
            ·
              refine ⟨5515382481834150877891171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7353843309112201170521561 5515382481834150877891171)
              ·
                refine ⟨8273073722751226316836757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5515382481834150877891171 8273073722751226316836757)
                ·
                  refine ⟨387800330753963733601723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8273073722751226316836757 387800330753963733601723)
                  ·
                    rfl

theorem cell22_3398573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_3398573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398573 prefixEnd_3398573 := by exact prefixLift 3398573
  have htrace : WordTrace (prefixWord ++ tailWord_3398573) baseStart_3398573 baseEnd_3398573 := by
    simpa [prefixWord, tailWord_3398573, baseEnd_3398573] using wordTrace_append hprefix tailTrace_3398573
  have hstable : (prefixWord ++ tailWord_3398573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398573).length < 2 ^ (prefixWord ++ tailWord_3398573).sum := by decide
  have hdescent : baseEnd_3398573 < baseStart_3398573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398597 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 3, 8]
def baseStart_3398597 : Nat := 118140960795 + 3398597 * 2 ^ 59
def prefixEnd_3398597 : Nat := 4983230072969 + 3 ^ 40 * 3398597 * 2
def baseEnd_3398597 : Nat := 1163409207952363138205095

theorem tailTrace_3398597 : CollatzResearch.WordTrace tailWord_3398597 prefixEnd_3398597 1163409207952363138205095 := by
  unfold tailWord_3398597
  simp only [CollatzResearch.WordTrace]
  refine ⟨123957016068470978001986045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82638010712313985334657363 123957016068470978001986045)
  ·
    refine ⟨46483881025676616750744767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123957016068470978001986045 46483881025676616750744767)
    ·
      refine ⟨69725821538514925126117151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46483881025676616750744767 69725821538514925126117151)
      ·
        refine ⟨104588732307772387689175727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69725821538514925126117151 104588732307772387689175727)
        ·
          refine ⟨156883098461658581533763591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104588732307772387689175727 156883098461658581533763591)
          ·
            refine ⟨235324647692487872300645387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156883098461658581533763591 235324647692487872300645387)
            ·
              refine ⟨352986971538731808450968081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235324647692487872300645387 352986971538731808450968081)
              ·
                refine ⟨264740228654048856338226061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352986971538731808450968081 264740228654048856338226061)
                ·
                  refine ⟨99277585745268321126834773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264740228654048856338226061 99277585745268321126834773)
                  ·
                    refine ⟨1163409207952363138205095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99277585745268321126834773 1163409207952363138205095)
                    ·
                      rfl

theorem cell22_3398597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_3398597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398597 prefixEnd_3398597 := by exact prefixLift 3398597
  have htrace : WordTrace (prefixWord ++ tailWord_3398597) baseStart_3398597 baseEnd_3398597 := by
    simpa [prefixWord, tailWord_3398597, baseEnd_3398597] using wordTrace_append hprefix tailTrace_3398597
  have hstable : (prefixWord ++ tailWord_3398597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398597).length < 2 ^ (prefixWord ++ tailWord_3398597).sum := by decide
  have hdescent : baseEnd_3398597 < baseStart_3398597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398684 : List Nat := [2, 2, 3, 1, 5, 1, 2, 2, 1, 3]
def baseStart_3398684 : Nat := 118140960795 + 3398684 * 2 ^ 59
def prefixEnd_3398684 : Nat := 4983230072969 + 3 ^ 40 * 3398684 * 2
def baseEnd_3398684 : Nat := 1163438989830323911279829

theorem tailTrace_3398684 : CollatzResearch.WordTrace tailWord_3398684 prefixEnd_3398684 1163438989830323911279829 := by
  unfold tailWord_3398684
  simp only [CollatzResearch.WordTrace]
  refine ⟨61980094609577895930201553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82640126146103861240268737 61980094609577895930201553)
  ·
    refine ⟨46485070957183421947651165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61980094609577895930201553 46485070957183421947651165)
    ·
      refine ⟨17431901608943783230369187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46485070957183421947651165 17431901608943783230369187)
      ·
        refine ⟨26147852413415674845553781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17431901608943783230369187 26147852413415674845553781)
        ·
          refine ⟨2451361163757719516770667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26147852413415674845553781 2451361163757719516770667)
          ·
            refine ⟨3677041745636579275156001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2451361163757719516770667 3677041745636579275156001)
            ·
              refine ⟨2757781309227434456367001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3677041745636579275156001 2757781309227434456367001)
              ·
                refine ⟨2068335981920575842275251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2757781309227434456367001 2068335981920575842275251)
                ·
                  refine ⟨3102503972880863763412877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2068335981920575842275251 3102503972880863763412877)
                  ·
                    refine ⟨1163438989830323911279829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3102503972880863763412877 1163438989830323911279829)
                    ·
                      rfl

theorem cell22_3398684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_3398684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398684 prefixEnd_3398684 := by exact prefixLift 3398684
  have htrace : WordTrace (prefixWord ++ tailWord_3398684) baseStart_3398684 baseEnd_3398684 := by
    simpa [prefixWord, tailWord_3398684, baseEnd_3398684] using wordTrace_append hprefix tailTrace_3398684
  have hstable : (prefixWord ++ tailWord_3398684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398684).length < 2 ^ (prefixWord ++ tailWord_3398684).sum := by decide
  have hdescent : baseEnd_3398684 < baseStart_3398684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398704 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 1, 6]
def baseStart_3398704 : Nat := 118140960795 + 3398704 * 2 ^ 59
def prefixEnd_3398704 : Nat := 4983230072969 + 3 ^ 40 * 3398704 * 2
def baseEnd_3398704 : Nat := 1163445836239050525779767

theorem tailTrace_3398704 : CollatzResearch.WordTrace tailWord_3398704 prefixEnd_3398704 1163445836239050525779767 := by
  unfold tailWord_3398704
  simp only [CollatzResearch.WordTrace]
  refine ⟨61980459339541667638065583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82640612452722223517420777 61980459339541667638065583)
  ·
    refine ⟨92970689009312501457098375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61980459339541667638065583 92970689009312501457098375)
    ·
      refine ⟨139456033513968752185647563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92970689009312501457098375 139456033513968752185647563)
      ·
        refine ⟨209184050270953128278471345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139456033513968752185647563 209184050270953128278471345)
        ·
          refine ⟨156888037703214846208853509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209184050270953128278471345 156888037703214846208853509)
          ·
            refine ⟨29416507069352783664160033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156888037703214846208853509 29416507069352783664160033)
            ·
              refine ⟨22062380302014587748120025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29416507069352783664160033 22062380302014587748120025)
              ·
                refine ⟨16546785226510940811090019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22062380302014587748120025 16546785226510940811090019)
                ·
                  refine ⟨24820177839766411216635029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16546785226510940811090019 24820177839766411216635029)
                  ·
                    refine ⟨1163445836239050525779767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24820177839766411216635029 1163445836239050525779767)
                    ·
                      rfl

theorem cell22_3398704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_3398704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398704 prefixEnd_3398704 := by exact prefixLift 3398704
  have htrace : WordTrace (prefixWord ++ tailWord_3398704) baseStart_3398704 baseEnd_3398704 := by
    simpa [prefixWord, tailWord_3398704, baseEnd_3398704] using wordTrace_append hprefix tailTrace_3398704
  have hstable : (prefixWord ++ tailWord_3398704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398704).length < 2 ^ (prefixWord ++ tailWord_3398704).sum := by decide
  have hdescent : baseEnd_3398704 < baseStart_3398704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398706 : List Nat := [3, 2, 1, 1, 2, 2, 4, 1, 1, 5]
def baseStart_3398706 : Nat := 118140960795 + 3398706 * 2 ^ 59
def prefixEnd_3398706 : Nat := 4983230072969 + 3 ^ 40 * 3398706 * 2
def baseEnd_3398706 : Nat := 1163446520879923187229761

theorem tailTrace_3398706 : CollatzResearch.WordTrace tailWord_3398706 prefixEnd_3398706 1163446520879923187229761 := by
  unfold tailWord_3398706
  simp only [CollatzResearch.WordTrace]
  refine ⟨30990247906269022404425993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82640661083384059745135981 30990247906269022404425993)
  ·
    refine ⟨23242685929701766803319495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30990247906269022404425993 23242685929701766803319495)
    ·
      refine ⟨34864028894552650204979243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23242685929701766803319495 34864028894552650204979243)
      ·
        refine ⟨52296043341828975307468865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34864028894552650204979243 52296043341828975307468865)
        ·
          refine ⟨39222032506371731480601649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52296043341828975307468865 39222032506371731480601649)
          ·
            refine ⟨29416524379778798610451237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39222032506371731480601649 29416524379778798610451237)
            ·
              refine ⟨5515598321208524739459607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29416524379778798610451237 5515598321208524739459607)
              ·
                refine ⟨8273397481812787109189411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5515598321208524739459607 8273397481812787109189411)
                ·
                  refine ⟨12410096222719180663784117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8273397481812787109189411 12410096222719180663784117)
                  ·
                    refine ⟨1163446520879923187229761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12410096222719180663784117 1163446520879923187229761)
                    ·
                      rfl

theorem cell22_3398706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_3398706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398706 prefixEnd_3398706 := by exact prefixLift 3398706
  have htrace : WordTrace (prefixWord ++ tailWord_3398706) baseStart_3398706 baseEnd_3398706 := by
    simpa [prefixWord, tailWord_3398706, baseEnd_3398706] using wordTrace_append hprefix tailTrace_3398706
  have hstable : (prefixWord ++ tailWord_3398706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398706).length < 2 ^ (prefixWord ++ tailWord_3398706).sum := by decide
  have hdescent : baseEnd_3398706 < baseStart_3398706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398708 : List Nat := [2, 5, 1, 2, 1, 2, 1, 2, 6]
def baseStart_3398708 : Nat := 118140960795 + 3398708 * 2 ^ 59
def prefixEnd_3398708 : Nat := 4983230072969 + 3 ^ 40 * 3398708 * 2
def baseEnd_3398708 : Nat := 387815735173598616226585

theorem tailTrace_3398708 : CollatzResearch.WordTrace tailWord_3398708 prefixEnd_3398708 387815735173598616226585 := by
  unfold tailWord_3398708
  simp only [CollatzResearch.WordTrace]
  refine ⟨61980532285534421979638389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82640709714045895972851185 61980532285534421979638389)
  ·
    refine ⟨5810674901768852060591099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61980532285534421979638389 5810674901768852060591099)
    ·
      refine ⟨8716012352653278090886649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5810674901768852060591099 8716012352653278090886649)
      ·
        refine ⟨6537009264489958568164987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8716012352653278090886649 6537009264489958568164987)
        ·
          refine ⟨9805513896734937852247481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6537009264489958568164987 9805513896734937852247481)
          ·
            refine ⟨7354135422551203389185611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9805513896734937852247481 7354135422551203389185611)
            ·
              refine ⟨11031203133826805083778417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7354135422551203389185611 11031203133826805083778417)
              ·
                refine ⟨8273402350370103812833813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11031203133826805083778417 8273402350370103812833813)
                ·
                  refine ⟨387815735173598616226585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8273402350370103812833813 387815735173598616226585)
                  ·
                    rfl

theorem cell22_3398708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_3398708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398708 prefixEnd_3398708 := by exact prefixLift 3398708
  have htrace : WordTrace (prefixWord ++ tailWord_3398708) baseStart_3398708 baseEnd_3398708 := by
    simpa [prefixWord, tailWord_3398708, baseEnd_3398708] using wordTrace_append hprefix tailTrace_3398708
  have hstable : (prefixWord ++ tailWord_3398708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398708).length < 2 ^ (prefixWord ++ tailWord_3398708).sum := by decide
  have hdescent : baseEnd_3398708 < baseStart_3398708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398779 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 1, 7]
def baseStart_3398779 : Nat := 118140960795 + 3398779 * 2 ^ 59
def prefixEnd_3398779 : Nat := 4983230072969 + 3 ^ 40 * 3398779 * 2
def baseEnd_3398779 : Nat := 1163471510271775330154537

theorem tailTrace_3398779 : CollatzResearch.WordTrace tailWord_3398779 prefixEnd_3398779 1163471510271775330154537 := by
  unfold tailWord_3398779
  simp only [CollatzResearch.WordTrace]
  refine ⟨123963654153811623085111391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82642436102541082056740927 123963654153811623085111391)
  ·
    refine ⟨185945481230717434627667087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123963654153811623085111391 185945481230717434627667087)
    ·
      refine ⟨278918221846076151941500631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185945481230717434627667087 278918221846076151941500631)
      ·
        refine ⟨418377332769114227912250947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278918221846076151941500631 418377332769114227912250947)
        ·
          refine ⟨627565999153671341868376421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418377332769114227912250947 627565999153671341868376421)
          ·
            refine ⟨117668624841313376600320579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 627565999153671341868376421 117668624841313376600320579)
            ·
              refine ⟨176502937261970064900480869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117668624841313376600320579 176502937261970064900480869)
              ·
                refine ⟨33094300736619387168840163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176502937261970064900480869 33094300736619387168840163)
                ·
                  refine ⟨49641451104929080753260245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33094300736619387168840163 49641451104929080753260245)
                  ·
                    refine ⟨1163471510271775330154537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49641451104929080753260245 1163471510271775330154537)
                    ·
                      rfl

theorem cell22_3398779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 7].length) (baseStart_3398779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398779 prefixEnd_3398779 := by exact prefixLift 3398779
  have htrace : WordTrace (prefixWord ++ tailWord_3398779) baseStart_3398779 baseEnd_3398779 := by
    simpa [prefixWord, tailWord_3398779, baseEnd_3398779] using wordTrace_append hprefix tailTrace_3398779
  have hstable : (prefixWord ++ tailWord_3398779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398779).length < 2 ^ (prefixWord ++ tailWord_3398779).sum := by decide
  have hdescent : baseEnd_3398779 < baseStart_3398779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398841 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 3, 5]
def baseStart_3398841 : Nat := 118140960795 + 3398841 * 2 ^ 59
def prefixEnd_3398841 : Nat := 4983230072969 + 3 ^ 40 * 3398841 * 2
def baseEnd_3398841 : Nat := 1163492734138827835104347

theorem tailTrace_3398841 : CollatzResearch.WordTrace tailWord_3398841 prefixEnd_3398841 1163492734138827835104347 := by
  unfold tailWord_3398841
  simp only [CollatzResearch.WordTrace]
  refine ⟨123965915479587007673868377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82643943653058005115912251 123965915479587007673868377)
  ·
    refine ⟨92974436609690255755401283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123965915479587007673868377 92974436609690255755401283)
    ·
      refine ⟨139461654914535383633101925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92974436609690255755401283 139461654914535383633101925)
      ·
        refine ⟨26149060296475384431206611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139461654914535383633101925 26149060296475384431206611)
        ·
          refine ⟨39223590444713076646809917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26149060296475384431206611 39223590444713076646809917)
          ·
            refine ⟨14708846416767403742553719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39223590444713076646809917 14708846416767403742553719)
            ·
              refine ⟨22063269625151105613830579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14708846416767403742553719 22063269625151105613830579)
              ·
                refine ⟨33094904437726658420745869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22063269625151105613830579 33094904437726658420745869)
                ·
                  refine ⟨12410589164147496907779701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33094904437726658420745869 12410589164147496907779701)
                  ·
                    refine ⟨1163492734138827835104347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12410589164147496907779701 1163492734138827835104347)
                    ·
                      rfl

theorem cell22_3398841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_3398841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398841 prefixEnd_3398841 := by exact prefixLift 3398841
  have htrace : WordTrace (prefixWord ++ tailWord_3398841) baseStart_3398841 baseEnd_3398841 := by
    simpa [prefixWord, tailWord_3398841, baseEnd_3398841] using wordTrace_append hprefix tailTrace_3398841
  have hstable : (prefixWord ++ tailWord_3398841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398841).length < 2 ^ (prefixWord ++ tailWord_3398841).sum := by decide
  have hdescent : baseEnd_3398841 < baseStart_3398841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398871 : List Nat := [1, 1, 3, 2, 1, 2, 5, 7]
def baseStart_3398871 : Nat := 118140960795 + 3398871 * 2 ^ 59
def prefixEnd_3398871 : Nat := 4983230072969 + 3 ^ 40 * 3398871 * 2
def baseEnd_3398871 : Nat := 129278111527990861872695

theorem tailTrace_3398871 : CollatzResearch.WordTrace tailWord_3398871 prefixEnd_3398871 129278111527990861872695 := by
  unfold tailWord_3398871
  simp only [CollatzResearch.WordTrace]
  refine ⟨123967009669478322797460467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82644673112985548531640311 123967009669478322797460467)
  ·
    refine ⟨185950514504217484196190701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123967009669478322797460467 185950514504217484196190701)
    ·
      refine ⟨69731442939081556573571513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185950514504217484196190701 69731442939081556573571513)
      ·
        refine ⟨52298582204311167430178635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69731442939081556573571513 52298582204311167430178635)
        ·
          refine ⟨78447873306466751145267953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52298582204311167430178635 78447873306466751145267953)
          ·
            refine ⟨58835904979850063358950965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78447873306466751145267953 58835904979850063358950965)
            ·
              refine ⟨5515866091860943439901653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58835904979850063358950965 5515866091860943439901653)
              ·
                refine ⟨129278111527990861872695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5515866091860943439901653 129278111527990861872695)
                ·
                  rfl

theorem cell22_3398871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 7].length) (baseStart_3398871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398871 prefixEnd_3398871 := by exact prefixLift 3398871
  have htrace : WordTrace (prefixWord ++ tailWord_3398871) baseStart_3398871 baseEnd_3398871 := by
    simpa [prefixWord, tailWord_3398871, baseEnd_3398871] using wordTrace_append hprefix tailTrace_3398871
  have hstable : (prefixWord ++ tailWord_3398871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398871).length < 2 ^ (prefixWord ++ tailWord_3398871).sum := by decide
  have hdescent : baseEnd_3398871 < baseStart_3398871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398888 : List Nat := [2, 1, 4, 1, 2, 1, 5, 6]
def baseStart_3398888 : Nat := 118140960795 + 3398888 * 2 ^ 59
def prefixEnd_3398888 : Nat := 4983230072969 + 3 ^ 40 * 3398888 * 2
def baseEnd_3398888 : Nat := 129278758133259486575467

theorem tailTrace_3398888 : CollatzResearch.WordTrace tailWord_3398888 prefixEnd_3398888 129278758133259486575467 := by
  unfold tailWord_3398888
  simp only [CollatzResearch.WordTrace]
  refine ⟨61983814855208367350414659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82645086473611156467219545 61983814855208367350414659)
  ·
    refine ⟨92975722282812551025621989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61983814855208367350414659 92975722282812551025621989)
    ·
      refine ⟨17432947928027353317304123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92975722282812551025621989 17432947928027353317304123)
      ·
        refine ⟨26149421892041029975956185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17432947928027353317304123 26149421892041029975956185)
        ·
          refine ⟨19612066419030772481967139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26149421892041029975956185 19612066419030772481967139)
          ·
            refine ⟨29418099628546158722950709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19612066419030772481967139 29418099628546158722950709)
            ·
              refine ⟨2757946840176202380276629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29418099628546158722950709 2757946840176202380276629)
              ·
                refine ⟨129278758133259486575467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2757946840176202380276629 129278758133259486575467)
                ·
                  rfl

theorem cell22_3398888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 6].length) (baseStart_3398888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398888 prefixEnd_3398888 := by exact prefixLift 3398888
  have htrace : WordTrace (prefixWord ++ tailWord_3398888) baseStart_3398888 baseEnd_3398888 := by
    simpa [prefixWord, tailWord_3398888, baseEnd_3398888] using wordTrace_append hprefix tailTrace_3398888
  have hstable : (prefixWord ++ tailWord_3398888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398888).length < 2 ^ (prefixWord ++ tailWord_3398888).sum := by decide
  have hdescent : baseEnd_3398888 < baseStart_3398888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398890 : List Nat := [3, 1, 3, 1, 1, 5, 1, 1, 2, 4]
def baseStart_3398890 : Nat := 118140960795 + 3398890 * 2 ^ 59
def prefixEnd_3398890 : Nat := 4983230072969 + 3 ^ 40 * 3398890 * 2
def baseEnd_3398890 : Nat := 1163509507840208040629197

theorem tailTrace_3398890 : CollatzResearch.WordTrace tailWord_3398890 prefixEnd_3398890 1163509507840208040629197 := by
  unfold tailWord_3398890
  simp only [CollatzResearch.WordTrace]
  refine ⟨30991925664102372260600531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82645135104272992694934749 30991925664102372260600531)
  ·
    refine ⟨46487888496153558390900797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30991925664102372260600531 46487888496153558390900797)
    ·
      refine ⟨17432958186057584396587799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46487888496153558390900797 17432958186057584396587799)
      ·
        refine ⟨26149437279086376594881699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17432958186057584396587799 26149437279086376594881699)
        ·
          refine ⟨39224155918629564892322549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26149437279086376594881699 39224155918629564892322549)
          ·
            refine ⟨3677264617371521708655239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39224155918629564892322549 3677264617371521708655239)
            ·
              refine ⟨5515896926057282562982859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3677264617371521708655239 5515896926057282562982859)
              ·
                refine ⟨8273845389085923844474289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5515896926057282562982859 8273845389085923844474289)
                ·
                  refine ⟨6205384041814442883355717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8273845389085923844474289 6205384041814442883355717)
                  ·
                    refine ⟨1163509507840208040629197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6205384041814442883355717 1163509507840208040629197)
                    ·
                      rfl

theorem cell22_3398890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_3398890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398890 prefixEnd_3398890 := by exact prefixLift 3398890
  have htrace : WordTrace (prefixWord ++ tailWord_3398890) baseStart_3398890 baseEnd_3398890 := by
    simpa [prefixWord, tailWord_3398890, baseEnd_3398890] using wordTrace_append hprefix tailTrace_3398890
  have hstable : (prefixWord ++ tailWord_3398890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398890).length < 2 ^ (prefixWord ++ tailWord_3398890).sum := by decide
  have hdescent : baseEnd_3398890 < baseStart_3398890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398954 : List Nat := [3, 1, 4, 2, 1, 1, 3, 3, 1, 3]
def baseStart_3398954 : Nat := 118140960795 + 3398954 * 2 ^ 59
def prefixEnd_3398954 : Nat := 4983230072969 + 3 ^ 40 * 3398954 * 2
def baseEnd_3398954 : Nat := 1163531416348133207029001

theorem tailTrace_3398954 : CollatzResearch.WordTrace tailWord_3398954 prefixEnd_3398954 1163531416348133207029001 := by
  unfold tailWord_3398954
  simp only [CollatzResearch.WordTrace]
  refine ⟨30992509232044406993182979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82646691285451751981821277 30992509232044406993182979)
  ·
    refine ⟨46488763848066610489774469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30992509232044406993182979 46488763848066610489774469)
    ·
      refine ⟨8716643221512489466832713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46488763848066610489774469 8716643221512489466832713)
      ·
        refine ⟨6537482416134367100124535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8716643221512489466832713 6537482416134367100124535)
        ·
          refine ⟨9806223624201550650186803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6537482416134367100124535 9806223624201550650186803)
          ·
            refine ⟨14709335436302325975280205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9806223624201550650186803 14709335436302325975280205)
            ·
              refine ⟨5516000788613372240730077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14709335436302325975280205 5516000788613372240730077)
              ·
                refine ⟨2068500295730014590273779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5516000788613372240730077 2068500295730014590273779)
                ·
                  refine ⟨3102750443595021885410669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2068500295730014590273779 3102750443595021885410669)
                  ·
                    refine ⟨1163531416348133207029001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3102750443595021885410669 1163531416348133207029001)
                    ·
                      rfl

theorem cell22_3398954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_3398954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398954 prefixEnd_3398954 := by exact prefixLift 3398954
  have htrace : WordTrace (prefixWord ++ tailWord_3398954) baseStart_3398954 baseEnd_3398954 := by
    simpa [prefixWord, tailWord_3398954, baseEnd_3398954] using wordTrace_append hprefix tailTrace_3398954
  have hstable : (prefixWord ++ tailWord_3398954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398954).length < 2 ^ (prefixWord ++ tailWord_3398954).sum := by decide
  have hdescent : baseEnd_3398954 < baseStart_3398954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398993 : List Nat := [1, 2, 2, 1, 4, 1, 2, 3, 1, 5]
def baseStart_3398993 : Nat := 118140960795 + 3398993 * 2 ^ 59
def prefixEnd_3398993 : Nat := 4983230072969 + 3 ^ 40 * 3398993 * 2
def baseEnd_3398993 : Nat := 1163544766845150105303881

theorem tailTrace_3398993 : CollatzResearch.WordTrace tailWord_3398993 prefixEnd_3398993 1163544766845150105303881 := by
  unfold tailWord_3398993
  simp only [CollatzResearch.WordTrace]
  refine ⟨123971459375036337633401633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82647639583357558422267755 123971459375036337633401633)
  ·
    refine ⟨92978594531277253225051225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123971459375036337633401633 92978594531277253225051225)
    ·
      refine ⟨69733945898457939918788419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92978594531277253225051225 69733945898457939918788419)
      ·
        refine ⟨104600918847686909878182629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69733945898457939918788419 104600918847686909878182629)
        ·
          refine ⟨19612672283941295602159243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104600918847686909878182629 19612672283941295602159243)
          ·
            refine ⟨29419008425911943403238865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19612672283941295602159243 29419008425911943403238865)
            ·
              refine ⟨22064256319433957552429149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29419008425911943403238865 22064256319433957552429149)
              ·
                refine ⟨8274096119787734082160931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22064256319433957552429149 8274096119787734082160931)
                ·
                  refine ⟨12411144179681601123241397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8274096119787734082160931 12411144179681601123241397)
                  ·
                    refine ⟨1163544766845150105303881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12411144179681601123241397 1163544766845150105303881)
                    ·
                      rfl

theorem cell22_3398993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_3398993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398993 prefixEnd_3398993 := by exact prefixLift 3398993
  have htrace : WordTrace (prefixWord ++ tailWord_3398993) baseStart_3398993 baseEnd_3398993 := by
    simpa [prefixWord, tailWord_3398993, baseEnd_3398993] using wordTrace_append hprefix tailTrace_3398993
  have hstable : (prefixWord ++ tailWord_3398993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398993).length < 2 ^ (prefixWord ++ tailWord_3398993).sum := by decide
  have hdescent : baseEnd_3398993 < baseStart_3398993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398997 : List Nat := [1, 3, 2, 2, 3, 3, 1, 2, 1, 4]
def baseStart_3398997 : Nat := 118140960795 + 3398997 * 2 ^ 59
def prefixEnd_3398997 : Nat := 4983230072969 + 3 ^ 40 * 3398997 * 2
def baseEnd_3398997 : Nat := 1163546136126895428203869

theorem tailTrace_3398997 : CollatzResearch.WordTrace tailWord_3398997 prefixEnd_3398997 1163546136126895428203869 := by
  unfold tailWord_3398997
  simp only [CollatzResearch.WordTrace]
  refine ⟨123971605267021846316547245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82647736844681230877698163 123971605267021846316547245)
  ·
    refine ⟨46489351975133192368705217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123971605267021846316547245 46489351975133192368705217)
    ·
      refine ⟨34867013981349894276528913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46489351975133192368705217 34867013981349894276528913)
      ·
        refine ⟨26150260486012420707396685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34867013981349894276528913 26150260486012420707396685)
        ·
          refine ⟨9806347682254657765273757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26150260486012420707396685 9806347682254657765273757)
          ·
            refine ⟨3677380380845496661977659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9806347682254657765273757 3677380380845496661977659)
            ·
              refine ⟨5516070571268244992966489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3677380380845496661977659 5516070571268244992966489)
              ·
                refine ⟨4137052928451183744724867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5516070571268244992966489 4137052928451183744724867)
                ·
                  refine ⟨6205579392676775617087301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4137052928451183744724867 6205579392676775617087301)
                  ·
                    refine ⟨1163546136126895428203869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6205579392676775617087301 1163546136126895428203869)
                    ·
                      rfl

theorem cell22_3398997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_3398997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3398997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3398997 prefixEnd_3398997 := by exact prefixLift 3398997
  have htrace : WordTrace (prefixWord ++ tailWord_3398997) baseStart_3398997 baseEnd_3398997 := by
    simpa [prefixWord, tailWord_3398997, baseEnd_3398997] using wordTrace_append hprefix tailTrace_3398997
  have hstable : (prefixWord ++ tailWord_3398997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398997).length < 2 ^ (prefixWord ++ tailWord_3398997).sum := by decide
  have hdescent : baseEnd_3398997 < baseStart_3398997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399010 : List Nat := [3, 3, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_3399010 : Nat := 118140960795 + 3399010 * 2 ^ 59
def prefixEnd_3399010 : Nat := 4983230072969 + 3 ^ 40 * 3399010 * 2
def baseEnd_3399010 : Nat := 1163550586292567727628829

theorem tailTrace_3399010 : CollatzResearch.WordTrace tailWord_3399010 prefixEnd_3399010 1163550586292567727628829 := by
  unfold tailWord_3399010
  simp only [CollatzResearch.WordTrace]
  refine ⟨30993019853993687384192621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82648052943983166357846989 30993019853993687384192621)
  ·
    refine ⟨11622382445247632769072233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30993019853993687384192621 11622382445247632769072233)
    ·
      refine ⟨8716786833935724576804175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11622382445247632769072233 8716786833935724576804175)
      ·
        refine ⟨13075180250903586865206263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8716786833935724576804175 13075180250903586865206263)
        ·
          refine ⟨19612770376355380297809395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13075180250903586865206263 19612770376355380297809395)
          ·
            refine ⟨29419155564533070446714093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19612770376355380297809395 29419155564533070446714093)
            ·
              refine ⟨11032183336699901417517785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29419155564533070446714093 11032183336699901417517785)
              ·
                refine ⟨8274137502524926063138339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11032183336699901417517785 8274137502524926063138339)
                ·
                  refine ⟨12411206253787389094707509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8274137502524926063138339 12411206253787389094707509)
                  ·
                    refine ⟨1163550586292567727628829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12411206253787389094707509 1163550586292567727628829)
                    ·
                      rfl

theorem cell22_3399010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_3399010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399010 prefixEnd_3399010 := by exact prefixLift 3399010
  have htrace : WordTrace (prefixWord ++ tailWord_3399010) baseStart_3399010 baseEnd_3399010 := by
    simpa [prefixWord, tailWord_3399010, baseEnd_3399010] using wordTrace_append hprefix tailTrace_3399010
  have hstable : (prefixWord ++ tailWord_3399010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399010).length < 2 ^ (prefixWord ++ tailWord_3399010).sum := by decide
  have hdescent : baseEnd_3399010 < baseStart_3399010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399115 : List Nat := [1, 1, 1, 1, 3, 3, 3, 4, 1, 4]
def baseStart_3399115 : Nat := 118140960795 + 3399115 * 2 ^ 59
def prefixEnd_3399115 : Nat := 4983230072969 + 3 ^ 40 * 3399115 * 2
def baseEnd_3399115 : Nat := 1163586529938382453753507

theorem tailTrace_3399115 : CollatzResearch.WordTrace tailWord_3399115 prefixEnd_3399115 1163586529938382453753507 := by
  unfold tailWord_3399115
  simp only [CollatzResearch.WordTrace]
  refine ⟨123975909080594352469342799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82650606053729568312895199 123975909080594352469342799)
  ·
    refine ⟨185963863620891528704014199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123975909080594352469342799 185963863620891528704014199)
    ·
      refine ⟨278945795431337293056021299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185963863620891528704014199 278945795431337293056021299)
      ·
        refine ⟨418418693147005939584031949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278945795431337293056021299 418418693147005939584031949)
        ·
          refine ⟨156907009930127227344011981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418418693147005939584031949 156907009930127227344011981)
          ·
            refine ⟨58840128723797710254004493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156907009930127227344011981 58840128723797710254004493)
            ·
              refine ⟨22065048271424141345251685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58840128723797710254004493 22065048271424141345251685)
              ·
                refine ⟨4137196550892026502234691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22065048271424141345251685 4137196550892026502234691)
                ·
                  refine ⟨6205794826338039753352037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4137196550892026502234691 6205794826338039753352037)
                  ·
                    refine ⟨1163586529938382453753507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6205794826338039753352037 1163586529938382453753507)
                    ·
                      rfl

theorem cell22_3399115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 4].length) (baseStart_3399115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399115 prefixEnd_3399115 := by exact prefixLift 3399115
  have htrace : WordTrace (prefixWord ++ tailWord_3399115) baseStart_3399115 baseEnd_3399115 := by
    simpa [prefixWord, tailWord_3399115, baseEnd_3399115] using wordTrace_append hprefix tailTrace_3399115
  have hstable : (prefixWord ++ tailWord_3399115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399115).length < 2 ^ (prefixWord ++ tailWord_3399115).sum := by decide
  have hdescent : baseEnd_3399115 < baseStart_3399115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399162 : List Nat := [3, 1, 1, 1, 1, 2, 5, 3, 2, 3]
def baseStart_3399162 : Nat := 118140960795 + 3399162 * 2 ^ 59
def prefixEnd_3399162 : Nat := 4983230072969 + 3 ^ 40 * 3399162 * 2
def baseEnd_3399162 : Nat := 1163602618998889997828363

theorem tailTrace_3399162 : CollatzResearch.WordTrace tailWord_3399162 prefixEnd_3399162 1163602618998889997828363 := by
  unfold tailWord_3399162
  simp only [CollatzResearch.WordTrace]
  refine ⟨30994405827856019874075935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82651748874282719664202493 30994405827856019874075935)
  ·
    refine ⟨46491608741784029811113903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30994405827856019874075935 46491608741784029811113903)
    ·
      refine ⟨69737413112676044716670855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46491608741784029811113903 69737413112676044716670855)
      ·
        refine ⟨104606119669014067075006283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69737413112676044716670855 104606119669014067075006283)
        ·
          refine ⟨156909179503521100612509425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104606119669014067075006283 156909179503521100612509425)
          ·
            refine ⟨117681884627640825459382069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156909179503521100612509425 117681884627640825459382069)
            ·
              refine ⟨11032676683841327386817069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117681884627640825459382069 11032676683841327386817069)
              ·
                refine ⟨4137253756440497770056401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11032676683841327386817069 4137253756440497770056401)
                ·
                  refine ⟨3102940317330373327542301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4137253756440497770056401 3102940317330373327542301)
                  ·
                    refine ⟨1163602618998889997828363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3102940317330373327542301 1163602618998889997828363)
                    ·
                      rfl

theorem cell22_3399162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_3399162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399162 prefixEnd_3399162 := by exact prefixLift 3399162
  have htrace : WordTrace (prefixWord ++ tailWord_3399162) baseStart_3399162 baseEnd_3399162 := by
    simpa [prefixWord, tailWord_3399162, baseEnd_3399162] using wordTrace_append hprefix tailTrace_3399162
  have hstable : (prefixWord ++ tailWord_3399162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399162).length < 2 ^ (prefixWord ++ tailWord_3399162).sum := by decide
  have hdescent : baseEnd_3399162 < baseStart_3399162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399175 : List Nat := [1, 1, 4, 3, 2, 1, 2, 8]
def baseStart_3399175 : Nat := 118140960795 + 3399175 * 2 ^ 59
def prefixEnd_3399175 : Nat := 4983230072969 + 3 ^ 40 * 3399175 * 2
def baseEnd_3399175 : Nat := 129289674351618033028147

theorem tailTrace_3399175 : CollatzResearch.WordTrace tailWord_3399175 prefixEnd_3399175 129289674351618033028147 := by
  unfold tailWord_3399175
  simp only [CollatzResearch.WordTrace]
  refine ⟨123978097460376982716526979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82652064973584655144351319 123978097460376982716526979)
  ·
    refine ⟨185967146190565474074790469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123978097460376982716526979 185967146190565474074790469)
    ·
      refine ⟨34868839910731026389023213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185967146190565474074790469 34868839910731026389023213)
      ·
        refine ⟨13075814966524134895883705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34868839910731026389023213 13075814966524134895883705)
        ·
          refine ⟨9806861224893101171912779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13075814966524134895883705 9806861224893101171912779)
          ·
            refine ⟨14710291837339651757869169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9806861224893101171912779 14710291837339651757869169)
            ·
              refine ⟨11032718878004738818401877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14710291837339651757869169 11032718878004738818401877)
              ·
                refine ⟨129289674351618033028147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11032718878004738818401877 129289674351618033028147)
                ·
                  rfl

theorem cell22_3399175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 8].length) (baseStart_3399175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399175 prefixEnd_3399175 := by exact prefixLift 3399175
  have htrace : WordTrace (prefixWord ++ tailWord_3399175) baseStart_3399175 baseEnd_3399175 := by
    simpa [prefixWord, tailWord_3399175, baseEnd_3399175] using wordTrace_append hprefix tailTrace_3399175
  have hstable : (prefixWord ++ tailWord_3399175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399175).length < 2 ^ (prefixWord ++ tailWord_3399175).sum := by decide
  have hdescent : baseEnd_3399175 < baseStart_3399175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399282 : List Nat := [3, 2, 1, 2, 3, 1, 2, 2, 6]
def baseStart_3399282 : Nat := 118140960795 + 3399282 * 2 ^ 59
def prefixEnd_3399282 : Nat := 4983230072969 + 3 ^ 40 * 3399282 * 2
def baseEnd_3399282 : Nat := 387881232483749894942665

theorem tailTrace_3399282 : CollatzResearch.WordTrace tailWord_3399282 prefixEnd_3399282 387881232483749894942665 := by
  unfold tailWord_3399282
  simp only [CollatzResearch.WordTrace]
  refine ⟨30995500017747334997668025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82654666713992893327114733 30995500017747334997668025)
  ·
    refine ⟨23246625013310501248251019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30995500017747334997668025 23246625013310501248251019)
    ·
      refine ⟨34869937519965751872376529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23246625013310501248251019 34869937519965751872376529)
      ·
        refine ⟨26152453139974313904282397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34869937519965751872376529 26152453139974313904282397)
        ·
          refine ⟨9807169927490367714105899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26152453139974313904282397 9807169927490367714105899)
          ·
            refine ⟨14710754891235551571158849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9807169927490367714105899 14710754891235551571158849)
            ·
              refine ⟨11033066168426663678369137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14710754891235551571158849 11033066168426663678369137)
              ·
                refine ⟨8274799626319997758776853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11033066168426663678369137 8274799626319997758776853)
                ·
                  refine ⟨387881232483749894942665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8274799626319997758776853 387881232483749894942665)
                  ·
                    rfl

theorem cell22_3399282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_3399282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399282 prefixEnd_3399282 := by exact prefixLift 3399282
  have htrace : WordTrace (prefixWord ++ tailWord_3399282) baseStart_3399282 baseEnd_3399282 := by
    simpa [prefixWord, tailWord_3399282, baseEnd_3399282] using wordTrace_append hprefix tailTrace_3399282
  have hstable : (prefixWord ++ tailWord_3399282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399282).length < 2 ^ (prefixWord ++ tailWord_3399282).sum := by decide
  have hdescent : baseEnd_3399282 < baseStart_3399282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399316 : List Nat := [2, 4, 2, 2, 2, 2, 1, 1, 6]
def baseStart_3399316 : Nat := 118140960795 + 3399316 * 2 ^ 59
def prefixEnd_3399316 : Nat := 4983230072969 + 3 ^ 40 * 3399316 * 2
def baseEnd_3399316 : Nat := 387885112115361643159297

theorem tailTrace_3399316 : CollatzResearch.WordTrace tailWord_3399316 prefixEnd_3399316 387885112115361643159297 := by
  unfold tailWord_3399316
  simp only [CollatzResearch.WordTrace]
  refine ⟨61991620076433081898704901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82655493435244109198273201 61991620076433081898704901)
  ·
    refine ⟨11623428764331202856007169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61991620076433081898704901 11623428764331202856007169)
    ·
      refine ⟨8717571573248402142005377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11623428764331202856007169 8717571573248402142005377)
      ·
        refine ⟨6538178679936301606504033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8717571573248402142005377 6538178679936301606504033)
        ·
          refine ⟨4903634009952226204878025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6538178679936301606504033 4903634009952226204878025)
          ·
            refine ⟨3677725507464169653658519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4903634009952226204878025 3677725507464169653658519)
            ·
              refine ⟨5516588261196254480487779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3677725507464169653658519 5516588261196254480487779)
              ·
                refine ⟨8274882391794381720731669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5516588261196254480487779 8274882391794381720731669)
                ·
                  refine ⟨387885112115361643159297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8274882391794381720731669 387885112115361643159297)
                  ·
                    rfl

theorem cell22_3399316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_3399316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399316 prefixEnd_3399316 := by exact prefixLift 3399316
  have htrace : WordTrace (prefixWord ++ tailWord_3399316) baseStart_3399316 baseEnd_3399316 := by
    simpa [prefixWord, tailWord_3399316, baseEnd_3399316] using wordTrace_append hprefix tailTrace_3399316
  have hstable : (prefixWord ++ tailWord_3399316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399316).length < 2 ^ (prefixWord ++ tailWord_3399316).sum := by decide
  have hdescent : baseEnd_3399316 < baseStart_3399316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399355 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 9]
def baseStart_3399355 : Nat := 118140960795 + 3399355 * 2 ^ 59
def prefixEnd_3399355 : Nat := 4983230072969 + 3 ^ 40 * 3399355 * 2
def baseEnd_3399355 : Nat := 387889562281033942584257

theorem tailTrace_3399355 : CollatzResearch.WordTrace tailWord_3399355 prefixEnd_3399355 387889562281033942584257 := by
  unfold tailWord_3399355
  simp only [CollatzResearch.WordTrace]
  refine ⟨123984662599724873458079519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82656441733149915638719679 123984662599724873458079519)
  ·
    refine ⟨185976993899587310187119279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123984662599724873458079519 185976993899587310187119279)
    ·
      refine ⟨278965490849380965280678919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185976993899587310187119279 278965490849380965280678919)
      ·
        refine ⟨418448236274071447921018379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278965490849380965280678919 418448236274071447921018379)
        ·
          refine ⟨627672354411107171881527569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418448236274071447921018379 627672354411107171881527569)
          ·
            refine ⟨470754265808330378911145677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 627672354411107171881527569 470754265808330378911145677)
            ·
              refine ⟨176532849678123892091679629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 470754265808330378911145677 176532849678123892091679629)
              ·
                refine ⟨66199818629296459534379861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176532849678123892091679629 66199818629296459534379861)
                ·
                  refine ⟨387889562281033942584257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66199818629296459534379861 387889562281033942584257)
                  ·
                    rfl

theorem cell22_3399355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 9].length) (baseStart_3399355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399355 prefixEnd_3399355 := by exact prefixLift 3399355
  have htrace : WordTrace (prefixWord ++ tailWord_3399355) baseStart_3399355 baseEnd_3399355 := by
    simpa [prefixWord, tailWord_3399355, baseEnd_3399355] using wordTrace_append hprefix tailTrace_3399355
  have hstable : (prefixWord ++ tailWord_3399355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399355).length < 2 ^ (prefixWord ++ tailWord_3399355).sum := by decide
  have hdescent : baseEnd_3399355 < baseStart_3399355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399434 : List Nat := [3, 1, 2, 2, 1, 4, 2, 1, 6]
def baseStart_3399434 : Nat := 118140960795 + 3399434 * 2 ^ 59
def prefixEnd_3399434 : Nat := 4983230072969 + 3 ^ 40 * 3399434 * 2
def baseEnd_3399434 : Nat := 387898576719190651675843

theorem tailTrace_3399434 : CollatzResearch.WordTrace tailWord_3399434 prefixEnd_3399434 387898576719190651675843 := by
  unfold tailWord_3399434
  simp only [CollatzResearch.WordTrace]
  refine ⟨30996885991609667487551339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82658362644292446633470237 30996885991609667487551339)
  ·
    refine ⟨46495328987414501231327009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30996885991609667487551339 46495328987414501231327009)
    ·
      refine ⟨34871496740560875923495257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46495328987414501231327009 34871496740560875923495257)
      ·
        refine ⟨26153622555420656942621443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34871496740560875923495257 26153622555420656942621443)
        ·
          refine ⟨39230433833130985413932165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26153622555420656942621443 39230433833130985413932165)
          ·
            refine ⟨7355706343712059765112281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39230433833130985413932165 7355706343712059765112281)
            ·
              refine ⟨5516779757784044823834211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7355706343712059765112281 5516779757784044823834211)
              ·
                refine ⟨8275169636676067235751317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5516779757784044823834211 8275169636676067235751317)
                ·
                  refine ⟨387898576719190651675843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8275169636676067235751317 387898576719190651675843)
                  ·
                    rfl

theorem cell22_3399434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_3399434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399434 prefixEnd_3399434 := by exact prefixLift 3399434
  have htrace : WordTrace (prefixWord ++ tailWord_3399434) baseStart_3399434 baseEnd_3399434 := by
    simpa [prefixWord, tailWord_3399434, baseEnd_3399434] using wordTrace_append hprefix tailTrace_3399434
  have hstable : (prefixWord ++ tailWord_3399434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399434).length < 2 ^ (prefixWord ++ tailWord_3399434).sum := by decide
  have hdescent : baseEnd_3399434 < baseStart_3399434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399464 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 1, 6]
def baseStart_3399464 : Nat := 118140960795 + 3399464 * 2 ^ 59
def prefixEnd_3399464 : Nat := 4983230072969 + 3 ^ 40 * 3399464 * 2
def baseEnd_3399464 : Nat := 1163705999770661876777437

theorem tailTrace_3399464 : CollatzResearch.WordTrace tailWord_3399464 prefixEnd_3399464 1163705999770661876777437 := by
  unfold tailWord_3399464
  simp only [CollatzResearch.WordTrace]
  refine ⟨61994319078164992536898723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82659092104219990049198297 61994319078164992536898723)
  ·
    refine ⟨92991478617247488805348085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61994319078164992536898723 92991478617247488805348085)
    ·
      refine ⟨8717951120366952075501383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92991478617247488805348085 8717951120366952075501383)
      ·
        refine ⟨13076926680550428113252075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8717951120366952075501383 13076926680550428113252075)
        ·
          refine ⟨19615390020825642169878113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13076926680550428113252075 19615390020825642169878113)
          ·
            refine ⟨14711542515619231627408585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19615390020825642169878113 14711542515619231627408585)
            ·
              refine ⟨11033656886714423720556439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14711542515619231627408585 11033656886714423720556439)
              ·
                refine ⟨16550485330071635580834659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11033656886714423720556439 16550485330071635580834659)
                ·
                  refine ⟨24825727995107453371251989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16550485330071635580834659 24825727995107453371251989)
                  ·
                    refine ⟨1163705999770661876777437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24825727995107453371251989 1163705999770661876777437)
                    ·
                      rfl

theorem cell22_3399464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_3399464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399464 prefixEnd_3399464 := by exact prefixLift 3399464
  have htrace : WordTrace (prefixWord ++ tailWord_3399464) baseStart_3399464 baseEnd_3399464 := by
    simpa [prefixWord, tailWord_3399464, baseEnd_3399464] using wordTrace_append hprefix tailTrace_3399464
  have hstable : (prefixWord ++ tailWord_3399464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399464).length < 2 ^ (prefixWord ++ tailWord_3399464).sum := by decide
  have hdescent : baseEnd_3399464 < baseStart_3399464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399500 : List Nat := [2, 2, 1, 3, 4, 2, 2, 1, 2, 3]
def baseStart_3399500 : Nat := 118140960795 + 3399500 * 2 ^ 59
def prefixEnd_3399500 : Nat := 4983230072969 + 3 ^ 40 * 3399500 * 2
def baseEnd_3399500 : Nat := 1163718323306369782877327

theorem tailTrace_3399500 : CollatzResearch.WordTrace tailWord_3399500 prefixEnd_3399500 1163718323306369782877327 := by
  unfold tailWord_3399500
  simp only [CollatzResearch.WordTrace]
  refine ⟨61994975592099781611053977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82659967456133042148071969 61994975592099781611053977)
  ·
    refine ⟨46496231694074836208290483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61994975592099781611053977 46496231694074836208290483)
    ·
      refine ⟨69744347541112254312435725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46496231694074836208290483 69744347541112254312435725)
      ·
        refine ⟨26154130327917095367163397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69744347541112254312435725 26154130327917095367163397)
        ·
          refine ⟨4903899436484455381343137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26154130327917095367163397 4903899436484455381343137)
          ·
            refine ⟨3677924577363341536007353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4903899436484455381343137 3677924577363341536007353)
            ·
              refine ⟨2758443433022506152005515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3677924577363341536007353 2758443433022506152005515)
              ·
                refine ⟨4137665149533759228008273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758443433022506152005515 4137665149533759228008273)
                ·
                  refine ⟨3103248862150319421006205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4137665149533759228008273 3103248862150319421006205)
                  ·
                    refine ⟨1163718323306369782877327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3103248862150319421006205 1163718323306369782877327)
                    ·
                      rfl

theorem cell22_3399500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 2, 3].length) (baseStart_3399500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399500 prefixEnd_3399500 := by exact prefixLift 3399500
  have htrace : WordTrace (prefixWord ++ tailWord_3399500) baseStart_3399500 baseEnd_3399500 := by
    simpa [prefixWord, tailWord_3399500, baseEnd_3399500] using wordTrace_append hprefix tailTrace_3399500
  have hstable : (prefixWord ++ tailWord_3399500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399500).length < 2 ^ (prefixWord ++ tailWord_3399500).sum := by decide
  have hdescent : baseEnd_3399500 < baseStart_3399500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399528 : List Nat := [2, 1, 4, 2, 1, 1, 2, 5, 1, 3]
def baseStart_3399528 : Nat := 118140960795 + 3399528 * 2 ^ 59
def prefixEnd_3399528 : Nat := 4983230072969 + 3 ^ 40 * 3399528 * 2
def baseEnd_3399528 : Nat := 1163727908278587043177241

theorem tailTrace_3399528 : CollatzResearch.WordTrace tailWord_3399528 prefixEnd_3399528 1163727908278587043177241 := by
  unfold tailWord_3399528
  simp only [CollatzResearch.WordTrace]
  refine ⟨61995486214049062002063619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82660648285398749336084825 61995486214049062002063619)
  ·
    refine ⟨92993229321073593003095429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61995486214049062002063619 92993229321073593003095429)
    ·
      refine ⟨17436230497701298688080393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92993229321073593003095429 17436230497701298688080393)
      ·
        refine ⟨13077172873275974016060295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17436230497701298688080393 13077172873275974016060295)
        ·
          refine ⟨19615759309913961024090443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13077172873275974016060295 19615759309913961024090443)
          ·
            refine ⟨29423638964870941536135665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19615759309913961024090443 29423638964870941536135665)
            ·
              refine ⟨22067729223653206152101749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29423638964870941536135665 22067729223653206152101749)
              ·
                refine ⟨2068849614717488076759539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22067729223653206152101749 2068849614717488076759539)
                ·
                  refine ⟨3103274422076232115139309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2068849614717488076759539 3103274422076232115139309)
                  ·
                    refine ⟨1163727908278587043177241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3103274422076232115139309 1163727908278587043177241)
                    ·
                      rfl

theorem cell22_3399528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_3399528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399528 prefixEnd_3399528 := by exact prefixLift 3399528
  have htrace : WordTrace (prefixWord ++ tailWord_3399528) baseStart_3399528 baseEnd_3399528 := by
    simpa [prefixWord, tailWord_3399528, baseEnd_3399528] using wordTrace_append hprefix tailTrace_3399528
  have hstable : (prefixWord ++ tailWord_3399528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399528).length < 2 ^ (prefixWord ++ tailWord_3399528).sum := by decide
  have hdescent : baseEnd_3399528 < baseStart_3399528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399541 : List Nat := [1, 3, 4, 1, 1, 1, 4, 2, 5]
def baseStart_3399541 : Nat := 118140960795 + 3399541 * 2 ^ 59
def prefixEnd_3399541 : Nat := 4983230072969 + 3 ^ 40 * 3399541 * 2
def baseEnd_3399541 : Nat := 387910786148086447534067

theorem tailTrace_3399541 : CollatzResearch.WordTrace tailWord_3399541 prefixEnd_3399541 387910786148086447534067 := by
  unfold tailWord_3399541
  simp only [CollatzResearch.WordTrace]
  refine ⟨123991446577051027224350477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82660964384700684816233651 123991446577051027224350477)
  ·
    refine ⟨46496792466394135209131429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123991446577051027224350477 46496792466394135209131429)
    ·
      refine ⟨8718148587448900351712143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46496792466394135209131429 8718148587448900351712143)
      ·
        refine ⟨13077222881173350527568215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8718148587448900351712143 13077222881173350527568215)
        ·
          refine ⟨19615834321760025791352323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13077222881173350527568215 19615834321760025791352323)
          ·
            refine ⟨29423751482640038687028485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19615834321760025791352323 29423751482640038687028485)
            ·
              refine ⟨5516953402995007253817841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29423751482640038687028485 5516953402995007253817841)
              ·
                refine ⟨4137715052246255440363381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5516953402995007253817841 4137715052246255440363381)
                ·
                  refine ⟨387910786148086447534067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4137715052246255440363381 387910786148086447534067)
                  ·
                    rfl

theorem cell22_3399541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_3399541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399541 prefixEnd_3399541 := by exact prefixLift 3399541
  have htrace : WordTrace (prefixWord ++ tailWord_3399541) baseStart_3399541 baseEnd_3399541 := by
    simpa [prefixWord, tailWord_3399541, baseEnd_3399541] using wordTrace_append hprefix tailTrace_3399541
  have hstable : (prefixWord ++ tailWord_3399541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399541).length < 2 ^ (prefixWord ++ tailWord_3399541).sum := by decide
  have hdescent : baseEnd_3399541 < baseStart_3399541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399588 : List Nat := [2, 3, 1, 2, 1, 3, 4, 1, 1, 4]
def baseStart_3399588 : Nat := 118140960795 + 3399588 * 2 ^ 59
def prefixEnd_3399588 : Nat := 4983230072969 + 3 ^ 40 * 3399588 * 2
def baseEnd_3399588 : Nat := 1163748447504766886677057

theorem tailTrace_3399588 : CollatzResearch.WordTrace tailWord_3399588 prefixEnd_3399588 1163748447504766886677057 := by
  unfold tailWord_3399588
  simp only [CollatzResearch.WordTrace]
  refine ⟨61996580403940377125655709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82662107205253836167540945 61996580403940377125655709)
  ·
    refine ⟨23248717651477641422120891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61996580403940377125655709 23248717651477641422120891)
    ·
      refine ⟨34873076477216462133181337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23248717651477641422120891 34873076477216462133181337)
      ·
        refine ⟨26154807357912346599886003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34873076477216462133181337 26154807357912346599886003)
        ·
          refine ⟨39232211036868519899829005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26154807357912346599886003 39232211036868519899829005)
          ·
            refine ⟨14712079138825694962435877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39232211036868519899829005 14712079138825694962435877)
            ·
              refine ⟨2758514838529817805456727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14712079138825694962435877 2758514838529817805456727)
              ·
                refine ⟨4137772257794726708185091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758514838529817805456727 4137772257794726708185091)
                ·
                  refine ⟨6206658386692090062277637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4137772257794726708185091 6206658386692090062277637)
                  ·
                    refine ⟨1163748447504766886677057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6206658386692090062277637 1163748447504766886677057)
                    ·
                      rfl

theorem cell22_3399588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_3399588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399588 prefixEnd_3399588 := by exact prefixLift 3399588
  have htrace : WordTrace (prefixWord ++ tailWord_3399588) baseStart_3399588 baseEnd_3399588 := by
    simpa [prefixWord, tailWord_3399588, baseEnd_3399588] using wordTrace_append hprefix tailTrace_3399588
  have hstable : (prefixWord ++ tailWord_3399588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399588).length < 2 ^ (prefixWord ++ tailWord_3399588).sum := by decide
  have hdescent : baseEnd_3399588 < baseStart_3399588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399592 : List Nat := [2, 1, 6, 2, 2, 1, 1, 2, 5]
def baseStart_3399592 : Nat := 118140960795 + 3399592 * 2 ^ 59
def prefixEnd_3399592 : Nat := 4983230072969 + 3 ^ 40 * 3399592 * 2
def baseEnd_3399592 : Nat := 387916605595504069859015

theorem tailTrace_3399592 : CollatzResearch.WordTrace tailWord_3399592 prefixEnd_3399592 387916605595504069859015 := by
  unfold tailWord_3399592
  simp only [CollatzResearch.WordTrace]
  refine ⟨61996653349933131467228515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82662204466577508622971353 61996653349933131467228515)
  ·
    refine ⟨92994980024899697200842773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61996653349933131467228515 92994980024899697200842773)
    ·
      refine ⟨4359139688667173306289505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 92994980024899697200842773 4359139688667173306289505)
      ·
        refine ⟨3269354766500379979717129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4359139688667173306289505 3269354766500379979717129)
        ·
          refine ⟨2452016074875284984787847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3269354766500379979717129 2452016074875284984787847)
          ·
            refine ⟨3678024112312927477181771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2452016074875284984787847 3678024112312927477181771)
            ·
              refine ⟨5517036168469391215772657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3678024112312927477181771 5517036168469391215772657)
              ·
                refine ⟨4137777126352043411829493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5517036168469391215772657 4137777126352043411829493)
                ·
                  refine ⟨387916605595504069859015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4137777126352043411829493 387916605595504069859015)
                  ·
                    rfl

theorem cell22_3399592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 5].length) (baseStart_3399592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399592 prefixEnd_3399592 := by exact prefixLift 3399592
  have htrace : WordTrace (prefixWord ++ tailWord_3399592) baseStart_3399592 baseEnd_3399592 := by
    simpa [prefixWord, tailWord_3399592, baseEnd_3399592] using wordTrace_append hprefix tailTrace_3399592
  have hstable : (prefixWord ++ tailWord_3399592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399592).length < 2 ^ (prefixWord ++ tailWord_3399592).sum := by decide
  have hdescent : baseEnd_3399592 < baseStart_3399592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399599 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 4, 4]
def baseStart_3399599 : Nat := 118140960795 + 3399599 * 2 ^ 59
def prefixEnd_3399599 : Nat := 4983230072969 + 3 ^ 40 * 3399599 * 2
def baseEnd_3399599 : Nat := 1163752213029566524652023

theorem tailTrace_3399599 : CollatzResearch.WordTrace tailWord_3399599 prefixEnd_3399599 1163752213029566524652023 := by
  unfold tailWord_3399599
  simp only [CollatzResearch.WordTrace]
  refine ⟨123993562010840903129961851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82662374673893935419974567 123993562010840903129961851)
  ·
    refine ⟨185990343016261354694942777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123993562010840903129961851 185990343016261354694942777)
    ·
      refine ⟨139492757262196016021207083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185990343016261354694942777 139492757262196016021207083)
      ·
        refine ⟨209239135893294024031810625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139492757262196016021207083 209239135893294024031810625)
        ·
          refine ⟨156929351919970518023857969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209239135893294024031810625 156929351919970518023857969)
          ·
            refine ⟨117697013939977888517893477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156929351919970518023857969 117697013939977888517893477)
            ·
              refine ⟨22068190113745854097105027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117697013939977888517893477 22068190113745854097105027)
              ·
                refine ⟨33102285170618781145657541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22068190113745854097105027 33102285170618781145657541)
                ·
                  refine ⟨6206678469491021464810789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33102285170618781145657541 6206678469491021464810789)
                  ·
                    refine ⟨1163752213029566524652023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6206678469491021464810789 1163752213029566524652023)
                    ·
                      rfl

theorem cell22_3399599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 4].length) (baseStart_3399599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399599 prefixEnd_3399599 := by exact prefixLift 3399599
  have htrace : WordTrace (prefixWord ++ tailWord_3399599) baseStart_3399599 baseEnd_3399599 := by
    simpa [prefixWord, tailWord_3399599, baseEnd_3399599] using wordTrace_append hprefix tailTrace_3399599
  have hstable : (prefixWord ++ tailWord_3399599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399599).length < 2 ^ (prefixWord ++ tailWord_3399599).sum := by decide
  have hdescent : baseEnd_3399599 < baseStart_3399599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399650 : List Nat := [3, 3, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_3399650 : Nat := 118140960795 + 3399650 * 2 ^ 59
def prefixEnd_3399650 : Nat := 4983230072969 + 3 ^ 40 * 3399650 * 2
def baseEnd_3399650 : Nat := 1163769671371819391626867

theorem tailTrace_3399650 : CollatzResearch.WordTrace tailWord_3399650 prefixEnd_3399650 1163769671371819391626867 := by
  unfold tailWord_3399650
  simp only [CollatzResearch.WordTrace]
  refine ⟨30998855533414034710017101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82663614755770759226712269 30998855533414034710017101)
  ·
    refine ⟨11624570825030263016256413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30998855533414034710017101 11624570825030263016256413)
    ·
      refine ⟨4359214059386348631096155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11624570825030263016256413 4359214059386348631096155)
      ·
        refine ⟨6538821089079522946644233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4359214059386348631096155 6538821089079522946644233)
        ·
          refine ⟨4904115816809642209983175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6538821089079522946644233 4904115816809642209983175)
          ·
            refine ⟨7356173725214463314974763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4904115816809642209983175 7356173725214463314974763)
            ·
              refine ⟨11034260587821694972462145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7356173725214463314974763 11034260587821694972462145)
              ·
                refine ⟨8275695440866271229346609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11034260587821694972462145 8275695440866271229346609)
                ·
                  refine ⟨6206771580649703422009957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8275695440866271229346609 6206771580649703422009957)
                  ·
                    refine ⟨1163769671371819391626867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6206771580649703422009957 1163769671371819391626867)
                    ·
                      rfl

theorem cell22_3399650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_3399650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399650 prefixEnd_3399650 := by exact prefixLift 3399650
  have htrace : WordTrace (prefixWord ++ tailWord_3399650) baseStart_3399650 baseEnd_3399650 := by
    simpa [prefixWord, tailWord_3399650, baseEnd_3399650] using wordTrace_append hprefix tailTrace_3399650
  have hstable : (prefixWord ++ tailWord_3399650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399650).length < 2 ^ (prefixWord ++ tailWord_3399650).sum := by decide
  have hdescent : baseEnd_3399650 < baseStart_3399650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399676 : List Nat := [2, 2, 2, 1, 2, 2, 3, 3, 5]
def baseStart_3399676 : Nat := 118140960795 + 3399676 * 2 ^ 59
def prefixEnd_3399676 : Nat := 4983230072969 + 3 ^ 40 * 3399676 * 2
def baseEnd_3399676 : Nat := 387926190567721330158929

theorem tailTrace_3399676 : CollatzResearch.WordTrace tailWord_3399676 prefixEnd_3399676 387926190567721330158929 := by
  unfold tailWord_3399676
  simp only [CollatzResearch.WordTrace]
  refine ⟨61998185215780972640257441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82664246954374630187009921 61998185215780972640257441)
  ·
    refine ⟨46498638911835729480193081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61998185215780972640257441 46498638911835729480193081)
    ·
      refine ⟨34873979183876797110144811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46498638911835729480193081 34873979183876797110144811)
      ·
        refine ⟨52310968775815195665217217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34873979183876797110144811 52310968775815195665217217)
        ·
          refine ⟨39233226581861396748912913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52310968775815195665217217 39233226581861396748912913)
          ·
            refine ⟨29424919936396047561684685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39233226581861396748912913 29424919936396047561684685)
            ·
              refine ⟨11034344976148517835631757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29424919936396047561684685 11034344976148517835631757)
              ·
                refine ⟨4137879366055694188361909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11034344976148517835631757 4137879366055694188361909)
                ·
                  refine ⟨387926190567721330158929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4137879366055694188361909 387926190567721330158929)
                  ·
                    rfl

theorem cell22_3399676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_3399676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399676 prefixEnd_3399676 := by exact prefixLift 3399676
  have htrace : WordTrace (prefixWord ++ tailWord_3399676) baseStart_3399676 baseEnd_3399676 := by
    simpa [prefixWord, tailWord_3399676, baseEnd_3399676] using wordTrace_append hprefix tailTrace_3399676
  have hstable : (prefixWord ++ tailWord_3399676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399676).length < 2 ^ (prefixWord ++ tailWord_3399676).sum := by decide
  have hdescent : baseEnd_3399676 < baseStart_3399676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399751 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 1, 6]
def baseStart_3399751 : Nat := 118140960795 + 3399751 * 2 ^ 59
def prefixEnd_3399751 : Nat := 4983230072969 + 3 ^ 40 * 3399751 * 2
def baseEnd_3399751 : Nat := 1163804245735888794851557

theorem tailTrace_3399751 : CollatzResearch.WordTrace tailWord_3399751 prefixEnd_3399751 1163804245735888794851557 := by
  unfold tailWord_3399751
  simp only [CollatzResearch.WordTrace]
  refine ⟨123999105906290233089495107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82666070604193488726330071 123999105906290233089495107)
  ·
    refine ⟨185998658859435349634242661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123999105906290233089495107 185998658859435349634242661)
    ·
      refine ⟨34874748536144128056420499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185998658859435349634242661 34874748536144128056420499)
      ·
        refine ⟨52312122804216192084630749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34874748536144128056420499 52312122804216192084630749)
        ·
          refine ⟨19617046051581072031736531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52312122804216192084630749 19617046051581072031736531)
          ·
            refine ⟨29425569077371608047604797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19617046051581072031736531 29425569077371608047604797)
            ·
              refine ⟨11034588404014353017851799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29425569077371608047604797 11034588404014353017851799)
              ·
                refine ⟨16551882606021529526777699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11034588404014353017851799 16551882606021529526777699)
                ·
                  refine ⟨24827823909032294290166549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16551882606021529526777699 24827823909032294290166549)
                  ·
                    refine ⟨1163804245735888794851557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24827823909032294290166549 1163804245735888794851557)
                    ·
                      rfl

theorem cell22_3399751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_3399751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399751 prefixEnd_3399751 := by exact prefixLift 3399751
  have htrace : WordTrace (prefixWord ++ tailWord_3399751) baseStart_3399751 baseEnd_3399751 := by
    simpa [prefixWord, tailWord_3399751, baseEnd_3399751] using wordTrace_append hprefix tailTrace_3399751
  have hstable : (prefixWord ++ tailWord_3399751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399751).length < 2 ^ (prefixWord ++ tailWord_3399751).sum := by decide
  have hdescent : baseEnd_3399751 < baseStart_3399751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399811 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 7]
def baseStart_3399811 : Nat := 118140960795 + 3399811 * 2 ^ 59
def prefixEnd_3399811 : Nat := 4983230072969 + 3 ^ 40 * 3399811 * 2
def baseEnd_3399811 : Nat := 387941594987356212783791

theorem tailTrace_3399811 : CollatzResearch.WordTrace tailWord_3399811 prefixEnd_3399811 387941594987356212783791 := by
  unfold tailWord_3399811
  simp only [CollatzResearch.WordTrace]
  refine ⟨124001294286072863336679287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82667529524048575557786191 124001294286072863336679287)
  ·
    refine ⟨186001941429109295005018931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124001294286072863336679287 186001941429109295005018931)
    ·
      refine ⟨279002912143663942507528397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186001941429109295005018931 279002912143663942507528397)
      ·
        refine ⟨104626092053873978440323149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279002912143663942507528397 104626092053873978440323149)
        ·
          refine ⟨39234784520202741915121181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104626092053873978440323149 39234784520202741915121181)
          ·
            refine ⟨14713044195076028218170443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39234784520202741915121181 14713044195076028218170443)
            ·
              refine ⟨22069566292614042327255665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14713044195076028218170443 22069566292614042327255665)
              ·
                refine ⟨16552174719460531745441749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22069566292614042327255665 16552174719460531745441749)
                ·
                  refine ⟨387941594987356212783791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16552174719460531745441749 387941594987356212783791)
                  ·
                    rfl

theorem cell22_3399811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 7].length) (baseStart_3399811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399811 prefixEnd_3399811 := by exact prefixLift 3399811
  have htrace : WordTrace (prefixWord ++ tailWord_3399811) baseStart_3399811 baseEnd_3399811 := by
    simpa [prefixWord, tailWord_3399811, baseEnd_3399811] using wordTrace_append hprefix tailTrace_3399811
  have hstable : (prefixWord ++ tailWord_3399811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399811).length < 2 ^ (prefixWord ++ tailWord_3399811).sum := by decide
  have hdescent : baseEnd_3399811 < baseStart_3399811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399832 : List Nat := [2, 1, 2, 4, 3, 2, 1, 1, 3, 3]
def baseStart_3399832 : Nat := 118140960795 + 3399832 * 2 ^ 59
def prefixEnd_3399832 : Nat := 4983230072969 + 3 ^ 40 * 3399832 * 2
def baseEnd_3399832 : Nat := 1163831973691231583576309

theorem tailTrace_3399832 : CollatzResearch.WordTrace tailWord_3399832 prefixEnd_3399832 1163831973691231583576309 := by
  unfold tailWord_3399832
  simp only [CollatzResearch.WordTrace]
  refine ⟨62001030109498391961596875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82668040145997855948795833 62001030109498391961596875)
  ·
    refine ⟨93001545164247587942395313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62001030109498391961596875 93001545164247587942395313)
    ·
      refine ⟨69751158873185690956796485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93001545164247587942395313 69751158873185690956796485)
      ·
        refine ⟨13078342288722317054399341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69751158873185690956796485 13078342288722317054399341)
        ·
          refine ⟨4904378358270868895399753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13078342288722317054399341 4904378358270868895399753)
          ·
            refine ⟨3678283768703151671549815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4904378358270868895399753 3678283768703151671549815)
            ·
              refine ⟨5517425653054727507324723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3678283768703151671549815 5517425653054727507324723)
              ·
                refine ⟨8276138479582091260987085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5517425653054727507324723 8276138479582091260987085)
                ·
                  refine ⟨3103551929843284222870157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8276138479582091260987085 3103551929843284222870157)
                  ·
                    refine ⟨1163831973691231583576309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3103551929843284222870157 1163831973691231583576309)
                    ·
                      rfl

theorem cell22_3399832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_3399832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399832 prefixEnd_3399832 := by exact prefixLift 3399832
  have htrace : WordTrace (prefixWord ++ tailWord_3399832) baseStart_3399832 baseEnd_3399832 := by
    simpa [prefixWord, tailWord_3399832, baseEnd_3399832] using wordTrace_append hprefix tailTrace_3399832
  have hstable : (prefixWord ++ tailWord_3399832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399832).length < 2 ^ (prefixWord ++ tailWord_3399832).sum := by decide
  have hdescent : baseEnd_3399832 < baseStart_3399832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399858 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_3399858 : Nat := 118140960795 + 3399858 * 2 ^ 59
def prefixEnd_3399858 : Nat := 4983230072969 + 3 ^ 40 * 3399858 * 2
def baseEnd_3399858 : Nat := 1163840874022576182426229

theorem tailTrace_3399858 : CollatzResearch.WordTrace tailWord_3399858 prefixEnd_3399858 1163840874022576182426229 := by
  unfold tailWord_3399858
  simp only [CollatzResearch.WordTrace]
  refine ⟨31000752129225647590910057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82668672344601726909093485 31000752129225647590910057)
  ·
    refine ⟨23250564096919235693182543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31000752129225647590910057 23250564096919235693182543)
    ·
      refine ⟨34875846145378853539773815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23250564096919235693182543 34875846145378853539773815)
      ·
        refine ⟨52313769218068280309660723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34875846145378853539773815 52313769218068280309660723)
        ·
          refine ⟨78470653827102420464491085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52313769218068280309660723 78470653827102420464491085)
          ·
            refine ⟨29426495185163407674184157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78470653827102420464491085 29426495185163407674184157)
            ·
              refine ⟨11034935694436277877819059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29426495185163407674184157 11034935694436277877819059)
              ·
                refine ⟨16552403541654416816728589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11034935694436277877819059 16552403541654416816728589)
                ·
                  refine ⟨6207151328120406306273221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16552403541654416816728589 6207151328120406306273221)
                  ·
                    refine ⟨1163840874022576182426229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6207151328120406306273221 1163840874022576182426229)
                    ·
                      rfl

theorem cell22_3399858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_3399858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399858 prefixEnd_3399858 := by exact prefixLift 3399858
  have htrace : WordTrace (prefixWord ++ tailWord_3399858) baseStart_3399858 baseEnd_3399858 := by
    simpa [prefixWord, tailWord_3399858, baseEnd_3399858] using wordTrace_append hprefix tailTrace_3399858
  have hstable : (prefixWord ++ tailWord_3399858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399858).length < 2 ^ (prefixWord ++ tailWord_3399858).sum := by decide
  have hdescent : baseEnd_3399858 < baseStart_3399858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399905 : List Nat := [1, 2, 3, 1, 3, 1, 1, 5, 2, 3]
def baseStart_3399905 : Nat := 118140960795 + 3399905 * 2 ^ 59
def prefixEnd_3399905 : Nat := 4983230072969 + 3 ^ 40 * 3399905 * 2
def baseEnd_3399905 : Nat := 1163856963083083726501085

theorem tailTrace_3399905 : CollatzResearch.WordTrace tailWord_3399905 prefixEnd_3399905 1163856963083083726501085 := by
  unfold tailWord_3399905
  simp only [CollatzResearch.WordTrace]
  refine ⟨124004722747732317390601169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82669815165154878260400779 124004722747732317390601169)
  ·
    refine ⟨93003542060799238042950877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124004722747732317390601169 93003542060799238042950877)
    ·
      refine ⟨34876328272799714266106579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93003542060799238042950877 34876328272799714266106579)
      ·
        refine ⟨52314492409199571399159869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34876328272799714266106579 52314492409199571399159869)
        ·
          refine ⟨19617934653449839274684951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52314492409199571399159869 19617934653449839274684951)
          ·
            refine ⟨29426901980174758912027427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19617934653449839274684951 29426901980174758912027427)
            ·
              refine ⟨44140352970262138368041141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29426901980174758912027427 44140352970262138368041141)
              ·
                refine ⟨4138158090962075472003857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44140352970262138368041141 4138158090962075472003857)
                ·
                  refine ⟨3103618568221556604002893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4138158090962075472003857 3103618568221556604002893)
                  ·
                    refine ⟨1163856963083083726501085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3103618568221556604002893 1163856963083083726501085)
                    ·
                      rfl

theorem cell22_3399905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_3399905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399905 prefixEnd_3399905 := by exact prefixLift 3399905
  have htrace : WordTrace (prefixWord ++ tailWord_3399905) baseStart_3399905 baseEnd_3399905 := by
    simpa [prefixWord, tailWord_3399905, baseEnd_3399905] using wordTrace_append hprefix tailTrace_3399905
  have hstable : (prefixWord ++ tailWord_3399905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399905).length < 2 ^ (prefixWord ++ tailWord_3399905).sum := by decide
  have hdescent : baseEnd_3399905 < baseStart_3399905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399963 : List Nat := [1, 1, 1, 1, 1, 1, 6, 5, 5]
def baseStart_3399963 : Nat := 118140960795 + 3399963 * 2 ^ 59
def prefixEnd_3399963 : Nat := 4983230072969 + 3 ^ 40 * 3399963 * 2
def baseEnd_3399963 : Nat := 387958939222796969516969

theorem tailTrace_3399963 : CollatzResearch.WordTrace tailWord_3399963 prefixEnd_3399963 387958939222796969516969 := by
  unfold tailWord_3399963
  simp only [CollatzResearch.WordTrace]
  refine ⟨124006838181522193296212543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82671225454348128864141695 124006838181522193296212543)
  ·
    refine ⟨186010257272283289944318815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124006838181522193296212543 186010257272283289944318815)
    ·
      refine ⟨279015385908424934916478223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186010257272283289944318815 279015385908424934916478223)
      ·
        refine ⟨418523078862637402374717335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279015385908424934916478223 418523078862637402374717335)
        ·
          refine ⟨627784618293956103562076003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418523078862637402374717335 627784618293956103562076003)
          ·
            refine ⟨941676927440934155343114005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627784618293956103562076003 941676927440934155343114005)
            ·
              refine ⟨44141105973793788531708469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 941676927440934155343114005 44141105973793788531708469)
              ·
                refine ⟨4138228685043167674847669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44141105973793788531708469 4138228685043167674847669)
                ·
                  refine ⟨387958939222796969516969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4138228685043167674847669 387958939222796969516969)
                  ·
                    rfl

theorem cell22_3399963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 5].length) (baseStart_3399963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3399963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3399963 prefixEnd_3399963 := by exact prefixLift 3399963
  have htrace : WordTrace (prefixWord ++ tailWord_3399963) baseStart_3399963 baseEnd_3399963 := by
    simpa [prefixWord, tailWord_3399963, baseEnd_3399963] using wordTrace_append hprefix tailTrace_3399963
  have hstable : (prefixWord ++ tailWord_3399963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399963).length < 2 ^ (prefixWord ++ tailWord_3399963).sum := by decide
  have hdescent : baseEnd_3399963 < baseStart_3399963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400001 : List Nat := [1, 2, 5, 2, 3, 1, 1, 1, 3, 3]
def baseStart_3400001 : Nat := 118140960795 + 3400001 * 2 ^ 59
def prefixEnd_3400001 : Nat := 4983230072969 + 3 ^ 40 * 3400001 * 2
def baseEnd_3400001 : Nat := 1163889825844971476100791

theorem tailTrace_3400001 : CollatzResearch.WordTrace tailWord_3400001 prefixEnd_3400001 1163889825844971476100791 := by
  unfold tailWord_3400001
  simp only [CollatzResearch.WordTrace]
  refine ⟨124008224155384525786095857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82672149436923017190730571 124008224155384525786095857)
  ·
    refine ⟨93006168116538394339571893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124008224155384525786095857 93006168116538394339571893)
    ·
      refine ⟨8719328260925474469334865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93006168116538394339571893 8719328260925474469334865)
      ·
        refine ⟨6539496195694105852001149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8719328260925474469334865 6539496195694105852001149)
        ·
          refine ⟨2452311073385289694500431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6539496195694105852001149 2452311073385289694500431)
          ·
            refine ⟨3678466610077934541750647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2452311073385289694500431 3678466610077934541750647)
            ·
              refine ⟨5517699915116901812625971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3678466610077934541750647 5517699915116901812625971)
              ·
                refine ⟨8276549872675352718938957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5517699915116901812625971 8276549872675352718938957)
                ·
                  refine ⟨3103706202253257269602109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8276549872675352718938957 3103706202253257269602109)
                  ·
                    refine ⟨1163889825844971476100791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3103706202253257269602109 1163889825844971476100791)
                    ·
                      rfl

theorem cell22_3400001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_3400001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400001 prefixEnd_3400001 := by exact prefixLift 3400001
  have htrace : WordTrace (prefixWord ++ tailWord_3400001) baseStart_3400001 baseEnd_3400001 := by
    simpa [prefixWord, tailWord_3400001, baseEnd_3400001] using wordTrace_append hprefix tailTrace_3400001
  have hstable : (prefixWord ++ tailWord_3400001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400001).length < 2 ^ (prefixWord ++ tailWord_3400001).sum := by decide
  have hdescent : baseEnd_3400001 < baseStart_3400001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400040 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 3, 5]
def baseStart_3400040 : Nat := 118140960795 + 3400040 * 2 ^ 59
def prefixEnd_3400040 : Nat := 4983230072969 + 3 ^ 40 * 3400040 * 2
def baseEnd_3400040 : Nat := 1163903176341988374375671

theorem tailTrace_3400040 : CollatzResearch.WordTrace tailWord_3400040 prefixEnd_3400040 1163903176341988374375671 := by
  unfold tailWord_3400040
  simp only [CollatzResearch.WordTrace]
  refine ⟨62004823301121617723382787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82673097734828823631177049 62004823301121617723382787)
  ·
    refine ⟨93007234951682426585074181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62004823301121617723382787 93007234951682426585074181)
    ·
      refine ⟨17438856553440454984701409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93007234951682426585074181 17438856553440454984701409)
      ·
        refine ⟨13079142415080341238526057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17438856553440454984701409 13079142415080341238526057)
        ·
          refine ⟨9809356811310255928894543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13079142415080341238526057 9809356811310255928894543)
          ·
            refine ⟨14714035216965383893341815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9809356811310255928894543 14714035216965383893341815)
            ·
              refine ⟨22071052825448075840012723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14714035216965383893341815 22071052825448075840012723)
              ·
                refine ⟨33106579238172113760019085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22071052825448075840012723 33106579238172113760019085)
                ·
                  refine ⟨12414967214314542660007157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33106579238172113760019085 12414967214314542660007157)
                  ·
                    refine ⟨1163903176341988374375671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12414967214314542660007157 1163903176341988374375671)
                    ·
                      rfl

theorem cell22_3400040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_3400040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400040 prefixEnd_3400040 := by exact prefixLift 3400040
  have htrace : WordTrace (prefixWord ++ tailWord_3400040) baseStart_3400040 baseEnd_3400040 := by
    simpa [prefixWord, tailWord_3400040, baseEnd_3400040] using wordTrace_append hprefix tailTrace_3400040
  have hstable : (prefixWord ++ tailWord_3400040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400040).length < 2 ^ (prefixWord ++ tailWord_3400040).sum := by decide
  have hdescent : baseEnd_3400040 < baseStart_3400040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400044 : List Nat := [2, 2, 1, 1, 6, 1, 3, 1, 1, 4]
def baseStart_3400044 : Nat := 118140960795 + 3400044 * 2 ^ 59
def prefixEnd_3400044 : Nat := 4983230072969 + 3 ^ 40 * 3400044 * 2
def baseEnd_3400044 : Nat := 1163904545623733697275659

theorem tailTrace_3400044 : CollatzResearch.WordTrace tailWord_3400044 prefixEnd_3400044 1163904545623733697275659 := by
  unfold tailWord_3400044
  simp only [CollatzResearch.WordTrace]
  refine ⟨62004896247114372064955593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82673194996152496086607457 62004896247114372064955593)
  ·
    refine ⟨46503672185335779048716695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62004896247114372064955593 46503672185335779048716695)
    ·
      refine ⟨69755508278003668573075043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46503672185335779048716695 69755508278003668573075043)
      ·
        refine ⟨104633262417005502859612565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69755508278003668573075043 104633262417005502859612565)
        ·
          refine ⟨4904684175797132946544339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104633262417005502859612565 4904684175797132946544339)
          ·
            refine ⟨7357026263695699419816509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4904684175797132946544339 7357026263695699419816509)
            ·
              refine ⟨2758884848885887282431191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7357026263695699419816509 2758884848885887282431191)
              ·
                refine ⟨4138327273328830923646787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758884848885887282431191 4138327273328830923646787)
                ·
                  refine ⟨6207490909993246385470181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138327273328830923646787 6207490909993246385470181)
                  ·
                    refine ⟨1163904545623733697275659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6207490909993246385470181 1163904545623733697275659)
                    ·
                      rfl

theorem cell22_3400044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 4].length) (baseStart_3400044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400044 prefixEnd_3400044 := by exact prefixLift 3400044
  have htrace : WordTrace (prefixWord ++ tailWord_3400044) baseStart_3400044 baseEnd_3400044 := by
    simpa [prefixWord, tailWord_3400044, baseEnd_3400044] using wordTrace_append hprefix tailTrace_3400044
  have hstable : (prefixWord ++ tailWord_3400044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400044).length < 2 ^ (prefixWord ++ tailWord_3400044).sum := by decide
  have hdescent : baseEnd_3400044 < baseStart_3400044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400059 : List Nat := [1, 1, 1, 1, 1, 9, 2, 2, 4]
def baseStart_3400059 : Nat := 118140960795 + 3400059 * 2 ^ 59
def prefixEnd_3400059 : Nat := 4983230072969 + 3 ^ 40 * 3400059 * 2
def baseEnd_3400059 : Nat := 387969893476759552716871

theorem tailTrace_3400059 : CollatzResearch.WordTrace tailWord_3400059 prefixEnd_3400059 387969893476759552716871 := by
  unfold tailWord_3400059
  simp only [CollatzResearch.WordTrace]
  refine ⟨124010339589174401691707231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82673559726116267794471487 124010339589174401691707231)
  ·
    refine ⟨186015509383761602537560847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124010339589174401691707231 186015509383761602537560847)
    ·
      refine ⟨279023264075642403806341271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186015509383761602537560847 279023264075642403806341271)
      ·
        refine ⟨418534896113463605709511907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279023264075642403806341271 418534896113463605709511907)
        ·
          refine ⟨627802344170195408564267861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418534896113463605709511907 627802344170195408564267861)
          ·
            refine ⟨3678529360372238722056257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 627802344170195408564267861 3678529360372238722056257)
            ·
              refine ⟨2758897020279179041542193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3678529360372238722056257 2758897020279179041542193)
              ·
                refine ⟨2069172765209384281156645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2758897020279179041542193 2069172765209384281156645)
                ·
                  refine ⟨387969893476759552716871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2069172765209384281156645 387969893476759552716871)
                  ·
                    rfl

theorem cell22_3400059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 4].length) (baseStart_3400059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400059 prefixEnd_3400059 := by exact prefixLift 3400059
  have htrace : WordTrace (prefixWord ++ tailWord_3400059) baseStart_3400059 baseEnd_3400059 := by
    simpa [prefixWord, tailWord_3400059, baseEnd_3400059] using wordTrace_append hprefix tailTrace_3400059
  have hstable : (prefixWord ++ tailWord_3400059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400059).length < 2 ^ (prefixWord ++ tailWord_3400059).sum := by decide
  have hdescent : baseEnd_3400059 < baseStart_3400059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400074 : List Nat := [3, 1, 2, 5, 1, 1, 2, 1, 1, 5]
def baseStart_3400074 : Nat := 118140960795 + 3400074 * 2 ^ 59
def prefixEnd_3400074 : Nat := 4983230072969 + 3 ^ 40 * 3400074 * 2
def baseEnd_3400074 : Nat := 1163914815236823619025567

theorem tailTrace_3400074 : CollatzResearch.WordTrace tailWord_3400074 prefixEnd_3400074 1163914815236823619025567 := by
  unfold tailWord_3400074
  simp only [CollatzResearch.WordTrace]
  refine ⟨31002721671030014813375819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82673924456080039502335517 31002721671030014813375819)
  ·
    refine ⟨46504082506545022220063729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31002721671030014813375819 46504082506545022220063729)
    ·
      refine ⟨34878061879908766665047797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46504082506545022220063729 34878061879908766665047797)
      ·
        refine ⟨3269818301241446874848231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34878061879908766665047797 3269818301241446874848231)
        ·
          refine ⟨4904727451862170312272347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3269818301241446874848231 4904727451862170312272347)
          ·
            refine ⟨7357091177793255468408521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4904727451862170312272347 7357091177793255468408521)
            ·
              refine ⟨5517818383344941601306391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7357091177793255468408521 5517818383344941601306391)
              ·
                refine ⟨8276727575017412401959587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5517818383344941601306391 8276727575017412401959587)
                ·
                  refine ⟨12415091362526118602939381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8276727575017412401959587 12415091362526118602939381)
                  ·
                    refine ⟨1163914815236823619025567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12415091362526118602939381 1163914815236823619025567)
                    ·
                      rfl

theorem cell22_3400074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_3400074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400074 prefixEnd_3400074 := by exact prefixLift 3400074
  have htrace : WordTrace (prefixWord ++ tailWord_3400074) baseStart_3400074 baseEnd_3400074 := by
    simpa [prefixWord, tailWord_3400074, baseEnd_3400074] using wordTrace_append hprefix tailTrace_3400074
  have hstable : (prefixWord ++ tailWord_3400074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400074).length < 2 ^ (prefixWord ++ tailWord_3400074).sum := by decide
  have hdescent : baseEnd_3400074 < baseStart_3400074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400119 : List Nat := [1, 1, 3, 1, 3, 3, 2, 4, 1, 3]
def baseStart_3400119 : Nat := 118140960795 + 3400119 * 2 ^ 59
def prefixEnd_3400119 : Nat := 4983230072969 + 3 ^ 40 * 3400119 * 2
def baseEnd_3400119 : Nat := 1163930219656458501650429

theorem tailTrace_3400119 : CollatzResearch.WordTrace tailWord_3400119 prefixEnd_3400119 1163930219656458501650429 := by
  unfold tailWord_3400119
  simp only [CollatzResearch.WordTrace]
  refine ⟨124012527968957031938891411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82675018645971354625927607 124012527968957031938891411)
  ·
    refine ⟨186018791953435547908337117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124012527968957031938891411 186018791953435547908337117)
    ·
      refine ⟨69757046982538330465626419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186018791953435547908337117 69757046982538330465626419)
      ·
        refine ⟨104635570473807495698439629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69757046982538330465626419 104635570473807495698439629)
        ·
          refine ⟨39238338927677810886914861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104635570473807495698439629 39238338927677810886914861)
          ·
            refine ⟨14714377097879179082593073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39238338927677810886914861 14714377097879179082593073)
            ·
              refine ⟨11035782823409384311944805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14714377097879179082593073 11035782823409384311944805)
              ·
                refine ⟨2069209279389259558489651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11035782823409384311944805 2069209279389259558489651)
                ·
                  refine ⟨3103813919083889337734477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2069209279389259558489651 3103813919083889337734477)
                  ·
                    refine ⟨1163930219656458501650429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3103813919083889337734477 1163930219656458501650429)
                    ·
                      rfl

theorem cell22_3400119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 1, 3].length) (baseStart_3400119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400119 prefixEnd_3400119 := by exact prefixLift 3400119
  have htrace : WordTrace (prefixWord ++ tailWord_3400119) baseStart_3400119 baseEnd_3400119 := by
    simpa [prefixWord, tailWord_3400119, baseEnd_3400119] using wordTrace_append hprefix tailTrace_3400119
  have hstable : (prefixWord ++ tailWord_3400119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400119).length < 2 ^ (prefixWord ++ tailWord_3400119).sum := by decide
  have hdescent : baseEnd_3400119 < baseStart_3400119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400145 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 3, 4]
def baseStart_3400145 : Nat := 118140960795 + 3400145 * 2 ^ 59
def prefixEnd_3400145 : Nat := 4983230072969 + 3 ^ 40 * 3400145 * 2
def baseEnd_3400145 : Nat := 1163939119987803100500349

theorem tailTrace_3400145 : CollatzResearch.WordTrace tailWord_3400145 prefixEnd_3400145 1163939119987803100500349 := by
  unfold tailWord_3400145
  simp only [CollatzResearch.WordTrace]
  refine ⟨124013476266862838379337889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82675650844575225586225259 124013476266862838379337889)
  ·
    refine ⟨93010107200147128784503417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124013476266862838379337889 93010107200147128784503417)
    ·
      refine ⟨69757580400110346588377563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93010107200147128784503417 69757580400110346588377563)
      ·
        refine ⟨104636370600165519882566345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69757580400110346588377563 104636370600165519882566345)
        ·
          refine ⟨78477277950124139911924759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104636370600165519882566345 78477277950124139911924759)
          ·
            refine ⟨117715916925186209867887139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78477277950124139911924759 117715916925186209867887139)
            ·
              refine ⟨176573875387779314801830709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117715916925186209867887139 176573875387779314801830709)
              ·
                refine ⟨16553800817604310762671629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176573875387779314801830709 16553800817604310762671629)
                ·
                  refine ⟨6207675306601616536001861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16553800817604310762671629 6207675306601616536001861)
                  ·
                    refine ⟨1163939119987803100500349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6207675306601616536001861 1163939119987803100500349)
                    ·
                      rfl

theorem cell22_3400145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_3400145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400145 prefixEnd_3400145 := by exact prefixLift 3400145
  have htrace : WordTrace (prefixWord ++ tailWord_3400145) baseStart_3400145 baseEnd_3400145 := by
    simpa [prefixWord, tailWord_3400145, baseEnd_3400145] using wordTrace_append hprefix tailTrace_3400145
  have hstable : (prefixWord ++ tailWord_3400145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400145).length < 2 ^ (prefixWord ++ tailWord_3400145).sum := by decide
  have hdescent : baseEnd_3400145 < baseStart_3400145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400196 : List Nat := [2, 3, 2, 3, 1, 3, 1, 2, 1, 4]
def baseStart_3400196 : Nat := 118140960795 + 3400196 * 2 ^ 59
def prefixEnd_3400196 : Nat := 4983230072969 + 3 ^ 40 * 3400196 * 2
def baseEnd_3400196 : Nat := 1163956578330055967475193

theorem tailTrace_3400196 : CollatzResearch.WordTrace tailWord_3400196 prefixEnd_3400196 1163956578330055967475193 := by
  unfold tailWord_3400196
  simp only [CollatzResearch.WordTrace]
  refine ⟨62007668194839037044722221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82676890926452049392962961 62007668194839037044722221)
  ·
    refine ⟨23252875573064638891770833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62007668194839037044722221 23252875573064638891770833)
    ·
      refine ⟨17439656679798479168828125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23252875573064638891770833 17439656679798479168828125)
      ·
        refine ⟨6539871254924429688310547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17439656679798479168828125 6539871254924429688310547)
        ·
          refine ⟨9809806882386644532465821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6539871254924429688310547 9809806882386644532465821)
          ·
            refine ⟨3678677580894991699674683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9809806882386644532465821 3678677580894991699674683)
            ·
              refine ⟨5518016371342487549512025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3678677580894991699674683 5518016371342487549512025)
              ·
                refine ⟨4138512278506865662134019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5518016371342487549512025 4138512278506865662134019)
                ·
                  refine ⟨6207768417760298493201029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138512278506865662134019 6207768417760298493201029)
                  ·
                    refine ⟨1163956578330055967475193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6207768417760298493201029 1163956578330055967475193)
                    ·
                      rfl

theorem cell22_3400196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_3400196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400196 prefixEnd_3400196 := by exact prefixLift 3400196
  have htrace : WordTrace (prefixWord ++ tailWord_3400196) baseStart_3400196 baseEnd_3400196 := by
    simpa [prefixWord, tailWord_3400196, baseEnd_3400196] using wordTrace_append hprefix tailTrace_3400196
  have hstable : (prefixWord ++ tailWord_3400196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400196).length < 2 ^ (prefixWord ++ tailWord_3400196).sum := by decide
  have hdescent : baseEnd_3400196 < baseStart_3400196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400284 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 7]
def baseStart_3400284 : Nat := 118140960795 + 3400284 * 2 ^ 59
def prefixEnd_3400284 : Nat := 4983230072969 + 3 ^ 40 * 3400284 * 2
def baseEnd_3400284 : Nat := 387995567509484357091641

theorem tailTrace_3400284 : CollatzResearch.WordTrace tailWord_3400284 prefixEnd_3400284 387995567509484357091641 := by
  unfold tailWord_3400284
  simp only [CollatzResearch.WordTrace]
  refine ⟨62009273006679632559323953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82679030675572843412431937 62009273006679632559323953)
  ·
    refine ⟨46506954755009724419492965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62009273006679632559323953 46506954755009724419492965)
    ·
      refine ⟨8720054016564323328654931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46506954755009724419492965 8720054016564323328654931)
      ·
        refine ⟨13080081024846484992982397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8720054016564323328654931 13080081024846484992982397)
        ·
          refine ⟨4905030384317431872368399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13080081024846484992982397 4905030384317431872368399)
          ·
            refine ⟨7357545576476147808552599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4905030384317431872368399 7357545576476147808552599)
            ·
              refine ⟨11036318364714221712828899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7357545576476147808552599 11036318364714221712828899)
              ·
                refine ⟨16554477547071332569243349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11036318364714221712828899 16554477547071332569243349)
                ·
                  refine ⟨387995567509484357091641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16554477547071332569243349 387995567509484357091641)
                  ·
                    rfl

theorem cell22_3400284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_3400284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400284 prefixEnd_3400284 := by exact prefixLift 3400284
  have htrace : WordTrace (prefixWord ++ tailWord_3400284) baseStart_3400284 baseEnd_3400284 := by
    simpa [prefixWord, tailWord_3400284, baseEnd_3400284] using wordTrace_append hprefix tailTrace_3400284
  have hstable : (prefixWord ++ tailWord_3400284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400284).length < 2 ^ (prefixWord ++ tailWord_3400284).sum := by decide
  have hdescent : baseEnd_3400284 < baseStart_3400284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400301 : List Nat := [1, 5, 1, 1, 3, 2, 3, 1, 5]
def baseStart_3400301 : Nat := 118140960795 + 3400301 * 2 ^ 59
def prefixEnd_3400301 : Nat := 4983230072969 + 3 ^ 40 * 3400301 * 2
def baseEnd_3400301 : Nat := 387997507325290231199957

theorem tailTrace_3400301 : CollatzResearch.WordTrace tailWord_3400301 prefixEnd_3400301 387997507325290231199957 := by
  unfold tailWord_3400301
  simp only [CollatzResearch.WordTrace]
  refine ⟨124019166054297677022016757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82679444036198451348011171 124019166054297677022016757)
  ·
    refine ⟨11626796817590407220814071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124019166054297677022016757 11626796817590407220814071)
    ·
      refine ⟨17440195226385610831221107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11626796817590407220814071 17440195226385610831221107)
      ·
        refine ⟨26160292839578416246831661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17440195226385610831221107 26160292839578416246831661)
        ·
          refine ⟨9810109814841906092561873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26160292839578416246831661 9810109814841906092561873)
          ·
            refine ⟨7357582361131429569421405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9810109814841906092561873 7357582361131429569421405)
            ·
              refine ⟨2759093385424286088533027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7357582361131429569421405 2759093385424286088533027)
              ·
                refine ⟨4138640078136429132799541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2759093385424286088533027 4138640078136429132799541)
                ·
                  refine ⟨387997507325290231199957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4138640078136429132799541 387997507325290231199957)
                  ·
                    rfl

theorem cell22_3400301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_3400301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400301 prefixEnd_3400301 := by exact prefixLift 3400301
  have htrace : WordTrace (prefixWord ++ tailWord_3400301) baseStart_3400301 baseEnd_3400301 := by
    simpa [prefixWord, tailWord_3400301, baseEnd_3400301] using wordTrace_append hprefix tailTrace_3400301
  have hstable : (prefixWord ++ tailWord_3400301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400301).length < 2 ^ (prefixWord ++ tailWord_3400301).sum := by decide
  have hdescent : baseEnd_3400301 < baseStart_3400301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400327 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 3, 5]
def baseStart_3400327 : Nat := 118140960795 + 3400327 * 2 ^ 59
def prefixEnd_3400327 : Nat := 4983230072969 + 3 ^ 40 * 3400327 * 2
def baseEnd_3400327 : Nat := 1164001422307215292449791

theorem tailTrace_3400327 : CollatzResearch.WordTrace tailWord_3400327 prefixEnd_3400327 1164001422307215292449791 := by
  unfold tailWord_3400327
  simp only [CollatzResearch.WordTrace]
  refine ⟨124020114352203483462463235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82680076234802322308308823 124020114352203483462463235)
  ·
    refine ⟨186030171528305225193694853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124020114352203483462463235 186030171528305225193694853)
    ·
      refine ⟨34880657161557229723817785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186030171528305225193694853 34880657161557229723817785)
      ·
        refine ⟨26160492871167922292863339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34880657161557229723817785 26160492871167922292863339)
        ·
          refine ⟨39240739306751883439295009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26160492871167922292863339 39240739306751883439295009)
          ·
            refine ⟨29430554480063912579471257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39240739306751883439295009 29430554480063912579471257)
            ·
              refine ⟨22072915860047934434603443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29430554480063912579471257 22072915860047934434603443)
              ·
                refine ⟨33109373790071901651905165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22072915860047934434603443 33109373790071901651905165)
                ·
                  refine ⟨12416015171276963119464437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33109373790071901651905165 12416015171276963119464437)
                  ·
                    refine ⟨1164001422307215292449791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12416015171276963119464437 1164001422307215292449791)
                    ·
                      rfl

theorem cell22_3400327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_3400327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400327 prefixEnd_3400327 := by exact prefixLift 3400327
  have htrace : WordTrace (prefixWord ++ tailWord_3400327) baseStart_3400327 baseEnd_3400327 := by
    simpa [prefixWord, tailWord_3400327, baseEnd_3400327] using wordTrace_append hprefix tailTrace_3400327
  have hstable : (prefixWord ++ tailWord_3400327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400327).length < 2 ^ (prefixWord ++ tailWord_3400327).sum := by decide
  have hdescent : baseEnd_3400327 < baseStart_3400327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400344 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 4, 3]
def baseStart_3400344 : Nat := 118140960795 + 3400344 * 2 ^ 59
def prefixEnd_3400344 : Nat := 4983230072969 + 3 ^ 40 * 3400344 * 2
def baseEnd_3400344 : Nat := 1164007241754632914774739

theorem tailTrace_3400344 : CollatzResearch.WordTrace tailWord_3400344 prefixEnd_3400344 1164007241754632914774739 := by
  unfold tailWord_3400344
  simp only [CollatzResearch.WordTrace]
  refine ⟨62010367196570947682916043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82680489595427930243888057 62010367196570947682916043)
  ·
    refine ⟨93015550794856421524374065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62010367196570947682916043 93015550794856421524374065)
    ·
      refine ⟨69761663096142316143280549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93015550794856421524374065 69761663096142316143280549)
      ·
        refine ⟨13080311830526684276865103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69761663096142316143280549 13080311830526684276865103)
        ·
          refine ⟨19620467745790026415297655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13080311830526684276865103 19620467745790026415297655)
          ·
            refine ⟨29430701618685039622946483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19620467745790026415297655 29430701618685039622946483)
            ·
              refine ⟨44146052428027559434419725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29430701618685039622946483 44146052428027559434419725)
              ·
                refine ⟨16554769660510334787907397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44146052428027559434419725 16554769660510334787907397)
                ·
                  refine ⟨3104019311345687772732637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16554769660510334787907397 3104019311345687772732637)
                  ·
                    refine ⟨1164007241754632914774739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3104019311345687772732637 1164007241754632914774739)
                    ·
                      rfl

theorem cell22_3400344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_3400344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400344 prefixEnd_3400344 := by exact prefixLift 3400344
  have htrace : WordTrace (prefixWord ++ tailWord_3400344) baseStart_3400344 baseEnd_3400344 := by
    simpa [prefixWord, tailWord_3400344, baseEnd_3400344] using wordTrace_append hprefix tailTrace_3400344
  have hstable : (prefixWord ++ tailWord_3400344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400344).length < 2 ^ (prefixWord ++ tailWord_3400344).sum := by decide
  have hdescent : baseEnd_3400344 < baseStart_3400344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400397 : List Nat := [1, 6, 2, 1, 2, 2, 2, 2, 4]
def baseStart_3400397 : Nat := 118140960795 + 3400397 * 2 ^ 59
def prefixEnd_3400397 : Nat := 4983230072969 + 3 ^ 40 * 3400397 * 2
def baseEnd_3400397 : Nat := 388008461579252814399859

theorem tailTrace_3400397 : CollatzResearch.WordTrace tailWord_3400397 prefixEnd_3400397 388008461579252814399859 := by
  unfold tailWord_3400397
  simp only [CollatzResearch.WordTrace]
  refine ⟨124022667461949885417511445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82681778307966590278340963 124022667461949885417511445)
  ·
    refine ⟨5813562537278900878945849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 124022667461949885417511445 5813562537278900878945849)
    ·
      refine ⟨4360171902959175659209387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5813562537278900878945849 4360171902959175659209387)
      ·
        refine ⟨6540257854438763488814081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4360171902959175659209387 6540257854438763488814081)
        ·
          refine ⟨4905193390829072616610561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6540257854438763488814081 4905193390829072616610561)
          ·
            refine ⟨3678895043121804462457921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4905193390829072616610561 3678895043121804462457921)
            ·
              refine ⟨2759171282341353346843441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3678895043121804462457921 2759171282341353346843441)
              ·
                refine ⟨2069378461756015010132581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2759171282341353346843441 2069378461756015010132581)
                ·
                  refine ⟨388008461579252814399859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2069378461756015010132581 388008461579252814399859)
                  ·
                    rfl

theorem cell22_3400397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_3400397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400397 prefixEnd_3400397 := by exact prefixLift 3400397
  have htrace : WordTrace (prefixWord ++ tailWord_3400397) baseStart_3400397 baseEnd_3400397 := by
    simpa [prefixWord, tailWord_3400397, baseEnd_3400397] using wordTrace_append hprefix tailTrace_3400397
  have hstable : (prefixWord ++ tailWord_3400397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400397).length < 2 ^ (prefixWord ++ tailWord_3400397).sum := by decide
  have hdescent : baseEnd_3400397 < baseStart_3400397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400447 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 10]
def baseStart_3400447 : Nat := 118140960795 + 3400447 * 2 ^ 59
def prefixEnd_3400447 : Nat := 4983230072969 + 3 ^ 40 * 3400447 * 2
def baseEnd_3400447 : Nat := 388014166919858326483141

theorem tailTrace_3400447 : CollatzResearch.WordTrace tailWord_3400447 prefixEnd_3400447 388014166919858326483141 := by
  unfold tailWord_3400447
  simp only [CollatzResearch.WordTrace]
  refine ⟨124024491111768743956831595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82682994074512495971221063 124024491111768743956831595)
  ·
    refine ⟨186036736667653115935247393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124024491111768743956831595 186036736667653115935247393)
    ·
      refine ⟨139527552500739836951435545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186036736667653115935247393 139527552500739836951435545)
      ·
        refine ⟨104645664375554877713576659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139527552500739836951435545 104645664375554877713576659)
        ·
          refine ⟨156968496563332316570364989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104645664375554877713576659 156968496563332316570364989)
          ·
            refine ⟨58863186211249618713886871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156968496563332316570364989 58863186211249618713886871)
            ·
              refine ⟨88294779316874428070830307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58863186211249618713886871 88294779316874428070830307)
              ·
                refine ⟨132442168975311642106245461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88294779316874428070830307 132442168975311642106245461)
                ·
                  refine ⟨388014166919858326483141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 132442168975311642106245461 388014166919858326483141)
                  ·
                    rfl

theorem cell22_3400447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 10].length) (baseStart_3400447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400447 prefixEnd_3400447 := by exact prefixLift 3400447
  have htrace : WordTrace (prefixWord ++ tailWord_3400447) baseStart_3400447 baseEnd_3400447 := by
    simpa [prefixWord, tailWord_3400447, baseEnd_3400447] using wordTrace_append hprefix tailTrace_3400447
  have hstable : (prefixWord ++ tailWord_3400447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400447).length < 2 ^ (prefixWord ++ tailWord_3400447).sum := by decide
  have hdescent : baseEnd_3400447 < baseStart_3400447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400511 : List Nat := [1, 1, 2, 2, 5, 2, 1, 2, 2, 4]
def baseStart_3400511 : Nat := 118140960795 + 3400511 * 2 ^ 59
def prefixEnd_3400511 : Nat := 4983230072969 + 3 ^ 40 * 3400511 * 2
def baseEnd_3400511 : Nat := 1164064409267500145849227

theorem tailTrace_3400511 : CollatzResearch.WordTrace tailWord_3400511 prefixEnd_3400511 1164064409267500145849227 := by
  unfold tailWord_3400511
  simp only [CollatzResearch.WordTrace]
  refine ⟨124026825383536882887161387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82684550255691255258107591 124026825383536882887161387)
  ·
    refine ⟨186040238075305324330742081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124026825383536882887161387 186040238075305324330742081)
    ·
      refine ⟨139530178556478993248056561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186040238075305324330742081 139530178556478993248056561)
      ·
        refine ⟨104647633917359244936042421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139530178556478993248056561 104647633917359244936042421)
        ·
          refine ⟨9810715679752429212753977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104647633917359244936042421 9810715679752429212753977)
          ·
            refine ⟨7358036759814321909565483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9810715679752429212753977 7358036759814321909565483)
            ·
              refine ⟨11037055139721482864348225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7358036759814321909565483 11037055139721482864348225)
              ·
                refine ⟨8277791354791112148261169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11037055139721482864348225 8277791354791112148261169)
                ·
                  refine ⟨6208343516093334111195877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8277791354791112148261169 6208343516093334111195877)
                  ·
                    refine ⟨1164064409267500145849227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6208343516093334111195877 1164064409267500145849227)
                    ·
                      rfl

theorem cell22_3400511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 4].length) (baseStart_3400511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400511 prefixEnd_3400511 := by exact prefixLift 3400511
  have htrace : WordTrace (prefixWord ++ tailWord_3400511) baseStart_3400511 baseEnd_3400511 := by
    simpa [prefixWord, tailWord_3400511, baseEnd_3400511] using wordTrace_append hprefix tailTrace_3400511
  have hstable : (prefixWord ++ tailWord_3400511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400511).length < 2 ^ (prefixWord ++ tailWord_3400511).sum := by decide
  have hdescent : baseEnd_3400511 < baseStart_3400511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400575 : List Nat := [1, 1, 2, 2, 1, 1, 8, 2, 1, 3]
def baseStart_3400575 : Nat := 118140960795 + 3400575 * 2 ^ 59
def prefixEnd_3400575 : Nat := 4983230072969 + 3 ^ 40 * 3400575 * 2
def baseEnd_3400575 : Nat := 1164086317775425312249031

theorem tailTrace_3400575 : CollatzResearch.WordTrace tailWord_3400575 prefixEnd_3400575 1164086317775425312249031 := by
  unfold tailWord_3400575
  simp only [CollatzResearch.WordTrace]
  refine ⟨124029159655305021817491179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82686106436870014544994119 124029159655305021817491179)
  ·
    refine ⟨186043739482957532726236769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124029159655305021817491179 186043739482957532726236769)
    ·
      refine ⟨139532804612218149544677577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186043739482957532726236769 139532804612218149544677577)
      ·
        refine ⟨104649603459163612158508183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139532804612218149544677577 104649603459163612158508183)
        ·
          refine ⟨156974405188745418237762275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104649603459163612158508183 156974405188745418237762275)
          ·
            refine ⟨235461607783118127356643413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156974405188745418237762275 235461607783118127356643413)
            ·
              refine ⟨2759315716208415554960665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 235461607783118127356643413 2759315716208415554960665)
              ·
                refine ⟨2069486787156311666220499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2759315716208415554960665 2069486787156311666220499)
                ·
                  refine ⟨3104230180734467499330749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2069486787156311666220499 3104230180734467499330749)
                  ·
                    refine ⟨1164086317775425312249031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3104230180734467499330749 1164086317775425312249031)
                    ·
                      rfl

theorem cell22_3400575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 1, 3].length) (baseStart_3400575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400575 prefixEnd_3400575 := by exact prefixLift 3400575
  have htrace : WordTrace (prefixWord ++ tailWord_3400575) baseStart_3400575 baseEnd_3400575 := by
    simpa [prefixWord, tailWord_3400575, baseEnd_3400575] using wordTrace_append hprefix tailTrace_3400575
  have hstable : (prefixWord ++ tailWord_3400575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400575).length < 2 ^ (prefixWord ++ tailWord_3400575).sum := by decide
  have hdescent : baseEnd_3400575 < baseStart_3400575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400586 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 1, 7]
def baseStart_3400586 : Nat := 118140960795 + 3400586 * 2 ^ 59
def prefixEnd_3400586 : Nat := 4983230072969 + 3 ^ 40 * 3400586 * 2
def baseEnd_3400586 : Nat := 1164090083300224950223997

theorem tailTrace_3400586 : CollatzResearch.WordTrace tailWord_3400586 prefixEnd_3400586 1164090083300224950223997 := by
  unfold tailWord_3400586
  simp only [CollatzResearch.WordTrace]
  refine ⟨31007390214566292674035403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82686373905510113797427741 31007390214566292674035403)
  ·
    refine ⟨46511085321849439011053105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31007390214566292674035403 46511085321849439011053105)
    ·
      refine ⟨34883313991387079258289829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46511085321849439011053105 34883313991387079258289829)
      ·
        refine ⟨6540621373385077360929343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34883313991387079258289829 6540621373385077360929343)
        ·
          refine ⟨9810932060077616041394015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6540621373385077360929343 9810932060077616041394015)
          ·
            refine ⟨14716398090116424062091023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9810932060077616041394015 14716398090116424062091023)
            ·
              refine ⟨22074597135174636093136535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14716398090116424062091023 22074597135174636093136535)
              ·
                refine ⟨33111895702761954139704803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22074597135174636093136535 33111895702761954139704803)
                ·
                  refine ⟨49667843554142931209557205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33111895702761954139704803 49667843554142931209557205)
                  ·
                    refine ⟨1164090083300224950223997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49667843554142931209557205 1164090083300224950223997)
                    ·
                      rfl

theorem cell22_3400586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_3400586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400586 prefixEnd_3400586 := by exact prefixLift 3400586
  have htrace : WordTrace (prefixWord ++ tailWord_3400586) baseStart_3400586 baseEnd_3400586 := by
    simpa [prefixWord, tailWord_3400586, baseEnd_3400586] using wordTrace_append hprefix tailTrace_3400586
  have hstable : (prefixWord ++ tailWord_3400586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400586).length < 2 ^ (prefixWord ++ tailWord_3400586).sum := by decide
  have hdescent : baseEnd_3400586 < baseStart_3400586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400601 : List Nat := [1, 2, 1, 2, 1, 3, 1, 6, 1, 4]
def baseStart_3400601 : Nat := 118140960795 + 3400601 * 2 ^ 59
def prefixEnd_3400601 : Nat := 4983230072969 + 3 ^ 40 * 3400601 * 2
def baseEnd_3400601 : Nat := 1164095218106769911098951

theorem tailTrace_3400601 : CollatzResearch.WordTrace tailWord_3400601 prefixEnd_3400601 1164095218106769911098951 := by
  unfold tailWord_3400601
  simp only [CollatzResearch.WordTrace]
  refine ⟨124030107953210828257937657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82686738635473885505291771 124030107953210828257937657)
  ·
    refine ⟨93022580964908121193453243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124030107953210828257937657 93022580964908121193453243)
    ·
      refine ⟨139533871447362181790179865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93022580964908121193453243 139533871447362181790179865)
      ·
        refine ⟨104650403585521636342634899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139533871447362181790179865 104650403585521636342634899)
        ·
          refine ⟨156975605378282454513952349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104650403585521636342634899 156975605378282454513952349)
          ·
            refine ⟨58865852016855920442732131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156975605378282454513952349 58865852016855920442732131)
            ·
              refine ⟨88298778025283880664098197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58865852016855920442732131 88298778025283880664098197)
              ·
                refine ⟨4139005219935181906129603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88298778025283880664098197 4139005219935181906129603)
                ·
                  refine ⟨6208507829902772859194405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4139005219935181906129603 6208507829902772859194405)
                  ·
                    refine ⟨1164095218106769911098951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6208507829902772859194405 1164095218106769911098951)
                    ·
                      rfl

theorem cell22_3400601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 4].length) (baseStart_3400601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400601 prefixEnd_3400601 := by exact prefixLift 3400601
  have htrace : WordTrace (prefixWord ++ tailWord_3400601) baseStart_3400601 baseEnd_3400601 := by
    simpa [prefixWord, tailWord_3400601, baseEnd_3400601] using wordTrace_append hprefix tailTrace_3400601
  have hstable : (prefixWord ++ tailWord_3400601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400601).length < 2 ^ (prefixWord ++ tailWord_3400601).sum := by decide
  have hdescent : baseEnd_3400601 < baseStart_3400601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400633 : List Nat := [1, 2, 1, 4, 2, 2, 2, 4, 4]
def baseStart_3400633 : Nat := 118140960795 + 3400633 * 2 ^ 59
def prefixEnd_3400633 : Nat := 4983230072969 + 3 ^ 40 * 3400633 * 2
def baseEnd_3400633 : Nat := 388035390786910831432951

theorem tailTrace_3400633 : CollatzResearch.WordTrace tailWord_3400633 prefixEnd_3400633 388035390786910831432951 := by
  unfold tailWord_3400633
  simp only [CollatzResearch.WordTrace]
  refine ⟨124031275089094897723102553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82687516726063265148735035 124031275089094897723102553)
  ·
    refine ⟨93023456316821173292326915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124031275089094897723102553 93023456316821173292326915)
    ·
      refine ⟨139535184475231759938490373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93023456316821173292326915 139535184475231759938490373)
      ·
        refine ⟨26162847089105954988466945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139535184475231759938490373 26162847089105954988466945)
        ·
          refine ⟨19622135316829466241350209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26162847089105954988466945 19622135316829466241350209)
          ·
            refine ⟨14716601487622099681012657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19622135316829466241350209 14716601487622099681012657)
            ·
              refine ⟨11037451115716574760759493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14716601487622099681012657 11037451115716574760759493)
              ·
                refine ⟨2069522084196857767642405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11037451115716574760759493 2069522084196857767642405)
                ·
                  refine ⟨388035390786910831432951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2069522084196857767642405 388035390786910831432951)
                  ·
                    rfl

theorem cell22_3400633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 4].length) (baseStart_3400633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400633 prefixEnd_3400633 := by exact prefixLift 3400633
  have htrace : WordTrace (prefixWord ++ tailWord_3400633) baseStart_3400633 baseEnd_3400633 := by
    simpa [prefixWord, tailWord_3400633, baseEnd_3400633] using wordTrace_append hprefix tailTrace_3400633
  have hstable : (prefixWord ++ tailWord_3400633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400633).length < 2 ^ (prefixWord ++ tailWord_3400633).sum := by decide
  have hdescent : baseEnd_3400633 < baseStart_3400633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400740 : List Nat := [2, 3, 1, 4, 1, 2, 2, 2, 5]
def baseStart_3400740 : Nat := 118140960795 + 3400740 * 2 ^ 59
def prefixEnd_3400740 : Nat := 4983230072969 + 3 ^ 40 * 3400740 * 2
def baseEnd_3400740 : Nat := 388047600215806627291175

theorem tailTrace_3400740 : CollatzResearch.WordTrace tailWord_3400740 prefixEnd_3400740 388047600215806627291175 := by
  unfold tailWord_3400740
  simp only [CollatzResearch.WordTrace]
  refine ⟨62017588849853627498623837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82690118466471503331498449 62017588849853627498623837)
  ·
    refine ⟨23256595818695110311983939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62017588849853627498623837 23256595818695110311983939)
    ·
      refine ⟨34884893728042665467975909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23256595818695110311983939 34884893728042665467975909)
      ·
        refine ⟨6540917574007999775245483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34884893728042665467975909 6540917574007999775245483)
        ·
          refine ⟨9811376361011999662868225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6540917574007999775245483 9811376361011999662868225)
          ·
            refine ⟨7358532270758999747151169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9811376361011999662868225 7358532270758999747151169)
            ·
              refine ⟨5518899203069249810363377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7358532270758999747151169 5518899203069249810363377)
              ·
                refine ⟨4139174402301937357772533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5518899203069249810363377 4139174402301937357772533)
                ·
                  refine ⟨388047600215806627291175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4139174402301937357772533 388047600215806627291175)
                  ·
                    rfl

theorem cell22_3400740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_3400740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400740 prefixEnd_3400740 := by exact prefixLift 3400740
  have htrace : WordTrace (prefixWord ++ tailWord_3400740) baseStart_3400740 baseEnd_3400740 := by
    simpa [prefixWord, tailWord_3400740, baseEnd_3400740] using wordTrace_append hprefix tailTrace_3400740
  have hstable : (prefixWord ++ tailWord_3400740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400740).length < 2 ^ (prefixWord ++ tailWord_3400740).sum := by decide
  have hdescent : baseEnd_3400740 < baseStart_3400740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400802 : List Nat := [3, 3, 2, 2, 1, 1, 2, 4, 4]
def baseStart_3400802 : Nat := 118140960795 + 3400802 * 2 ^ 59
def prefixEnd_3400802 : Nat := 4983230072969 + 3 ^ 40 * 3400802 * 2
def baseEnd_3400802 : Nat := 388054674838157462274445

theorem tailTrace_3400802 : CollatzResearch.WordTrace tailWord_3400802 prefixEnd_3400802 388054674838157462274445 := by
  unfold tailWord_3400802
  simp only [CollatzResearch.WordTrace]
  refine ⟨31009359756370659896501165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82691626016988426390669773 31009359756370659896501165)
  ·
    refine ⟨11628509908638997461187937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31009359756370659896501165 11628509908638997461187937)
    ·
      refine ⟨8721382431479248095890953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11628509908638997461187937 8721382431479248095890953)
      ·
        refine ⟨6541036823609436071918215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8721382431479248095890953 6541036823609436071918215)
        ·
          refine ⟨9811555235414154107877323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6541036823609436071918215 9811555235414154107877323)
          ·
            refine ⟨14717332853121231161815985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9811555235414154107877323 14717332853121231161815985)
            ·
              refine ⟨11037999639840923371361989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14717332853121231161815985 11037999639840923371361989)
              ·
                refine ⟨2069624932470173132130373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11037999639840923371361989 2069624932470173132130373)
                ·
                  refine ⟨388054674838157462274445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2069624932470173132130373 388054674838157462274445)
                  ·
                    rfl

theorem cell22_3400802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_3400802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400802 prefixEnd_3400802 := by exact prefixLift 3400802
  have htrace : WordTrace (prefixWord ++ tailWord_3400802) baseStart_3400802 baseEnd_3400802 := by
    simpa [prefixWord, tailWord_3400802, baseEnd_3400802] using wordTrace_append hprefix tailTrace_3400802
  have hstable : (prefixWord ++ tailWord_3400802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400802).length < 2 ^ (prefixWord ++ tailWord_3400802).sum := by decide
  have hdescent : baseEnd_3400802 < baseStart_3400802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400956 : List Nat := [2, 2, 2, 1, 6, 1, 2, 1, 1, 4]
def baseStart_3400956 : Nat := 118140960795 + 3400956 * 2 ^ 59
def prefixEnd_3400956 : Nat := 4983230072969 + 3 ^ 40 * 3400956 * 2
def baseEnd_3400956 : Nat := 1164216741861667318472863

theorem tailTrace_3400956 : CollatzResearch.WordTrace tailWord_3400956 prefixEnd_3400956 1164216741861667318472863 := by
  unfold tailWord_3400956
  simp only [CollatzResearch.WordTrace]
  refine ⟨62021527933462361943555361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82695370577949815924740481 62021527933462361943555361)
  ·
    refine ⟨46516145950096771457666521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62021527933462361943555361 46516145950096771457666521)
    ·
      refine ⟨34887109462572578593249891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46516145950096771457666521 34887109462572578593249891)
      ·
        refine ⟨52330664193858867889874837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34887109462572578593249891 52330664193858867889874837)
        ·
          refine ⟨2452999884087134432337883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52330664193858867889874837 2452999884087134432337883)
          ·
            refine ⟨3679499826130701648506825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2452999884087134432337883 3679499826130701648506825)
            ·
              refine ⟨2759624869598026236380119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3679499826130701648506825 2759624869598026236380119)
              ·
                refine ⟨4139437304397039354570179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2759624869598026236380119 4139437304397039354570179)
                ·
                  refine ⟨6209155956595559031855269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4139437304397039354570179 6209155956595559031855269)
                  ·
                    refine ⟨1164216741861667318472863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6209155956595559031855269 1164216741861667318472863)
                    ·
                      rfl

theorem cell22_3400956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_3400956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400956 prefixEnd_3400956 := by exact prefixLift 3400956
  have htrace : WordTrace (prefixWord ++ tailWord_3400956) baseStart_3400956 baseEnd_3400956 := by
    simpa [prefixWord, tailWord_3400956, baseEnd_3400956] using wordTrace_append hprefix tailTrace_3400956
  have hstable : (prefixWord ++ tailWord_3400956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400956).length < 2 ^ (prefixWord ++ tailWord_3400956).sum := by decide
  have hdescent : baseEnd_3400956 < baseStart_3400956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400997 : List Nat := [1, 3, 1, 2, 4, 1, 2, 2, 3, 3]
def baseStart_3400997 : Nat := 118140960795 + 3400997 * 2 ^ 59
def prefixEnd_3400997 : Nat := 4983230072969 + 3 ^ 40 * 3400997 * 2
def baseEnd_3400997 : Nat := 1164230776999556878197737

theorem tailTrace_3400997 : CollatzResearch.WordTrace tailWord_3400997 prefixEnd_3400997 1164230776999556878197737 := by
  unfold tailWord_3400997
  simp only [CollatzResearch.WordTrace]
  refine ⟨124044551259776187889353245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82696367506517458592902163 124044551259776187889353245)
  ·
    refine ⟨46516706722416070458507467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124044551259776187889353245 46516706722416070458507467)
    ·
      refine ⟨69775060083624105687761201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46516706722416070458507467 69775060083624105687761201)
      ·
        refine ⟨52331295062718079265820901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69775060083624105687761201 52331295062718079265820901)
        ·
          refine ⟨9812117824259639862341419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52331295062718079265820901 9812117824259639862341419)
          ·
            refine ⟨14718176736389459793512129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9812117824259639862341419 14718176736389459793512129)
            ·
              refine ⟨11038632552292094845134097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14718176736389459793512129 11038632552292094845134097)
              ·
                refine ⟨8278974414219071133850573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11038632552292094845134097 8278974414219071133850573)
                ·
                  refine ⟨3104615405332151675193965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8278974414219071133850573 3104615405332151675193965)
                  ·
                    refine ⟨1164230776999556878197737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3104615405332151675193965 1164230776999556878197737)
                    ·
                      rfl

theorem cell22_3400997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_3400997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3400997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3400997 prefixEnd_3400997 := by exact prefixLift 3400997
  have htrace : WordTrace (prefixWord ++ tailWord_3400997) baseStart_3400997 baseEnd_3400997 := by
    simpa [prefixWord, tailWord_3400997, baseEnd_3400997] using wordTrace_append hprefix tailTrace_3400997
  have hstable : (prefixWord ++ tailWord_3400997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400997).length < 2 ^ (prefixWord ++ tailWord_3400997).sum := by decide
  have hdescent : baseEnd_3400997 < baseStart_3400997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401010 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 7]
def baseStart_3401010 : Nat := 118140960795 + 3401010 * 2 ^ 59
def prefixEnd_3401010 : Nat := 4983230072969 + 3 ^ 40 * 3401010 * 2
def baseEnd_3401010 : Nat := 388078409055076392540899

theorem tailTrace_3401010 : CollatzResearch.WordTrace tailWord_3401010 prefixEnd_3401010 388078409055076392540899 := by
  unfold tailWord_3401010
  simp only [CollatzResearch.WordTrace]
  refine ⟨31011256352182272777394121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82696683605819394073050989 31011256352182272777394121)
  ·
    refine ⟨23258442264136704583045591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31011256352182272777394121 23258442264136704583045591)
    ·
      refine ⟨34887663396205056874568387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23258442264136704583045591 34887663396205056874568387)
      ·
        refine ⟨52331495094307585311852581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34887663396205056874568387 52331495094307585311852581)
        ·
          refine ⟨9812155330182672245972359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52331495094307585311852581 9812155330182672245972359)
          ·
            refine ⟨14718232995274008368958539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9812155330182672245972359 14718232995274008368958539)
            ·
              refine ⟨22077349492911012553437809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14718232995274008368958539 22077349492911012553437809)
              ·
                refine ⟨16558012119683259415078357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22077349492911012553437809 16558012119683259415078357)
                ·
                  refine ⟨388078409055076392540899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16558012119683259415078357 388078409055076392540899)
                  ·
                    rfl

theorem cell22_3401010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_3401010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401010 prefixEnd_3401010 := by exact prefixLift 3401010
  have htrace : WordTrace (prefixWord ++ tailWord_3401010) baseStart_3401010 baseEnd_3401010 := by
    simpa [prefixWord, tailWord_3401010, baseEnd_3401010] using wordTrace_append hprefix tailTrace_3401010
  have hstable : (prefixWord ++ tailWord_3401010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401010).length < 2 ^ (prefixWord ++ tailWord_3401010).sum := by decide
  have hdescent : baseEnd_3401010 < baseStart_3401010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401031 : List Nat := [1, 1, 4, 1, 2, 4, 3, 2, 1, 3]
def baseStart_3401031 : Nat := 118140960795 + 3401031 * 2 ^ 59
def prefixEnd_3401031 : Nat := 4983230072969 + 3 ^ 40 * 3401031 * 2
def baseEnd_3401031 : Nat := 1164242415894392122847633

theorem tailTrace_3401031 : CollatzResearch.WordTrace tailWord_3401031 prefixEnd_3401031 1164242415894392122847633 := by
  unfold tailWord_3401031
  simp only [CollatzResearch.WordTrace]
  refine ⟨124045791341653011696090947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82697194227768674464060631 124045791341653011696090947)
  ·
    refine ⟨186068687012479517544136421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124045791341653011696090947 186068687012479517544136421)
    ·
      refine ⟨34887878814839909539525579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186068687012479517544136421 34887878814839909539525579)
      ·
        refine ⟨52331818222259864309288369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34887878814839909539525579 52331818222259864309288369)
        ·
          refine ⟨39248863666694898231966277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52331818222259864309288369 39248863666694898231966277)
          ·
            refine ⟨7359161937505293418493677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39248863666694898231966277 7359161937505293418493677)
            ·
              refine ⟨2759685726564485031935129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7359161937505293418493677 2759685726564485031935129)
              ·
                refine ⟨2069764294923363773951347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2759685726564485031935129 2069764294923363773951347)
                ·
                  refine ⟨3104646442385045660927021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2069764294923363773951347 3104646442385045660927021)
                  ·
                    refine ⟨1164242415894392122847633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3104646442385045660927021 1164242415894392122847633)
                    ·
                      rfl

theorem cell22_3401031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_3401031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401031 prefixEnd_3401031 := by exact prefixLift 3401031
  have htrace : WordTrace (prefixWord ++ tailWord_3401031) baseStart_3401031 baseEnd_3401031 := by
    simpa [prefixWord, tailWord_3401031, baseEnd_3401031] using wordTrace_append hprefix tailTrace_3401031
  have hstable : (prefixWord ++ tailWord_3401031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401031).length < 2 ^ (prefixWord ++ tailWord_3401031).sum := by decide
  have hdescent : baseEnd_3401031 < baseStart_3401031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401040 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 3, 4]
def baseStart_3401040 : Nat := 118140960795 + 3401040 * 2 ^ 59
def prefixEnd_3401040 : Nat := 4983230072969 + 3 ^ 40 * 3401040 * 2
def baseEnd_3401040 : Nat := 1164245496778319099372605

theorem tailTrace_3401040 : CollatzResearch.WordTrace tailWord_3401040 prefixEnd_3401040 1164245496778319099372605 := by
  unfold tailWord_3401040
  simp only [CollatzResearch.WordTrace]
  refine ⟨62023059799310203116584287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82697413065746937488779049 62023059799310203116584287)
  ·
    refine ⟨93034589698965304674876431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62023059799310203116584287 93034589698965304674876431)
    ·
      refine ⟨139551884548447957012314647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93034589698965304674876431 139551884548447957012314647)
      ·
        refine ⟨209327826822671935518471971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139551884548447957012314647 209327826822671935518471971)
        ·
          refine ⟨313991740234007903277707957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209327826822671935518471971 313991740234007903277707957)
          ·
            refine ⟨29436725646938240932285121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 313991740234007903277707957 29436725646938240932285121)
            ·
              refine ⟨22077544235203680699213841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29436725646938240932285121 22077544235203680699213841)
              ·
                refine ⟨16558158176402760524410381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22077544235203680699213841 16558158176402760524410381)
                ·
                  refine ⟨6209309316151035196653893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16558158176402760524410381 6209309316151035196653893)
                  ·
                    refine ⟨1164245496778319099372605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6209309316151035196653893 1164245496778319099372605)
                    ·
                      rfl

theorem cell22_3401040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 3, 4].length) (baseStart_3401040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401040 prefixEnd_3401040 := by exact prefixLift 3401040
  have htrace : WordTrace (prefixWord ++ tailWord_3401040) baseStart_3401040 baseEnd_3401040 := by
    simpa [prefixWord, tailWord_3401040, baseEnd_3401040] using wordTrace_append hprefix tailTrace_3401040
  have hstable : (prefixWord ++ tailWord_3401040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401040).length < 2 ^ (prefixWord ++ tailWord_3401040).sum := by decide
  have hdescent : baseEnd_3401040 < baseStart_3401040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401072 : List Nat := [2, 1, 1, 1, 4, 2, 2, 5, 4]
def baseStart_3401072 : Nat := 118140960795 + 3401072 * 2 ^ 59
def prefixEnd_3401072 : Nat := 4983230072969 + 3 ^ 40 * 3401072 * 2
def baseEnd_3401072 : Nat := 388085483677427227524169

theorem tailTrace_3401072 : CollatzResearch.WordTrace tailWord_3401072 prefixEnd_3401072 388085483677427227524169 := by
  unfold tailWord_3401072
  simp only [CollatzResearch.WordTrace]
  refine ⟨62023643367252237849166735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82698191156336317132222313 62023643367252237849166735)
  ·
    refine ⟨93035465050878356773750103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62023643367252237849166735 93035465050878356773750103)
    ·
      refine ⟨139553197576317535160625155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93035465050878356773750103 139553197576317535160625155)
      ·
        refine ⟨209329796364476302740937733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139553197576317535160625155 209329796364476302740937733)
        ·
          refine ⟨39249336818339306763925825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209329796364476302740937733 39249336818339306763925825)
          ·
            refine ⟨29437002613754480072944369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39249336818339306763925825 29437002613754480072944369)
            ·
              refine ⟨22077751960315860054708277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29437002613754480072944369 22077751960315860054708277)
              ·
                refine ⟨2069789246279611880128901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22077751960315860054708277 2069789246279611880128901)
                ·
                  refine ⟨388085483677427227524169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2069789246279611880128901 388085483677427227524169)
                  ·
                    rfl

theorem cell22_3401072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 4].length) (baseStart_3401072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401072 prefixEnd_3401072 := by exact prefixLift 3401072
  have htrace : WordTrace (prefixWord ++ tailWord_3401072) baseStart_3401072 baseEnd_3401072 := by
    simpa [prefixWord, tailWord_3401072, baseEnd_3401072] using wordTrace_append hprefix tailTrace_3401072
  have hstable : (prefixWord ++ tailWord_3401072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401072).length < 2 ^ (prefixWord ++ tailWord_3401072).sum := by decide
  have hdescent : baseEnd_3401072 < baseStart_3401072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401074 : List Nat := [3, 2, 1, 2, 1, 2, 5, 1, 1, 4]
def baseStart_3401074 : Nat := 118140960795 + 3401074 * 2 ^ 59
def prefixEnd_3401074 : Nat := 4983230072969 + 3 ^ 40 * 3401074 * 2
def baseEnd_3401074 : Nat := 1164257135673154344022501

theorem tailTrace_3401074 : CollatzResearch.WordTrace tailWord_3401074 prefixEnd_3401074 1164257135673154344022501 := by
  unfold tailWord_3401074
  simp only [CollatzResearch.WordTrace]
  refine ⟨31011839920124307509976569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82698239786998153359937517 31011839920124307509976569)
  ·
    refine ⟨23258879940093230632482427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31011839920124307509976569 23258879940093230632482427)
    ·
      refine ⟨34888319910139845948723641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23258879940093230632482427 34888319910139845948723641)
      ·
        refine ⟨26166239932604884461542731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34888319910139845948723641 26166239932604884461542731)
        ·
          refine ⟨39249359898907326692314097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26166239932604884461542731 39249359898907326692314097)
          ·
            refine ⟨29437019924180495019235573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39249359898907326692314097 29437019924180495019235573)
            ·
              refine ⟨2759720617891921408053335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29437019924180495019235573 2759720617891921408053335)
              ·
                refine ⟨4139580926837882112080003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2759720617891921408053335 4139580926837882112080003)
                ·
                  refine ⟨6209371390256823168120005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4139580926837882112080003 6209371390256823168120005)
                  ·
                    refine ⟨1164257135673154344022501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6209371390256823168120005 1164257135673154344022501)
                    ·
                      rfl

theorem cell22_3401074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_3401074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401074 prefixEnd_3401074 := by exact prefixLift 3401074
  have htrace : WordTrace (prefixWord ++ tailWord_3401074) baseStart_3401074 baseEnd_3401074 := by
    simpa [prefixWord, tailWord_3401074, baseEnd_3401074] using wordTrace_append hprefix tailTrace_3401074
  have hstable : (prefixWord ++ tailWord_3401074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401074).length < 2 ^ (prefixWord ++ tailWord_3401074).sum := by decide
  have hdescent : baseEnd_3401074 < baseStart_3401074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401119 : List Nat := [1, 1, 2, 5, 1, 4, 1, 1, 2, 4]
def baseStart_3401119 : Nat := 118140960795 + 3401119 * 2 ^ 59
def prefixEnd_3401119 : Nat := 4983230072969 + 3 ^ 40 * 3401119 * 2
def baseEnd_3401119 : Nat := 1164272540092789226647363

theorem tailTrace_3401119 : CollatzResearch.WordTrace tailWord_3401119 prefixEnd_3401119 1164272540092789226647363 := by
  unfold tailWord_3401119
  simp only [CollatzResearch.WordTrace]
  refine ⟨124049000965334202725294411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82699333976889468483529607 124049000965334202725294411)
  ·
    refine ⟨186073501448001304087941617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124049000965334202725294411 186073501448001304087941617)
    ·
      refine ⟨139555126086000978065956213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186073501448001304087941617 139555126086000978065956213)
      ·
        refine ⟨13083293070562591693683395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139555126086000978065956213 13083293070562591693683395)
        ·
          refine ⟨19624939605843887540525093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13083293070562591693683395 19624939605843887540525093)
          ·
            refine ⟨3679676176095728913848455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19624939605843887540525093 3679676176095728913848455)
            ·
              refine ⟨5519514264143593370772683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3679676176095728913848455 5519514264143593370772683)
              ·
                refine ⟨8279271396215390056159025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5519514264143593370772683 8279271396215390056159025)
                ·
                  refine ⟨6209453547161542542119269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8279271396215390056159025 6209453547161542542119269)
                  ·
                    refine ⟨1164272540092789226647363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6209453547161542542119269 1164272540092789226647363)
                    ·
                      rfl

theorem cell22_3401119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 4].length) (baseStart_3401119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401119 prefixEnd_3401119 := by exact prefixLift 3401119
  have htrace : WordTrace (prefixWord ++ tailWord_3401119) baseStart_3401119 baseEnd_3401119 := by
    simpa [prefixWord, tailWord_3401119, baseEnd_3401119] using wordTrace_append hprefix tailTrace_3401119
  have hstable : (prefixWord ++ tailWord_3401119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401119).length < 2 ^ (prefixWord ++ tailWord_3401119).sum := by decide
  have hdescent : baseEnd_3401119 < baseStart_3401119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401149 : List Nat := [1, 4, 1, 2, 2, 1, 4, 1, 3, 3]
def baseStart_3401149 : Nat := 118140960795 + 3401149 * 2 ^ 59
def prefixEnd_3401149 : Nat := 4983230072969 + 3 ^ 40 * 3401149 * 2
def baseEnd_3401149 : Nat := 1164282809705879148397271

theorem tailTrace_3401149 : CollatzResearch.WordTrace tailWord_3401149 prefixEnd_3401149 1164282809705879148397271 := by
  unfold tailWord_3401149
  simp only [CollatzResearch.WordTrace]
  refine ⟨124050095155225517848886501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82700063436817011899257667 124050095155225517848886501)
  ·
    refine ⟨23259392841604784596666219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124050095155225517848886501 23259392841604784596666219)
    ·
      refine ⟨34889089262407176894999329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23259392841604784596666219 34889089262407176894999329)
      ·
        refine ⟨26166816946805382671249497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34889089262407176894999329 26166816946805382671249497)
        ·
          refine ⟨19625112710104037003437123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26166816946805382671249497 19625112710104037003437123)
          ·
            refine ⟨29437669065156055505155685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19625112710104037003437123 29437669065156055505155685)
            ·
              refine ⟨5519562949716760407216691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29437669065156055505155685 5519562949716760407216691)
              ·
                refine ⟨8279344424575140610825037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5519562949716760407216691 8279344424575140610825037)
                ·
                  refine ⟨3104754159215677729059389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8279344424575140610825037 3104754159215677729059389)
                  ·
                    refine ⟨1164282809705879148397271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3104754159215677729059389 1164282809705879148397271)
                    ·
                      rfl

theorem cell22_3401149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_3401149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401149 prefixEnd_3401149 := by exact prefixLift 3401149
  have htrace : WordTrace (prefixWord ++ tailWord_3401149) baseStart_3401149 baseEnd_3401149 := by
    simpa [prefixWord, tailWord_3401149, baseEnd_3401149] using wordTrace_append hprefix tailTrace_3401149
  have hstable : (prefixWord ++ tailWord_3401149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401149).length < 2 ^ (prefixWord ++ tailWord_3401149).sum := by decide
  have hdescent : baseEnd_3401149 < baseStart_3401149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401175 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 2, 8]
def baseStart_3401175 : Nat := 118140960795 + 3401175 * 2 ^ 59
def prefixEnd_3401175 : Nat := 4983230072969 + 3 ^ 40 * 3401175 * 2
def baseEnd_3401175 : Nat := 1164291710037223747247191

theorem tailTrace_3401175 : CollatzResearch.WordTrace tailWord_3401175 prefixEnd_3401175 1164291710037223747247191 := by
  unfold tailWord_3401175
  simp only [CollatzResearch.WordTrace]
  refine ⟨124051043453131324289332979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82700695635420882859555319 124051043453131324289332979)
  ·
    refine ⟨186076565179696986433999469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124051043453131324289332979 186076565179696986433999469)
    ·
      refine ⟨69778711942386369912749801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186076565179696986433999469 69778711942386369912749801)
      ·
        refine ⟨52334033956789777434562351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69778711942386369912749801 52334033956789777434562351)
        ·
          refine ⟨78501050935184666151843527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52334033956789777434562351 78501050935184666151843527)
          ·
            refine ⟨117751576402776999227765291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78501050935184666151843527 117751576402776999227765291)
            ·
              refine ⟨176627364604165498841647937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117751576402776999227765291 176627364604165498841647937)
              ·
                refine ⟨132470523453124124131235953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176627364604165498841647937 132470523453124124131235953)
                ·
                  refine ⟨99352892589843093098426965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132470523453124124131235953 99352892589843093098426965)
                  ·
                    refine ⟨1164291710037223747247191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99352892589843093098426965 1164291710037223747247191)
                    ·
                      rfl

theorem cell22_3401175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_3401175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401175 prefixEnd_3401175 := by exact prefixLift 3401175
  have htrace : WordTrace (prefixWord ++ tailWord_3401175) baseStart_3401175 baseEnd_3401175 := by
    simpa [prefixWord, tailWord_3401175, baseEnd_3401175] using wordTrace_append hprefix tailTrace_3401175
  have hstable : (prefixWord ++ tailWord_3401175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401175).length < 2 ^ (prefixWord ++ tailWord_3401175).sum := by decide
  have hdescent : baseEnd_3401175 < baseStart_3401175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401226 : List Nat := [3, 1, 2, 2, 2, 4, 1, 2, 1, 4]
def baseStart_3401226 : Nat := 118140960795 + 3401226 * 2 ^ 59
def prefixEnd_3401226 : Nat := 4983230072969 + 3 ^ 40 * 3401226 * 2
def baseEnd_3401226 : Nat := 1164309168379476614222035

theorem tailTrace_3401226 : CollatzResearch.WordTrace tailWord_3401226 prefixEnd_3401226 1164309168379476614222035 := by
  unfold tailWord_3401226
  simp only [CollatzResearch.WordTrace]
  refine ⟨31013225893986639999859883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82701935717297706666293021 31013225893986639999859883)
  ·
    refine ⟨46519838840979959999789825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31013225893986639999859883 46519838840979959999789825)
    ·
      refine ⟨34889879130734969999842369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46519838840979959999789825 34889879130734969999842369)
      ·
        refine ⟨26167409348051227499881777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34889879130734969999842369 26167409348051227499881777)
        ·
          refine ⟨19625557011038420624911333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26167409348051227499881777 19625557011038420624911333)
          ·
            refine ⟨3679791939569703867170875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19625557011038420624911333 3679791939569703867170875)
            ·
              refine ⟨5519687909354555800756313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3679791939569703867170875 5519687909354555800756313)
              ·
                refine ⟨4139765932015916850567235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5519687909354555800756313 4139765932015916850567235)
                ·
                  refine ⟨6209648898023875275850853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4139765932015916850567235 6209648898023875275850853)
                  ·
                    refine ⟨1164309168379476614222035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6209648898023875275850853 1164309168379476614222035)
                    ·
                      rfl

theorem cell22_3401226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_3401226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401226 prefixEnd_3401226 := by exact prefixLift 3401226
  have htrace : WordTrace (prefixWord ++ tailWord_3401226) baseStart_3401226 baseEnd_3401226 := by
    simpa [prefixWord, tailWord_3401226, baseEnd_3401226] using wordTrace_append hprefix tailTrace_3401226
  have hstable : (prefixWord ++ tailWord_3401226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401226).length < 2 ^ (prefixWord ++ tailWord_3401226).sum := by decide
  have hdescent : baseEnd_3401226 < baseStart_3401226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401269 : List Nat := [1, 3, 3, 1, 1, 5, 1, 7]
def baseStart_3401269 : Nat := 118140960795 + 3401269 * 2 ^ 59
def prefixEnd_3401269 : Nat := 4983230072969 + 3 ^ 40 * 3401269 * 2
def baseEnd_3401269 : Nat := 129369320906470981710767

theorem tailTrace_3401269 : CollatzResearch.WordTrace tailWord_3401269 prefixEnd_3401269 129369320906470981710767 := by
  unfold tailWord_3401269
  simp only [CollatzResearch.WordTrace]
  refine ⟨124054471914790778343254861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82702981276527185562169907 124054471914790778343254861)
  ·
    refine ⟨46520426968046541878720573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124054471914790778343254861 46520426968046541878720573)
    ·
      refine ⟨17445160113017453204520215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46520426968046541878720573 17445160113017453204520215)
      ·
        refine ⟨26167740169526179806780323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17445160113017453204520215 26167740169526179806780323)
        ·
          refine ⟨39251610254289269710170485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26167740169526179806780323 39251610254289269710170485)
          ·
            refine ⟨3679838461339619035328483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39251610254289269710170485 3679838461339619035328483)
            ·
              refine ⟨5519757692009428552992725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3679838461339619035328483 5519757692009428552992725)
              ·
                refine ⟨129369320906470981710767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5519757692009428552992725 129369320906470981710767)
                ·
                  rfl

theorem cell22_3401269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 7].length) (baseStart_3401269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401269 prefixEnd_3401269 := by exact prefixLift 3401269
  have htrace : WordTrace (prefixWord ++ tailWord_3401269) baseStart_3401269 baseEnd_3401269 := by
    simpa [prefixWord, tailWord_3401269, baseEnd_3401269] using wordTrace_append hprefix tailTrace_3401269
  have hstable : (prefixWord ++ tailWord_3401269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401269).length < 2 ^ (prefixWord ++ tailWord_3401269).sum := by decide
  have hdescent : baseEnd_3401269 < baseStart_3401269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401297 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 7]
def baseStart_3401297 : Nat := 118140960795 + 3401297 * 2 ^ 59
def prefixEnd_3401297 : Nat := 4983230072969 + 3 ^ 40 * 3401297 * 2
def baseEnd_3401297 : Nat := 388111157710152031898939

theorem tailTrace_3401297 : CollatzResearch.WordTrace tailWord_3401297 prefixEnd_3401297 388111157710152031898939 := by
  unfold tailWord_3401297
  simp only [CollatzResearch.WordTrace]
  refine ⟨124055493158689339125274145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82703662105792892750182763 124055493158689339125274145)
  ·
    refine ⟨93041619869017004343955609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124055493158689339125274145 93041619869017004343955609)
    ·
      refine ⟨69781214901762753257966707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93041619869017004343955609 69781214901762753257966707)
      ·
        refine ⟨104671822352644129886950061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69781214901762753257966707 104671822352644129886950061)
        ·
          refine ⟨39251933382241548707606273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104671822352644129886950061 39251933382241548707606273)
          ·
            refine ⟨29438950036681161530704705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39251933382241548707606273 29438950036681161530704705)
            ·
              refine ⟨22079212527510871148028529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29438950036681161530704705 22079212527510871148028529)
              ·
                refine ⟨16559409395633153361021397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22079212527510871148028529 16559409395633153361021397)
                ·
                  refine ⟨388111157710152031898939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16559409395633153361021397 388111157710152031898939)
                  ·
                    rfl

theorem cell22_3401297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 7].length) (baseStart_3401297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401297 prefixEnd_3401297 := by exact prefixLift 3401297
  have htrace : WordTrace (prefixWord ++ tailWord_3401297) baseStart_3401297 baseEnd_3401297 := by
    simpa [prefixWord, tailWord_3401297, baseEnd_3401297] using wordTrace_append hprefix tailTrace_3401297
  have hstable : (prefixWord ++ tailWord_3401297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401297).length < 2 ^ (prefixWord ++ tailWord_3401297).sum := by decide
  have hdescent : baseEnd_3401297 < baseStart_3401297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401352 : List Nat := [2, 1, 3, 5, 1, 2, 1, 3, 1, 3]
def baseStart_3401352 : Nat := 118140960795 + 3401352 * 2 ^ 59
def prefixEnd_3401352 : Nat := 4983230072969 + 3 ^ 40 * 3401352 * 2
def baseEnd_3401352 : Nat := 1164352300754454285571649

theorem tailTrace_3401352 : CollatzResearch.WordTrace tailWord_3401352 prefixEnd_3401352 1164352300754454285571649 := by
  unfold tailWord_3401352
  simp only [CollatzResearch.WordTrace]
  refine ⟨62028749586745041759263155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82704999448993389012350873 62028749586745041759263155)
  ·
    refine ⟨93043124380117562638894733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62028749586745041759263155 93043124380117562638894733)
    ·
      refine ⟨34891171642544085989585525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93043124380117562638894733 34891171642544085989585525)
      ·
        refine ⟨3271047341488508061523643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34891171642544085989585525 3271047341488508061523643)
        ·
          refine ⟨4906571012232762092285465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3271047341488508061523643 4906571012232762092285465)
          ·
            refine ⟨3679928259174571569214099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4906571012232762092285465 3679928259174571569214099)
            ·
              refine ⟨5519892388761857353821149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3679928259174571569214099 5519892388761857353821149)
              ·
                refine ⟨2069959645785696507682931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5519892388761857353821149 2069959645785696507682931)
                ·
                  refine ⟨3104939468678544761524397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2069959645785696507682931 3104939468678544761524397)
                  ·
                    refine ⟨1164352300754454285571649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3104939468678544761524397 1164352300754454285571649)
                    ·
                      rfl

theorem cell22_3401352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_3401352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401352 prefixEnd_3401352 := by exact prefixLift 3401352
  have htrace : WordTrace (prefixWord ++ tailWord_3401352) baseStart_3401352 baseEnd_3401352 := by
    simpa [prefixWord, tailWord_3401352, baseEnd_3401352] using wordTrace_append hprefix tailTrace_3401352
  have hstable : (prefixWord ++ tailWord_3401352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401352).length < 2 ^ (prefixWord ++ tailWord_3401352).sum := by decide
  have hdescent : baseEnd_3401352 < baseStart_3401352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401376 : List Nat := [2, 1, 1, 4, 3, 3, 1, 1, 6]
def baseStart_3401376 : Nat := 118140960795 + 3401376 * 2 ^ 59
def prefixEnd_3401376 : Nat := 4983230072969 + 3 ^ 40 * 3401376 * 2
def baseEnd_3401376 : Nat := 388120172148308740990525

theorem tailTrace_3401376 : CollatzResearch.WordTrace tailWord_3401376 prefixEnd_3401376 388120172148308740990525 := by
  unfold tailWord_3401376
  simp only [CollatzResearch.WordTrace]
  refine ⟨62029187262701567808699991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82705583016935423744933321 62029187262701567808699991)
  ·
    refine ⟨93043780894052351713049987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62029187262701567808699991 93043780894052351713049987)
    ·
      refine ⟨139565671341078527569574981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93043780894052351713049987 139565671341078527569574981)
      ·
        refine ⟨26168563376452223919295309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139565671341078527569574981 26168563376452223919295309)
        ·
          refine ⟨9813211266169583969735741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26168563376452223919295309 9813211266169583969735741)
          ·
            refine ⟨3679954224813593988650903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9813211266169583969735741 3679954224813593988650903)
            ·
              refine ⟨5519931337220390982976355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3679954224813593988650903 5519931337220390982976355)
              ·
                refine ⟨8279897005830586474464533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5519931337220390982976355 8279897005830586474464533)
                ·
                  refine ⟨388120172148308740990525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8279897005830586474464533 388120172148308740990525)
                  ·
                    rfl

theorem cell22_3401376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 6].length) (baseStart_3401376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401376 prefixEnd_3401376 := by exact prefixLift 3401376
  have htrace : WordTrace (prefixWord ++ tailWord_3401376) baseStart_3401376 baseEnd_3401376 := by
    simpa [prefixWord, tailWord_3401376, baseEnd_3401376] using wordTrace_append hprefix tailTrace_3401376
  have hstable : (prefixWord ++ tailWord_3401376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401376).length < 2 ^ (prefixWord ++ tailWord_3401376).sum := by decide
  have hdescent : baseEnd_3401376 < baseStart_3401376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401391 : List Nat := [1, 1, 2, 1, 2, 4, 3, 3, 2, 3]
def baseStart_3401391 : Nat := 118140960795 + 3401391 * 2 ^ 59
def prefixEnd_3401391 : Nat := 4983230072969 + 3 ^ 40 * 3401391 * 2
def baseEnd_3401391 : Nat := 1164365651251471183846529

theorem tailTrace_3401391 : CollatzResearch.WordTrace tailWord_3401391 prefixEnd_3401391 1164365651251471183846529 := by
  unfold tailWord_3401391
  simp only [CollatzResearch.WordTrace]
  refine ⟨124058921620348793179196027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82705947746899195452797351 124058921620348793179196027)
  ·
    refine ⟨186088382430523189768794041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124058921620348793179196027 186088382430523189768794041)
    ·
      refine ⟨139566286822892392326595531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186088382430523189768794041 139566286822892392326595531)
      ·
        refine ⟨209349430234338588489893297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139566286822892392326595531 209349430234338588489893297)
        ·
          refine ⟨157012072675753941367419973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209349430234338588489893297 157012072675753941367419973)
          ·
            refine ⟨29439763626703864006391245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157012072675753941367419973 29439763626703864006391245)
            ·
              refine ⟨11039911360013949002396717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29439763626703864006391245 11039911360013949002396717)
              ·
                refine ⟨4139966760005230875898769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11039911360013949002396717 4139966760005230875898769)
                ·
                  refine ⟨3104975070003923156924077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4139966760005230875898769 3104975070003923156924077)
                  ·
                    refine ⟨1164365651251471183846529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3104975070003923156924077 1164365651251471183846529)
                    ·
                      rfl

theorem cell22_3401391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 3].length) (baseStart_3401391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401391 prefixEnd_3401391 := by exact prefixLift 3401391
  have htrace : WordTrace (prefixWord ++ tailWord_3401391) baseStart_3401391 baseEnd_3401391 := by
    simpa [prefixWord, tailWord_3401391, baseEnd_3401391] using wordTrace_append hprefix tailTrace_3401391
  have hstable : (prefixWord ++ tailWord_3401391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401391).length < 2 ^ (prefixWord ++ tailWord_3401391).sum := by decide
  have hdescent : baseEnd_3401391 < baseStart_3401391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401404 : List Nat := [2, 2, 2, 3, 1, 2, 2, 8]
def baseStart_3401404 : Nat := 118140960795 + 3401404 * 2 ^ 59
def prefixEnd_3401404 : Nat := 4983230072969 + 3 ^ 40 * 3401404 * 2
def baseEnd_3401404 : Nat := 129374455713015942585721

theorem tailTrace_3401404 : CollatzResearch.WordTrace tailWord_3401404 prefixEnd_3401404 129374455713015942585721 := by
  unfold tailWord_3401404
  simp only [CollatzResearch.WordTrace]
  refine ⟨62029697884650848199709633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82706263846201130932946177 62029697884650848199709633)
  ·
    refine ⟨46522273413488136149782225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62029697884650848199709633 46522273413488136149782225)
    ·
      refine ⟨34891705060116102112336669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46522273413488136149782225 34891705060116102112336669)
      ·
        refine ⟨13084389397543538292126251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34891705060116102112336669 13084389397543538292126251)
        ·
          refine ⟨19626584096315307438189377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13084389397543538292126251 19626584096315307438189377)
          ·
            refine ⟨14719938072236480578642033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19626584096315307438189377 14719938072236480578642033)
            ·
              refine ⟨11039953554177360433981525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14719938072236480578642033 11039953554177360433981525)
              ·
                refine ⟨129374455713015942585721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11039953554177360433981525 129374455713015942585721)
                ·
                  rfl

theorem cell22_3401404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 8].length) (baseStart_3401404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401404 prefixEnd_3401404 := by exact prefixLift 3401404
  have htrace : WordTrace (prefixWord ++ tailWord_3401404) baseStart_3401404 baseEnd_3401404 := by
    simpa [prefixWord, tailWord_3401404, baseEnd_3401404] using wordTrace_append hprefix tailTrace_3401404
  have hstable : (prefixWord ++ tailWord_3401404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401404).length < 2 ^ (prefixWord ++ tailWord_3401404).sum := by decide
  have hdescent : baseEnd_3401404 < baseStart_3401404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401406 : List Nat := [4, 2, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_3401406 : Nat := 118140960795 + 3401406 * 2 ^ 59
def prefixEnd_3401406 : Nat := 4983230072969 + 3 ^ 40 * 3401406 * 2
def baseEnd_3401406 : Nat := 1164370786058016144721483

theorem tailTrace_3401406 : CollatzResearch.WordTrace tailWord_3401406 prefixEnd_3401406 1164370786058016144721483 := by
  unfold tailWord_3401406
  simp only [CollatzResearch.WordTrace]
  refine ⟨15507433589411806342624009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82706312476862967160661381 15507433589411806342624009)
  ·
    refine ⟨11630575192058854756968007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15507433589411806342624009 11630575192058854756968007)
    ·
      refine ⟨17445862788088282135452011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11630575192058854756968007 17445862788088282135452011)
      ·
        refine ⟨26168794182132423203178017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17445862788088282135452011 26168794182132423203178017)
        ·
          refine ⟨19626595636599317402383513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26168794182132423203178017 19626595636599317402383513)
          ·
            refine ⟨14719946727449488051787635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19626595636599317402383513 14719946727449488051787635)
            ·
              refine ⟨22079920091174232077681453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14719946727449488051787635 22079920091174232077681453)
              ·
                refine ⟨8279970034190337029130545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22079920091174232077681453 8279970034190337029130545)
                ·
                  refine ⟨6209977525642752771847909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8279970034190337029130545 6209977525642752771847909)
                  ·
                    refine ⟨1164370786058016144721483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6209977525642752771847909 1164370786058016144721483)
                    ·
                      rfl

theorem cell22_3401406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_3401406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401406 prefixEnd_3401406 := by exact prefixLift 3401406
  have htrace : WordTrace (prefixWord ++ tailWord_3401406) baseStart_3401406 baseEnd_3401406 := by
    simpa [prefixWord, tailWord_3401406, baseEnd_3401406] using wordTrace_append hprefix tailTrace_3401406
  have hstable : (prefixWord ++ tailWord_3401406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401406).length < 2 ^ (prefixWord ++ tailWord_3401406).sum := by decide
  have hdescent : baseEnd_3401406 < baseStart_3401406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401421 : List Nat := [1, 6, 2, 1, 1, 11]
def baseStart_3401421 : Nat := 118140960795 + 3401421 * 2 ^ 59
def prefixEnd_3401421 : Nat := 4983230072969 + 3 ^ 40 * 3401421 * 2
def baseEnd_3401421 : Nat := 14375011368698285254277

theorem tailTrace_3401421 : CollatzResearch.WordTrace tailWord_3401421 prefixEnd_3401421 14375011368698285254277 := by
  unfold tailWord_3401421
  simp only [CollatzResearch.WordTrace]
  refine ⟨124060015810240108302788117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82706677206826738868525411 124060015810240108302788117)
  ·
    refine ⟨5815313241105005076693193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 124060015810240108302788117 5815313241105005076693193)
    ·
      refine ⟨4361484930828753807519895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5815313241105005076693193 4361484930828753807519895)
      ·
        refine ⟨6542227396243130711279843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4361484930828753807519895 6542227396243130711279843)
        ·
          refine ⟨9813341094364696066919765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6542227396243130711279843 9813341094364696066919765)
          ·
            refine ⟨14375011368698285254277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9813341094364696066919765 14375011368698285254277)
            ·
              rfl

theorem cell22_3401421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 11].length) (baseStart_3401421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401421 prefixEnd_3401421 := by exact prefixLift 3401421
  have htrace : WordTrace (prefixWord ++ tailWord_3401421) baseStart_3401421 baseEnd_3401421 := by
    simpa [prefixWord, tailWord_3401421, baseEnd_3401421] using wordTrace_append hprefix tailTrace_3401421
  have hstable : (prefixWord ++ tailWord_3401421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401421).length < 2 ^ (prefixWord ++ tailWord_3401421).sum := by decide
  have hdescent : baseEnd_3401421 < baseStart_3401421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401434 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 2, 6]
def baseStart_3401434 : Nat := 118140960795 + 3401434 * 2 ^ 59
def prefixEnd_3401434 : Nat := 4983230072969 + 3 ^ 40 * 3401434 * 2
def baseEnd_3401434 : Nat := 1164380371030233405021397

theorem tailTrace_3401434 : CollatzResearch.WordTrace tailWord_3401434 prefixEnd_3401434 1164380371030233405021397 := by
  unfold tailWord_3401434
  simp only [CollatzResearch.WordTrace]
  refine ⟨31015122489798252880752839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82706993306128674348674237 31015122489798252880752839)
  ·
    refine ⟨46522683734697379321129259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31015122489798252880752839 46522683734697379321129259)
    ·
      refine ⟨69784025602046068981693889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46522683734697379321129259 69784025602046068981693889)
      ·
        refine ⟨52338019201534551736270417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69784025602046068981693889 52338019201534551736270417)
        ·
          refine ⟨39253514401150913802202813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52338019201534551736270417 39253514401150913802202813)
          ·
            refine ⟨14720067900431592675826055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39253514401150913802202813 14720067900431592675826055)
            ·
              refine ⟨22080101850647389013739083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14720067900431592675826055 22080101850647389013739083)
              ·
                refine ⟨33120152775971083520608625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22080101850647389013739083 33120152775971083520608625)
                ·
                  refine ⟨24840114581978312640456469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33120152775971083520608625 24840114581978312640456469)
                  ·
                    refine ⟨1164380371030233405021397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24840114581978312640456469 1164380371030233405021397)
                    ·
                      rfl

theorem cell22_3401434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_3401434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401434 prefixEnd_3401434 := by exact prefixLift 3401434
  have htrace : WordTrace (prefixWord ++ tailWord_3401434) baseStart_3401434 baseEnd_3401434 := by
    simpa [prefixWord, tailWord_3401434, baseEnd_3401434] using wordTrace_append hprefix tailTrace_3401434
  have hstable : (prefixWord ++ tailWord_3401434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401434).length < 2 ^ (prefixWord ++ tailWord_3401434).sum := by decide
  have hdescent : baseEnd_3401434 < baseStart_3401434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401453 : List Nat := [1, 5, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_3401453 : Nat := 118140960795 + 3401453 * 2 ^ 59
def prefixEnd_3401453 : Nat := 4983230072969 + 3 ^ 40 * 3401453 * 2
def baseEnd_3401453 : Nat := 1164386875118523688796339

theorem tailTrace_3401453 : CollatzResearch.WordTrace tailWord_3401453 prefixEnd_3401453 1164386875118523688796339 := by
  unfold tailWord_3401453
  simp only [CollatzResearch.WordTrace]
  refine ⟨124061182946124177767953013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82707455297416118511968675 124061182946124177767953013)
  ·
    refine ⟨11630735901199141665745595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124061182946124177767953013 11630735901199141665745595)
    ·
      refine ⟨17446103851798712498618393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11630735901199141665745595 17446103851798712498618393)
      ·
        refine ⟨13084577888849034373963795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17446103851798712498618393 13084577888849034373963795)
        ·
          refine ⟨19626866833273551560945693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13084577888849034373963795 19626866833273551560945693)
          ·
            refine ⟨7360075062477581835354635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19626866833273551560945693 7360075062477581835354635)
            ·
              refine ⟨11040112593716372753031953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7360075062477581835354635 11040112593716372753031953)
              ·
                refine ⟨8280084445287279564773965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11040112593716372753031953 8280084445287279564773965)
                ·
                  refine ⟨3105031666982729836790237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8280084445287279564773965 3105031666982729836790237)
                  ·
                    refine ⟨1164386875118523688796339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3105031666982729836790237 1164386875118523688796339)
                    ·
                      rfl

theorem cell22_3401453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_3401453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401453 prefixEnd_3401453 := by exact prefixLift 3401453
  have htrace : WordTrace (prefixWord ++ tailWord_3401453) baseStart_3401453 baseEnd_3401453 := by
    simpa [prefixWord, tailWord_3401453, baseEnd_3401453] using wordTrace_append hprefix tailTrace_3401453
  have hstable : (prefixWord ++ tailWord_3401453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401453).length < 2 ^ (prefixWord ++ tailWord_3401453).sum := by decide
  have hdescent : baseEnd_3401453 < baseStart_3401453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401528 : List Nat := [2, 1, 2, 1, 3, 3, 3, 3, 4]
def baseStart_3401528 : Nat := 118140960795 + 3401528 * 2 ^ 59
def prefixEnd_3401528 : Nat := 4983230072969 + 3 ^ 40 * 3401528 * 2
def baseEnd_3401528 : Nat := 388137516383749497723703

theorem tailTrace_3401528 : CollatzResearch.WordTrace tailWord_3401528 prefixEnd_3401528 388137516383749497723703 := by
  unfold tailWord_3401528
  simp only [CollatzResearch.WordTrace]
  refine ⟨62031959210426232788466619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82709278947234977051288825 62031959210426232788466619)
  ·
    refine ⟨93047938815639349182699929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62031959210426232788466619 93047938815639349182699929)
    ·
      refine ⟨69785954111729511887024947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93047938815639349182699929 69785954111729511887024947)
      ·
        refine ⟨104678931167594267830537421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69785954111729511887024947 104678931167594267830537421)
        ·
          refine ⟨39254599187847850436451533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104678931167594267830537421 39254599187847850436451533)
          ·
            refine ⟨14720474695442943913669325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39254599187847850436451533 14720474695442943913669325)
            ·
              refine ⟨5520178010791103967625997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14720474695442943913669325 5520178010791103967625997)
              ·
                refine ⟨2070066754046663987859749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5520178010791103967625997 2070066754046663987859749)
                ·
                  refine ⟨388137516383749497723703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2070066754046663987859749 388137516383749497723703)
                  ·
                    rfl

theorem cell22_3401528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 4].length) (baseStart_3401528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401528 prefixEnd_3401528 := by exact prefixLift 3401528
  have htrace : WordTrace (prefixWord ++ tailWord_3401528) baseStart_3401528 baseEnd_3401528 := by
    simpa [prefixWord, tailWord_3401528, baseEnd_3401528] using wordTrace_append hprefix tailTrace_3401528
  have hstable : (prefixWord ++ tailWord_3401528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401528).length < 2 ^ (prefixWord ++ tailWord_3401528).sum := by decide
  have hdescent : baseEnd_3401528 < baseStart_3401528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401539 : List Nat := [1, 1, 1, 3, 1, 5, 10]
def baseStart_3401539 : Nat := 118140960795 + 3401539 * 2 ^ 59
def prefixEnd_3401539 : Nat := 4983230072969 + 3 ^ 40 * 3401539 * 2
def baseEnd_3401539 : Nat := 43126530173186967820225

theorem tailTrace_3401539 : CollatzResearch.WordTrace tailWord_3401539 prefixEnd_3401539 43126530173186967820225 := by
  unfold tailWord_3401539
  simp only [CollatzResearch.WordTrace]
  refine ⟨124064319623812614455583671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82709546415875076303722447 124064319623812614455583671)
  ·
    refine ⟨186096479435718921683375507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124064319623812614455583671 186096479435718921683375507)
    ·
      refine ⟨279144719153578382525063261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186096479435718921683375507 279144719153578382525063261)
      ·
        refine ⟨104679269682591893446898723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279144719153578382525063261 104679269682591893446898723)
        ·
          refine ⟨157018904523887840170348085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104679269682591893446898723 157018904523887840170348085)
          ·
            refine ⟨14720522299114485015970133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157018904523887840170348085 14720522299114485015970133)
            ·
              refine ⟨43126530173186967820225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14720522299114485015970133 43126530173186967820225)
              ·
                rfl

theorem cell22_3401539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 10].length) (baseStart_3401539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401539 prefixEnd_3401539 := by exact prefixLift 3401539
  have htrace : WordTrace (prefixWord ++ tailWord_3401539) baseStart_3401539 baseEnd_3401539 := by
    simpa [prefixWord, tailWord_3401539, baseEnd_3401539] using wordTrace_append hprefix tailTrace_3401539
  have hstable : (prefixWord ++ tailWord_3401539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401539).length < 2 ^ (prefixWord ++ tailWord_3401539).sum := by decide
  have hdescent : baseEnd_3401539 < baseStart_3401539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401541 : List Nat := [1, 3, 1, 1, 1, 2, 5, 2, 2, 4]
def baseStart_3401541 : Nat := 118140960795 + 3401541 * 2 ^ 59
def prefixEnd_3401541 : Nat := 4983230072969 + 3 ^ 40 * 3401541 * 2
def baseEnd_3401541 : Nat := 1164416999316920792596069

theorem tailTrace_3401541 : CollatzResearch.WordTrace tailWord_3401541 prefixEnd_3401541 1164416999316920792596069 := by
  unfold tailWord_3401541
  simp only [CollatzResearch.WordTrace]
  refine ⟨124064392569805368797156477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82709595046536912531437651 124064392569805368797156477)
  ·
    refine ⟨46524147213677013298933679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124064392569805368797156477 46524147213677013298933679)
    ·
      refine ⟨69786220820515519948400519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46524147213677013298933679 69786220820515519948400519)
      ·
        refine ⟨104679331230773279922600779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69786220820515519948400519 104679331230773279922600779)
        ·
          refine ⟨157018996846159919883901169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104679331230773279922600779 157018996846159919883901169)
          ·
            refine ⟨117764247634619939912925877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157018996846159919883901169 117764247634619939912925877)
            ·
              refine ⟨11040398215745619366836801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117764247634619939912925877 11040398215745619366836801)
              ·
                refine ⟨8280298661809214525127601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11040398215745619366836801 8280298661809214525127601)
                ·
                  refine ⟨6210223996356910893845701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8280298661809214525127601 6210223996356910893845701)
                  ·
                    refine ⟨1164416999316920792596069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6210223996356910893845701 1164416999316920792596069)
                    ·
                      rfl

theorem cell22_3401541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_3401541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401541 prefixEnd_3401541 := by exact prefixLift 3401541
  have htrace : WordTrace (prefixWord ++ tailWord_3401541) baseStart_3401541 baseEnd_3401541 := by
    simpa [prefixWord, tailWord_3401541, baseEnd_3401541] using wordTrace_append hprefix tailTrace_3401541
  have hstable : (prefixWord ++ tailWord_3401541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401541).length < 2 ^ (prefixWord ++ tailWord_3401541).sum := by decide
  have hdescent : baseEnd_3401541 < baseStart_3401541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401556 : List Nat := [2, 4, 1, 1, 3, 1, 1, 9]
def baseStart_3401556 : Nat := 118140960795 + 3401556 * 2 ^ 59
def prefixEnd_3401556 : Nat := 4983230072969 + 3 ^ 40 * 3401556 * 2
def baseEnd_3401556 : Nat := 129380237124829528163447

theorem tailTrace_3401556 : CollatzResearch.WordTrace tailWord_3401556 prefixEnd_3401556 129380237124829528163447 := by
  unfold tailWord_3401556
  simp only [CollatzResearch.WordTrace]
  refine ⟨62032469832375513179476261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82709959776500684239301681 62032469832375513179476261)
  ·
    refine ⟨11631088093570408721151799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62032469832375513179476261 11631088093570408721151799)
    ·
      refine ⟨17446632140355613081727699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11631088093570408721151799 17446632140355613081727699)
      ·
        refine ⟨26169948210533419622591549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17446632140355613081727699 26169948210533419622591549)
        ·
          refine ⟨9813730578950032358471831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26169948210533419622591549 9813730578950032358471831)
          ·
            refine ⟨14720595868425048537707747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9813730578950032358471831 14720595868425048537707747)
            ·
              refine ⟨22080893802637572806561621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14720595868425048537707747 22080893802637572806561621)
              ·
                refine ⟨129380237124829528163447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22080893802637572806561621 129380237124829528163447)
                ·
                  rfl

theorem cell22_3401556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 9].length) (baseStart_3401556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401556 prefixEnd_3401556 := by exact prefixLift 3401556
  have htrace : WordTrace (prefixWord ++ tailWord_3401556) baseStart_3401556 baseEnd_3401556 := by
    simpa [prefixWord, tailWord_3401556, baseEnd_3401556] using wordTrace_append hprefix tailTrace_3401556
  have hstable : (prefixWord ++ tailWord_3401556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401556).length < 2 ^ (prefixWord ++ tailWord_3401556).sum := by decide
  have hdescent : baseEnd_3401556 < baseStart_3401556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401605 : List Nat := [1, 3, 1, 1, 3, 2, 3, 4, 1, 3]
def baseStart_3401605 : Nat := 118140960795 + 3401605 * 2 ^ 59
def prefixEnd_3401605 : Nat := 4983230072969 + 3 ^ 40 * 3401605 * 2
def baseEnd_3401605 : Nat := 1164438907824845958995873

theorem tailTrace_3401605 : CollatzResearch.WordTrace tailWord_3401605 prefixEnd_3401605 1164438907824845958995873 := by
  unfold tailWord_3401605
  simp only [CollatzResearch.WordTrace]
  refine ⟨124066726841573507727486269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82711151227715671818324179 124066726841573507727486269)
  ·
    refine ⟨46525022565590065397807351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124066726841573507727486269 46525022565590065397807351)
    ·
      refine ⟨69787533848385098096711027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46525022565590065397807351 69787533848385098096711027)
      ·
        refine ⟨104681300772577647145066541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69787533848385098096711027 104681300772577647145066541)
        ·
          refine ⟨39255487789716617679399953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104681300772577647145066541 39255487789716617679399953)
          ·
            refine ⟨29441615842287463259549965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39255487789716617679399953 29441615842287463259549965)
            ·
              refine ⟨11040605940857798722331237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29441615842287463259549965 11040605940857798722331237)
              ·
                refine ⟨2070113613910837260437107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11040605940857798722331237 2070113613910837260437107)
                ·
                  refine ⟨3105170420866255890655661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2070113613910837260437107 3105170420866255890655661)
                  ·
                    refine ⟨1164438907824845958995873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3105170420866255890655661 1164438907824845958995873)
                    ·
                      rfl

theorem cell22_3401605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 1, 3].length) (baseStart_3401605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401605 prefixEnd_3401605 := by exact prefixLift 3401605
  have htrace : WordTrace (prefixWord ++ tailWord_3401605) baseStart_3401605 baseEnd_3401605 := by
    simpa [prefixWord, tailWord_3401605, baseEnd_3401605] using wordTrace_append hprefix tailTrace_3401605
  have hstable : (prefixWord ++ tailWord_3401605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401605).length < 2 ^ (prefixWord ++ tailWord_3401605).sum := by decide
  have hdescent : baseEnd_3401605 < baseStart_3401605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401663 : List Nat := [1, 1, 2, 2, 2, 1, 3, 6, 4]
def baseStart_3401663 : Nat := 118140960795 + 3401663 * 2 ^ 59
def prefixEnd_3401663 : Nat := 4983230072969 + 3 ^ 40 * 3401663 * 2
def baseEnd_3401663 : Nat := 388152920803384380348565

theorem tailTrace_3401663 : CollatzResearch.WordTrace tailWord_3401663 prefixEnd_3401663 388152920803384380348565 := by
  unfold tailWord_3401663
  simp only [CollatzResearch.WordTrace]
  refine ⟨124068842275363383633097643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82712561516908922422065095 124068842275363383633097643)
  ·
    refine ⟨186103263413045075449646465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124068842275363383633097643 186103263413045075449646465)
    ·
      refine ⟨139577447559783806587234849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186103263413045075449646465 139577447559783806587234849)
      ·
        refine ⟨104683085669837854940426137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139577447559783806587234849 104683085669837854940426137)
        ·
          refine ⟨78512314252378391205319603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104683085669837854940426137 78512314252378391205319603)
          ·
            refine ⟨117768471378567586807979405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78512314252378391205319603 117768471378567586807979405)
            ·
              refine ⟨44163176766962845052992277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117768471378567586807979405 44163176766962845052992277)
              ·
                refine ⟨2070148910951383361859013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44163176766962845052992277 2070148910951383361859013)
                ·
                  refine ⟨388152920803384380348565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2070148910951383361859013 388152920803384380348565)
                  ·
                    rfl

theorem cell22_3401663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 4].length) (baseStart_3401663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401663 prefixEnd_3401663 := by exact prefixLift 3401663
  have htrace : WordTrace (prefixWord ++ tailWord_3401663) baseStart_3401663 baseEnd_3401663 := by
    simpa [prefixWord, tailWord_3401663, baseEnd_3401663] using wordTrace_append hprefix tailTrace_3401663
  have hstable : (prefixWord ++ tailWord_3401663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401663).length < 2 ^ (prefixWord ++ tailWord_3401663).sum := by decide
  have hdescent : baseEnd_3401663 < baseStart_3401663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401682 : List Nat := [3, 2, 2, 3, 2, 1, 2, 2, 1, 4]
def baseStart_3401682 : Nat := 118140960795 + 3401682 * 2 ^ 59
def prefixEnd_3401682 : Nat := 4983230072969 + 3 ^ 40 * 3401682 * 2
def baseEnd_3401682 : Nat := 1164465266498443424820637

theorem tailTrace_3401682 : CollatzResearch.WordTrace tailWord_3401682 prefixEnd_3401682 1164465266498443424820637 := by
  unfold tailWord_3401682
  simp only [CollatzResearch.WordTrace]
  refine ⟨31017383815573637469509825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82713023508196366585359533 31017383815573637469509825)
  ·
    refine ⟨23263037861680228102132369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31017383815573637469509825 23263037861680228102132369)
    ·
      refine ⟨17447278396260171076599277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23263037861680228102132369 17447278396260171076599277)
      ·
        refine ⟨6542729398597564153724729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17447278396260171076599277 6542729398597564153724729)
        ·
          refine ⟨4907047048948173115293547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6542729398597564153724729 4907047048948173115293547)
          ·
            refine ⟨7360570573422259672940321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4907047048948173115293547 7360570573422259672940321)
            ·
              refine ⟨5520427930066694754705241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7360570573422259672940321 5520427930066694754705241)
              ·
                refine ⟨4140320947550021066028931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5520427930066694754705241 4140320947550021066028931)
                ·
                  refine ⟨6210481421325031599043397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4140320947550021066028931 6210481421325031599043397)
                  ·
                    refine ⟨1164465266498443424820637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6210481421325031599043397 1164465266498443424820637)
                    ·
                      rfl

theorem cell22_3401682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_3401682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401682 prefixEnd_3401682 := by exact prefixLift 3401682
  have htrace : WordTrace (prefixWord ++ tailWord_3401682) baseStart_3401682 baseEnd_3401682 := by
    simpa [prefixWord, tailWord_3401682, baseEnd_3401682] using wordTrace_append hprefix tailTrace_3401682
  have hstable : (prefixWord ++ tailWord_3401682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401682).length < 2 ^ (prefixWord ++ tailWord_3401682).sum := by decide
  have hdescent : baseEnd_3401682 < baseStart_3401682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401710 : List Nat := [4, 1, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_3401710 : Nat := 118140960795 + 3401710 * 2 ^ 59
def prefixEnd_3401710 : Nat := 4983230072969 + 3 ^ 40 * 3401710 * 2
def baseEnd_3401710 : Nat := 1164474851470660685120551

theorem tailTrace_3401710 : CollatzResearch.WordTrace tailWord_3401710 prefixEnd_3401710 1164474851470660685120551 := by
  unfold tailWord_3401710
  simp only [CollatzResearch.WordTrace]
  refine ⟨15508819563274138832507323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82713704337462073773372389 15508819563274138832507323)
  ·
    refine ⟨23263229344911208248760985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15508819563274138832507323 23263229344911208248760985)
    ·
      refine ⟨17447422008683406186570739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23263229344911208248760985 17447422008683406186570739)
      ·
        refine ⟨26171133013025109279856109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17447422008683406186570739 26171133013025109279856109)
        ·
          refine ⟨9814174879884415979946041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26171133013025109279856109 9814174879884415979946041)
          ·
            refine ⟨7360631159913311984959531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9814174879884415979946041 7360631159913311984959531)
            ·
              refine ⟨11040946739869967977439297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7360631159913311984959531 11040946739869967977439297)
              ·
                refine ⟨8280710054902475983079473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11040946739869967977439297 8280710054902475983079473)
                ·
                  refine ⟨6210532541176856987309605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8280710054902475983079473 6210532541176856987309605)
                  ·
                    refine ⟨1164474851470660685120551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6210532541176856987309605 1164474851470660685120551)
                    ·
                      rfl

theorem cell22_3401710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_3401710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401710 prefixEnd_3401710 := by exact prefixLift 3401710
  have htrace : WordTrace (prefixWord ++ tailWord_3401710) baseStart_3401710 baseEnd_3401710 := by
    simpa [prefixWord, tailWord_3401710, baseEnd_3401710] using wordTrace_append hprefix tailTrace_3401710
  have hstable : (prefixWord ++ tailWord_3401710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401710).length < 2 ^ (prefixWord ++ tailWord_3401710).sum := by decide
  have hdescent : baseEnd_3401710 < baseStart_3401710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401770 : List Nat := [3, 1, 4, 1, 2, 1, 1, 4, 5]
def baseStart_3401770 : Nat := 118140960795 + 3401770 * 2 ^ 59
def prefixEnd_3401770 : Nat := 4983230072969 + 3 ^ 40 * 3401770 * 2
def baseEnd_3401770 : Nat := 388165130232280176206789

theorem tailTrace_3401770 : CollatzResearch.WordTrace tailWord_3401770 prefixEnd_3401770 388165130232280176206789 := by
  unfold tailWord_3401770
  simp only [CollatzResearch.WordTrace]
  refine ⟨31018186221493935226810691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82715163257317160604828509 31018186221493935226810691)
  ·
    refine ⟨46527279332240902840216037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31018186221493935226810691 46527279332240902840216037)
    ·
      refine ⟨8723864874795169282540507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46527279332240902840216037 8723864874795169282540507)
      ·
        refine ⟨13085797312192753923810761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8723864874795169282540507 13085797312192753923810761)
        ·
          refine ⟨9814347984144565442858071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13085797312192753923810761 9814347984144565442858071)
          ·
            refine ⟨14721521976216848164287107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9814347984144565442858071 14721521976216848164287107)
            ·
              refine ⟨22082282964325272246430661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14721521976216848164287107 22082282964325272246430661)
              ·
                refine ⟨4140428055810988546205749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22082282964325272246430661 4140428055810988546205749)
                ·
                  refine ⟨388165130232280176206789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4140428055810988546205749 388165130232280176206789)
                  ·
                    rfl

theorem cell22_3401770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_3401770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401770 prefixEnd_3401770 := by exact prefixLift 3401770
  have htrace : WordTrace (prefixWord ++ tailWord_3401770) baseStart_3401770 baseEnd_3401770 := by
    simpa [prefixWord, tailWord_3401770, baseEnd_3401770] using wordTrace_append hprefix tailTrace_3401770
  have hstable : (prefixWord ++ tailWord_3401770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401770).length < 2 ^ (prefixWord ++ tailWord_3401770).sum := by decide
  have hdescent : baseEnd_3401770 < baseStart_3401770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401774 : List Nat := [4, 1, 3, 1, 1, 3, 1, 4, 1, 3]
def baseStart_3401774 : Nat := 118140960795 + 3401774 * 2 ^ 59
def prefixEnd_3401774 : Nat := 4983230072969 + 3 ^ 40 * 3401774 * 2
def baseEnd_3401774 : Nat := 1164496759978585851520355

theorem tailTrace_3401774 : CollatzResearch.WordTrace tailWord_3401774 prefixEnd_3401774 1164496759978585851520355 := by
  unfold tailWord_3401774
  simp only [CollatzResearch.WordTrace]
  refine ⟨15509111347245156198798547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82715260518640833060258917 15509111347245156198798547)
  ·
    refine ⟨23263667020867734298197821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15509111347245156198798547 23263667020867734298197821)
    ·
      refine ⟨8723875132825400361824183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23263667020867734298197821 8723875132825400361824183)
      ·
        refine ⟨13085812699238100542736275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8723875132825400361824183 13085812699238100542736275)
        ·
          refine ⟨19628719048857150814104413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13085812699238100542736275 19628719048857150814104413)
          ·
            refine ⟨7360769643321431555289155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19628719048857150814104413 7360769643321431555289155)
            ·
              refine ⟨11041154464982147332933733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7360769643321431555289155 11041154464982147332933733)
              ·
                refine ⟨2070216462184152624925075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11041154464982147332933733 2070216462184152624925075)
                ·
                  refine ⟨3105324693276228937387613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2070216462184152624925075 3105324693276228937387613)
                  ·
                    refine ⟨1164496759978585851520355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3105324693276228937387613 1164496759978585851520355)
                    ·
                      rfl

theorem cell22_3401774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_3401774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401774 prefixEnd_3401774 := by exact prefixLift 3401774
  have htrace : WordTrace (prefixWord ++ tailWord_3401774) baseStart_3401774 baseEnd_3401774 := by
    simpa [prefixWord, tailWord_3401774, baseEnd_3401774] using wordTrace_append hprefix tailTrace_3401774
  have hstable : (prefixWord ++ tailWord_3401774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401774).length < 2 ^ (prefixWord ++ tailWord_3401774).sum := by decide
  have hdescent : baseEnd_3401774 < baseStart_3401774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401783 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 3, 4]
def baseStart_3401783 : Nat := 118140960795 + 3401783 * 2 ^ 59
def prefixEnd_3401783 : Nat := 4983230072969 + 3 ^ 40 * 3401783 * 2
def baseEnd_3401783 : Nat := 1164499840862512828045327

theorem tailTrace_3401783 : CollatzResearch.WordTrace tailWord_3401783 prefixEnd_3401783 1164499840862512828045327 := by
  unfold tailWord_3401783
  simp only [CollatzResearch.WordTrace]
  refine ⟨124073219034928644127466003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82715479356619096084977335 124073219034928644127466003)
  ·
    refine ⟨186109828552392966191199005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124073219034928644127466003 186109828552392966191199005)
    ·
      refine ⟨69791185707147362321699627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186109828552392966191199005 69791185707147362321699627)
      ·
        refine ⟨104686778560721043482549441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69791185707147362321699627 104686778560721043482549441)
        ·
          refine ⟨78515083920540782611912081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104686778560721043482549441 78515083920540782611912081)
          ·
            refine ⟨58886312940405586958934061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78515083920540782611912081 58886312940405586958934061)
            ·
              refine ⟨22082367352652095109600273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58886312940405586958934061 22082367352652095109600273)
              ·
                refine ⟨16561775514489071332200205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22082367352652095109600273 16561775514489071332200205)
                ·
                  refine ⟨6210665817933401749575077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16561775514489071332200205 6210665817933401749575077)
                  ·
                    refine ⟨1164499840862512828045327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6210665817933401749575077 1164499840862512828045327)
                    ·
                      rfl

theorem cell22_3401783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_3401783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401783 prefixEnd_3401783 := by exact prefixLift 3401783
  have htrace : WordTrace (prefixWord ++ tailWord_3401783) baseStart_3401783 baseEnd_3401783 := by
    simpa [prefixWord, tailWord_3401783, baseEnd_3401783] using wordTrace_append hprefix tailTrace_3401783
  have hstable : (prefixWord ++ tailWord_3401783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401783).length < 2 ^ (prefixWord ++ tailWord_3401783).sum := by decide
  have hdescent : baseEnd_3401783 < baseStart_3401783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401785 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 2, 5]
def baseStart_3401785 : Nat := 118140960795 + 3401785 * 2 ^ 59
def prefixEnd_3401785 : Nat := 4983230072969 + 3 ^ 40 * 3401785 * 2
def baseEnd_3401785 : Nat := 1164500525503385489495321

theorem tailTrace_3401785 : CollatzResearch.WordTrace tailWord_3401785 prefixEnd_3401785 1164500525503385489495321 := by
  unfold tailWord_3401785
  simp only [CollatzResearch.WordTrace]
  refine ⟨124073291980921398469038809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82715527987280932312692539 124073291980921398469038809)
  ·
    refine ⟨93054968985691048851779107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124073291980921398469038809 93054968985691048851779107)
    ·
      refine ⟨139582453478536573277668661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93054968985691048851779107 139582453478536573277668661)
      ·
        refine ⟨13085855013612803744781437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139582453478536573277668661 13085855013612803744781437)
        ·
          refine ⟨4907195630104801404293039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13085855013612803744781437 4907195630104801404293039)
          ·
            refine ⟨7360793445157202106439559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4907195630104801404293039 7360793445157202106439559)
            ·
              refine ⟨11041190167735803159659339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7360793445157202106439559 11041190167735803159659339)
              ·
                refine ⟨16561785251603704739489009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11041190167735803159659339 16561785251603704739489009)
                ·
                  refine ⟨12421338938702778554616757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16561785251603704739489009 12421338938702778554616757)
                  ·
                    refine ⟨1164500525503385489495321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12421338938702778554616757 1164500525503385489495321)
                    ·
                      rfl

theorem cell22_3401785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 5].length) (baseStart_3401785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401785 prefixEnd_3401785 := by exact prefixLift 3401785
  have htrace : WordTrace (prefixWord ++ tailWord_3401785) baseStart_3401785 baseEnd_3401785 := by
    simpa [prefixWord, tailWord_3401785, baseEnd_3401785] using wordTrace_append hprefix tailTrace_3401785
  have hstable : (prefixWord ++ tailWord_3401785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401785).length < 2 ^ (prefixWord ++ tailWord_3401785).sum := by decide
  have hdescent : baseEnd_3401785 < baseStart_3401785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401815 : List Nat := [1, 1, 3, 2, 2, 1, 3, 5, 4]
def baseStart_3401815 : Nat := 118140960795 + 3401815 * 2 ^ 59
def prefixEnd_3401815 : Nat := 4983230072969 + 3 ^ 40 * 3401815 * 2
def baseEnd_3401815 : Nat := 388170265038825137081743

theorem tailTrace_3401815 : CollatzResearch.WordTrace tailWord_3401815 prefixEnd_3401815 388170265038825137081743 := by
  unfold tailWord_3401815
  simp only [CollatzResearch.WordTrace]
  refine ⟨124074386170812713592630899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82716257447208475728420599 124074386170812713592630899)
  ·
    refine ⟨186111579256219070388946349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124074386170812713592630899 186111579256219070388946349)
    ·
      refine ⟨69791842221082151395854881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186111579256219070388946349 69791842221082151395854881)
      ·
        refine ⟨52343881665811613546891161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69791842221082151395854881 52343881665811613546891161)
        ·
          refine ⟨39257911249358710160168371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52343881665811613546891161 39257911249358710160168371)
          ·
            refine ⟨58886866874038065240252557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39257911249358710160168371 58886866874038065240252557)
            ·
              refine ⟨22082575077764274465094709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58886866874038065240252557 22082575077764274465094709)
              ·
                refine ⟨2070241413540400731102629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22082575077764274465094709 2070241413540400731102629)
                ·
                  refine ⟨388170265038825137081743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2070241413540400731102629 388170265038825137081743)
                  ·
                    rfl

theorem cell22_3401815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 4].length) (baseStart_3401815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401815 prefixEnd_3401815 := by exact prefixLift 3401815
  have htrace : WordTrace (prefixWord ++ tailWord_3401815) baseStart_3401815 baseEnd_3401815 := by
    simpa [prefixWord, tailWord_3401815, baseEnd_3401815] using wordTrace_append hprefix tailTrace_3401815
  have hstable : (prefixWord ++ tailWord_3401815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401815).length < 2 ^ (prefixWord ++ tailWord_3401815).sum := by decide
  have hdescent : baseEnd_3401815 < baseStart_3401815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401898 : List Nat := [3, 1, 5, 1, 2, 2, 2, 1, 2, 3]
def baseStart_3401898 : Nat := 118140960795 + 3401898 * 2 ^ 59
def prefixEnd_3401898 : Nat := 4983230072969 + 3 ^ 40 * 3401898 * 2
def baseEnd_3401898 : Nat := 1164539207712690861419975

theorem tailTrace_3401898 : CollatzResearch.WordTrace tailWord_3401898 prefixEnd_3401898 1164539207712690861419975 := by
  unfold tailWord_3401898
  simp only [CollatzResearch.WordTrace]
  refine ⟨31019353357378004691975587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82718275619674679178601565 31019353357378004691975587)
  ·
    refine ⟨46529030036067007037963381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31019353357378004691975587 46529030036067007037963381)
    ·
      refine ⟨4362096565881281909809067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46529030036067007037963381 4362096565881281909809067)
      ·
        refine ⟨6543144848821922864713601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4362096565881281909809067 6543144848821922864713601)
        ·
          refine ⟨4907358636616442148535201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6543144848821922864713601 4907358636616442148535201)
          ·
            refine ⟨3680518977462331611401401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4907358636616442148535201 3680518977462331611401401)
            ·
              refine ⟨2760389233096748708551051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3680518977462331611401401 2760389233096748708551051)
              ·
                refine ⟨4140583849645123062826577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2760389233096748708551051 4140583849645123062826577)
                ·
                  refine ⟨3105437887233842297119933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4140583849645123062826577 3105437887233842297119933)
                  ·
                    refine ⟨1164539207712690861419975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3105437887233842297119933 1164539207712690861419975)
                    ·
                      rfl

theorem cell22_3401898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_3401898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401898 prefixEnd_3401898 := by exact prefixLift 3401898
  have htrace : WordTrace (prefixWord ++ tailWord_3401898) baseStart_3401898 baseEnd_3401898 := by
    simpa [prefixWord, tailWord_3401898, baseEnd_3401898] using wordTrace_append hprefix tailTrace_3401898
  have hstable : (prefixWord ++ tailWord_3401898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401898).length < 2 ^ (prefixWord ++ tailWord_3401898).sum := by decide
  have hdescent : baseEnd_3401898 < baseStart_3401898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401903 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 1, 7]
def baseStart_3401903 : Nat := 118140960795 + 3401903 * 2 ^ 59
def prefixEnd_3401903 : Nat := 4983230072969 + 3 ^ 40 * 3401903 * 2
def baseEnd_3401903 : Nat := 1164540919314872515044959

theorem tailTrace_3401903 : CollatzResearch.WordTrace tailWord_3401903 prefixEnd_3401903 1164540919314872515044959 := by
  unfold tailWord_3401903
  simp only [CollatzResearch.WordTrace]
  refine ⟨124077595794493904621834363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82718397196329269747889575 124077595794493904621834363)
  ·
    refine ⟨186116393691740856932751545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124077595794493904621834363 186116393691740856932751545)
    ·
      refine ⟨139587295268805642699563659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186116393691740856932751545 139587295268805642699563659)
      ·
        refine ⟨209380942903208464049345489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139587295268805642699563659 209380942903208464049345489)
        ·
          refine ⟨157035707177406348037009117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209380942903208464049345489 157035707177406348037009117)
          ·
            refine ⟨58888390191527380513878419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157035707177406348037009117 58888390191527380513878419)
            ·
              refine ⟨88332585287291070770817629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58888390191527380513878419 88332585287291070770817629)
              ·
                refine ⟨33124719482734151539056611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88332585287291070770817629 33124719482734151539056611)
                ·
                  refine ⟨49687079224101227308584917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33124719482734151539056611 49687079224101227308584917)
                  ·
                    refine ⟨1164540919314872515044959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49687079224101227308584917 1164540919314872515044959)
                    ·
                      rfl

theorem cell22_3401903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_3401903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401903 prefixEnd_3401903 := by exact prefixLift 3401903
  have htrace : WordTrace (prefixWord ++ tailWord_3401903) baseStart_3401903 baseEnd_3401903 := by
    simpa [prefixWord, tailWord_3401903, baseEnd_3401903] using wordTrace_append hprefix tailTrace_3401903
  have hstable : (prefixWord ++ tailWord_3401903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401903).length < 2 ^ (prefixWord ++ tailWord_3401903).sum := by decide
  have hdescent : baseEnd_3401903 < baseStart_3401903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401982 : List Nat := [4, 2, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_3401982 : Nat := 118140960795 + 3401982 * 2 ^ 59
def prefixEnd_3401982 : Nat := 4983230072969 + 3 ^ 40 * 3401982 * 2
def baseEnd_3401982 : Nat := 1164567962629342642319717

theorem tailTrace_3401982 : CollatzResearch.WordTrace tailWord_3401982 prefixEnd_3401982 1164567962629342642319717 := by
  unfold tailWord_3401982
  simp only [CollatzResearch.WordTrace]
  refine ⟨15510059645150962639245025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82720318107471800742640133 15510059645150962639245025)
  ·
    refine ⟨11632544733863221979433769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15510059645150962639245025 11632544733863221979433769)
    ·
      refine ⟨8724408550397416484575327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11632544733863221979433769 8724408550397416484575327)
      ·
        refine ⟨13086612825596124726862991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8724408550397416484575327 13086612825596124726862991)
        ·
          refine ⟨19629919238394187090294487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13086612825596124726862991 19629919238394187090294487)
          ·
            refine ⟨29444878857591280635441731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19629919238394187090294487 29444878857591280635441731)
            ·
              refine ⟨44167318286386920953162597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29444878857591280635441731 44167318286386920953162597)
              ·
                refine ⟨8281372178697547678717987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44167318286386920953162597 8281372178697547678717987)
                ·
                  refine ⟨12422058268046321518076981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8281372178697547678717987 12422058268046321518076981)
                  ·
                    refine ⟨1164567962629342642319717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12422058268046321518076981 1164567962629342642319717)
                    ·
                      rfl

theorem cell22_3401982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_3401982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401982 prefixEnd_3401982 := by exact prefixLift 3401982
  have htrace : WordTrace (prefixWord ++ tailWord_3401982) baseStart_3401982 baseEnd_3401982 := by
    simpa [prefixWord, tailWord_3401982, baseEnd_3401982] using wordTrace_append hprefix tailTrace_3401982
  have hstable : (prefixWord ++ tailWord_3401982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401982).length < 2 ^ (prefixWord ++ tailWord_3401982).sum := by decide
  have hdescent : baseEnd_3401982 < baseStart_3401982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401986 : List Nat := [3, 4, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_3401986 : Nat := 118140960795 + 3401986 * 2 ^ 59
def prefixEnd_3401986 : Nat := 4983230072969 + 3 ^ 40 * 3401986 * 2
def baseEnd_3401986 : Nat := 1164569331911087965219705

theorem tailTrace_3401986 : CollatzResearch.WordTrace tailWord_3401986 prefixEnd_3401986 1164569331911087965219705 := by
  unfold tailWord_3401986
  simp only [CollatzResearch.WordTrace]
  refine ⟨31020155763298302449276453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82720415368795473198070541 31020155763298302449276453)
  ·
    refine ⟨5816279205618431709239335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31020155763298302449276453 5816279205618431709239335)
    ·
      refine ⟨8724418808427647563859003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5816279205618431709239335 8724418808427647563859003)
      ·
        refine ⟨13086628212641471345788505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8724418808427647563859003 13086628212641471345788505)
        ·
          refine ⟨9814971159481103509341379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13086628212641471345788505 9814971159481103509341379)
          ·
            refine ⟨14722456739221655264012069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9814971159481103509341379 14722456739221655264012069)
            ·
              refine ⟨2760460638604060362002263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14722456739221655264012069 2760460638604060362002263)
              ·
                refine ⟨4140690957906090543003395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2760460638604060362002263 4140690957906090543003395)
                ·
                  refine ⟨6211036436859135814505093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4140690957906090543003395 6211036436859135814505093)
                  ·
                    refine ⟨1164569331911087965219705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6211036436859135814505093 1164569331911087965219705)
                    ·
                      rfl

theorem cell22_3401986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_3401986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3401986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3401986 prefixEnd_3401986 := by exact prefixLift 3401986
  have htrace : WordTrace (prefixWord ++ tailWord_3401986) baseStart_3401986 baseEnd_3401986 := by
    simpa [prefixWord, tailWord_3401986, baseEnd_3401986] using wordTrace_append hprefix tailTrace_3401986
  have hstable : (prefixWord ++ tailWord_3401986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401986).length < 2 ^ (prefixWord ++ tailWord_3401986).sum := by decide
  have hdescent : baseEnd_3401986 < baseStart_3401986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402014 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_3402014 : Nat := 118140960795 + 3402014 * 2 ^ 59
def prefixEnd_3402014 : Nat := 4983230072969 + 3 ^ 40 * 3402014 * 2
def baseEnd_3402014 : Nat := 1164578916883305225519619

theorem tailTrace_3402014 : CollatzResearch.WordTrace tailWord_3402014 prefixEnd_3402014 1164578916883305225519619 := by
  unfold tailWord_3402014
  simp only [CollatzResearch.WordTrace]
  refine ⟨15510205537136471322390637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82721096198061180386083397 15510205537136471322390637)
  ·
    refine ⟨5816327076426176745896489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15510205537136471322390637 5816327076426176745896489)
    ·
      refine ⟨4362245307319632559422367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5816327076426176745896489 4362245307319632559422367)
      ·
        refine ⟨6543367960979448839133551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4362245307319632559422367 6543367960979448839133551)
        ·
          refine ⟨9815051941469173258700327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6543367960979448839133551 9815051941469173258700327)
          ·
            refine ⟨14722577912203759888050491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9815051941469173258700327 14722577912203759888050491)
            ·
              refine ⟨22083866868305639832075737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14722577912203759888050491 22083866868305639832075737)
              ·
                refine ⟨16562900151229229874056803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22083866868305639832075737 16562900151229229874056803)
                ·
                  refine ⟨24844350226843844811085205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16562900151229229874056803 24844350226843844811085205)
                  ·
                    refine ⟨1164578916883305225519619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24844350226843844811085205 1164578916883305225519619)
                    ·
                      rfl

theorem cell22_3402014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_3402014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402014 prefixEnd_3402014 := by exact prefixLift 3402014
  have htrace : WordTrace (prefixWord ++ tailWord_3402014) baseStart_3402014 baseEnd_3402014 := by
    simpa [prefixWord, tailWord_3402014, baseEnd_3402014] using wordTrace_append hprefix tailTrace_3402014
  have hstable : (prefixWord ++ tailWord_3402014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402014).length < 2 ^ (prefixWord ++ tailWord_3402014).sum := by decide
  have hdescent : baseEnd_3402014 < baseStart_3402014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402016 : List Nat := [2, 1, 1, 5, 2, 2, 3, 1, 2, 3]
def baseStart_3402016 : Nat := 118140960795 + 3402016 * 2 ^ 59
def prefixEnd_3402016 : Nat := 4983230072969 + 3 ^ 40 * 3402016 * 2
def baseEnd_3402016 : Nat := 1164579601524177886969613

theorem tailTrace_3402016 : CollatzResearch.WordTrace tailWord_3402016 prefixEnd_3402016 1164579601524177886969613 := by
  unfold tailWord_3402016
  simp only [CollatzResearch.WordTrace]
  refine ⟨62040858621542262460348951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82721144828723016613798601 62040858621542262460348951)
  ·
    refine ⟨93061287932313393690523427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62040858621542262460348951 93061287932313393690523427)
    ·
      refine ⟨139591931898470090535785141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93061287932313393690523427 139591931898470090535785141)
      ·
        refine ⟨13086743615481570987729857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139591931898470090535785141 13086743615481570987729857)
        ·
          refine ⟨9815057711611178240797393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13086743615481570987729857 9815057711611178240797393)
          ·
            refine ⟨7361293283708383680598045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9815057711611178240797393 7361293283708383680598045)
            ·
              refine ⟨2760484981390643880224267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7361293283708383680598045 2760484981390643880224267)
              ·
                refine ⟨4140727472085965820336401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2760484981390643880224267 4140727472085965820336401)
                ·
                  refine ⟨3105545604064474365252301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4140727472085965820336401 3105545604064474365252301)
                  ·
                    refine ⟨1164579601524177886969613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3105545604064474365252301 1164579601524177886969613)
                    ·
                      rfl

theorem cell22_3402016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 2, 3].length) (baseStart_3402016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402016 prefixEnd_3402016 := by exact prefixLift 3402016
  have htrace : WordTrace (prefixWord ++ tailWord_3402016) baseStart_3402016 baseEnd_3402016 := by
    simpa [prefixWord, tailWord_3402016, baseEnd_3402016] using wordTrace_append hprefix tailTrace_3402016
  have hstable : (prefixWord ++ tailWord_3402016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402016).length < 2 ^ (prefixWord ++ tailWord_3402016).sum := by decide
  have hdescent : baseEnd_3402016 < baseStart_3402016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402029 : List Nat := [1, 5, 3, 1, 2, 1, 1, 8]
def baseStart_3402029 : Nat := 118140960795 + 3402029 * 2 ^ 59
def prefixEnd_3402029 : Nat := 4983230072969 + 3 ^ 40 * 3402029 * 2
def baseEnd_3402029 : Nat := 129398227965538909599397

theorem tailTrace_3402029 : CollatzResearch.WordTrace tailWord_3402029 prefixEnd_3402029 129398227965538909599397 := by
  unfold tailWord_3402029
  simp only [CollatzResearch.WordTrace]
  refine ⟨124082191392037428140921141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82721460928024952093947427 124082191392037428140921141)
  ·
    refine ⟨11632705443003508888211357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124082191392037428140921141 11632705443003508888211357)
    ·
      refine ⟨4362264541126315833079259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11632705443003508888211357 4362264541126315833079259)
      ·
        refine ⟨6543396811689473749618889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4362264541126315833079259 6543396811689473749618889)
        ·
          refine ⟨4907547608767105312214167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6543396811689473749618889 4907547608767105312214167)
          ·
            refine ⟨7361321413150657968321251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4907547608767105312214167 7361321413150657968321251)
            ·
              refine ⟨11041982119725986952481877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7361321413150657968321251 11041982119725986952481877)
              ·
                refine ⟨129398227965538909599397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11041982119725986952481877 129398227965538909599397)
                ·
                  rfl

theorem cell22_3402029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 8].length) (baseStart_3402029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402029 prefixEnd_3402029 := by exact prefixLift 3402029
  have htrace : WordTrace (prefixWord ++ tailWord_3402029) baseStart_3402029 baseEnd_3402029 := by
    simpa [prefixWord, tailWord_3402029, baseEnd_3402029] using wordTrace_append hprefix tailTrace_3402029
  have hstable : (prefixWord ++ tailWord_3402029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402029).length < 2 ^ (prefixWord ++ tailWord_3402029).sum := by decide
  have hdescent : baseEnd_3402029 < baseStart_3402029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402040 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 7]
def baseStart_3402040 : Nat := 118140960795 + 3402040 * 2 ^ 59
def prefixEnd_3402040 : Nat := 4983230072969 + 3 ^ 40 * 3402040 * 2
def baseEnd_3402040 : Nat := 388195939071549941456513

theorem tailTrace_3402040 : CollatzResearch.WordTrace tailWord_3402040 prefixEnd_3402040 388195939071549941456513 := by
  unfold tailWord_3402040
  simp only [CollatzResearch.WordTrace]
  refine ⟨62041296297498788509785787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82721728396665051346381049 62041296297498788509785787)
  ·
    refine ⟨93061944446248182764678681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62041296297498788509785787 93061944446248182764678681)
    ·
      refine ⟨69796458334686137073509011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93061944446248182764678681 69796458334686137073509011)
      ·
        refine ⟨104694687502029205610263517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69796458334686137073509011 104694687502029205610263517)
        ·
          refine ⟨39260507813260952103848819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104694687502029205610263517 39260507813260952103848819)
          ·
            refine ⟨58890761719891428155773229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39260507813260952103848819 58890761719891428155773229)
            ·
              refine ⟨22084035644959285558414961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58890761719891428155773229 22084035644959285558414961)
              ·
                refine ⟨16563026733719464168811221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22084035644959285558414961 16563026733719464168811221)
                ·
                  refine ⟨388195939071549941456513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16563026733719464168811221 388195939071549941456513)
                  ·
                    rfl

theorem cell22_3402040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 7].length) (baseStart_3402040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402040 prefixEnd_3402040 := by exact prefixLift 3402040
  have htrace : WordTrace (prefixWord ++ tailWord_3402040) baseStart_3402040 baseEnd_3402040 := by
    simpa [prefixWord, tailWord_3402040, baseEnd_3402040] using wordTrace_append hprefix tailTrace_3402040
  have hstable : (prefixWord ++ tailWord_3402040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402040).length < 2 ^ (prefixWord ++ tailWord_3402040).sum := by decide
  have hdescent : baseEnd_3402040 < baseStart_3402040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402119 : List Nat := [1, 1, 4, 2, 2, 1, 3, 4, 4]
def baseStart_3402119 : Nat := 118140960795 + 3402119 * 2 ^ 59
def prefixEnd_3402119 : Nat := 4983230072969 + 3 ^ 40 * 3402119 * 2
def baseEnd_3402119 : Nat := 388204953509706650548099

theorem tailTrace_3402119 : CollatzResearch.WordTrace tailWord_3402119 prefixEnd_3402119 388204953509706650548099 := by
  unfold tailWord_3402119
  simp only [CollatzResearch.WordTrace]
  refine ⟨124085473961711373511697411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82723649307807582341131607 124085473961711373511697411)
  ·
    refine ⟨186128210942567060267546117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124085473961711373511697411 186128210942567060267546117)
    ·
      refine ⟨34899039551731323800164897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186128210942567060267546117 34899039551731323800164897)
      ·
        refine ⟨26174279663798492850123673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34899039551731323800164897 26174279663798492850123673)
        ·
          refine ⟨19630709747848869637592755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26174279663798492850123673 19630709747848869637592755)
          ·
            refine ⟨29446064621773304456389133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19630709747848869637592755 29446064621773304456389133)
            ·
              refine ⟨11042274233164989171145925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29446064621773304456389133 11042274233164989171145925)
              ·
                refine ⟨2070426418718435469589861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11042274233164989171145925 2070426418718435469589861)
                ·
                  refine ⟨388204953509706650548099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2070426418718435469589861 388204953509706650548099)
                  ·
                    rfl

theorem cell22_3402119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 4].length) (baseStart_3402119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402119 prefixEnd_3402119 := by exact prefixLift 3402119
  have htrace : WordTrace (prefixWord ++ tailWord_3402119) baseStart_3402119 baseEnd_3402119 := by
    simpa [prefixWord, tailWord_3402119, baseEnd_3402119] using wordTrace_append hprefix tailTrace_3402119
  have hstable : (prefixWord ++ tailWord_3402119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402119).length < 2 ^ (prefixWord ++ tailWord_3402119).sum := by decide
  have hdescent : baseEnd_3402119 < baseStart_3402119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402196 : List Nat := [2, 4, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_3402196 : Nat := 118140960795 + 3402196 * 2 ^ 59
def prefixEnd_3402196 : Nat := 4983230072969 + 3 ^ 40 * 3402196 * 2
def baseEnd_3402196 : Nat := 1164641219202717417469061

theorem tailTrace_3402196 : CollatzResearch.WordTrace tailWord_3402196 prefixEnd_3402196 1164641219202717417469061 := by
  unfold tailWord_3402196
  simp only [CollatzResearch.WordTrace]
  refine ⟨62044141191216207831125221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82725521588288277108166961 62044141191216207831125221)
  ·
    refine ⟨11633276473353038968335979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62044141191216207831125221 11633276473353038968335979)
    ·
      refine ⟨17449914710029558452503969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11633276473353038968335979 17449914710029558452503969)
      ·
        refine ⟨13087436032522168839377977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17449914710029558452503969 13087436032522168839377977)
        ·
          refine ⟨9815577024391626629533483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13087436032522168839377977 9815577024391626629533483)
          ·
            refine ⟨14723365536587439944300225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9815577024391626629533483 14723365536587439944300225)
            ·
              refine ⟨11042524152440579958225169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14723365536587439944300225 11042524152440579958225169)
              ·
                refine ⟨8281893114330434968668877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11042524152440579958225169 8281893114330434968668877)
                ·
                  refine ⟨3105709917873913113250829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8281893114330434968668877 3105709917873913113250829)
                  ·
                    refine ⟨1164641219202717417469061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3105709917873913113250829 1164641219202717417469061)
                    ·
                      rfl

theorem cell22_3402196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_3402196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402196 prefixEnd_3402196 := by exact prefixLift 3402196
  have htrace : WordTrace (prefixWord ++ tailWord_3402196) baseStart_3402196 baseEnd_3402196 := by
    simpa [prefixWord, tailWord_3402196, baseEnd_3402196] using wordTrace_append hprefix tailTrace_3402196
  have hstable : (prefixWord ++ tailWord_3402196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402196).length < 2 ^ (prefixWord ++ tailWord_3402196).sum := by decide
  have hdescent : baseEnd_3402196 < baseStart_3402196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402230 : List Nat := [5, 1, 1, 1, 2, 1, 5, 2, 1, 3]
def baseStart_3402230 : Nat := 118140960795 + 3402230 * 2 ^ 59
def prefixEnd_3402230 : Nat := 4983230072969 + 3 ^ 40 * 3402230 * 2
def baseEnd_3402230 : Nat := 1164652858097552662118957

theorem tailTrace_3402230 : CollatzResearch.WordTrace tailWord_3402230 prefixEnd_3402230 1164652858097552662118957 := by
  unfold tailWord_3402230
  simp only [CollatzResearch.WordTrace]
  refine ⟨7755595154019327466811759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82726348309539492979325429 7755595154019327466811759)
  ·
    refine ⟨11633392731028991200217639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7755595154019327466811759 11633392731028991200217639)
    ·
      refine ⟨17450089096543486800326459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11633392731028991200217639 17450089096543486800326459)
      ·
        refine ⟨26175133644815230200489689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17450089096543486800326459 26175133644815230200489689)
        ·
          refine ⟨19631350233611422650367267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26175133644815230200489689 19631350233611422650367267)
          ·
            refine ⟨29447025350417133975550901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19631350233611422650367267 29447025350417133975550901)
            ·
              refine ⟨2760658626601606310207897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29447025350417133975550901 2760658626601606310207897)
              ·
                refine ⟨2070493969951204732655923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2760658626601606310207897 2070493969951204732655923)
                ·
                  refine ⟨3105740954926807098983885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2070493969951204732655923 3105740954926807098983885)
                  ·
                    refine ⟨1164652858097552662118957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3105740954926807098983885 1164652858097552662118957)
                    ·
                      rfl

theorem cell22_3402230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_3402230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402230 prefixEnd_3402230 := by exact prefixLift 3402230
  have htrace : WordTrace (prefixWord ++ tailWord_3402230) baseStart_3402230 baseEnd_3402230 := by
    simpa [prefixWord, tailWord_3402230, baseEnd_3402230] using wordTrace_append hprefix tailTrace_3402230
  have hstable : (prefixWord ++ tailWord_3402230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402230).length < 2 ^ (prefixWord ++ tailWord_3402230).sum := by decide
  have hdescent : baseEnd_3402230 < baseStart_3402230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402269 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_3402269 : Nat := 118140960795 + 3402269 * 2 ^ 59
def prefixEnd_3402269 : Nat := 4983230072969 + 3 ^ 40 * 3402269 * 2
def baseEnd_3402269 : Nat := 1164666208594569560393837

theorem tailTrace_3402269 : CollatzResearch.WordTrace tailWord_3402269 prefixEnd_3402269 1164666208594569560393837 := by
  unfold tailWord_3402269
  simp only [CollatzResearch.WordTrace]
  refine ⟨124090944911167949129657861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82727296607445299419771907 124090944911167949129657861)
  ·
    refine ⟨23267052170843990461810849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124090944911167949129657861 23267052170843990461810849)
    ·
      refine ⟨17450289128132992846358137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23267052170843990461810849 17450289128132992846358137)
      ·
        refine ⟨13087716846099744634768603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17450289128132992846358137 13087716846099744634768603)
        ·
          refine ⟨19631575269149616952152905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13087716846099744634768603 19631575269149616952152905)
          ·
            refine ⟨14723681451862212714114679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19631575269149616952152905 14723681451862212714114679)
            ·
              refine ⟨22085522177793319071172019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14723681451862212714114679 22085522177793319071172019)
              ·
                refine ⟨33128283266689978606758029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22085522177793319071172019 33128283266689978606758029)
                ·
                  refine ⟨12423106225008741977534261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33128283266689978606758029 12423106225008741977534261)
                  ·
                    refine ⟨1164666208594569560393837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12423106225008741977534261 1164666208594569560393837)
                    ·
                      rfl

theorem cell22_3402269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_3402269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402269 prefixEnd_3402269 := by exact prefixLift 3402269
  have htrace : WordTrace (prefixWord ++ tailWord_3402269) baseStart_3402269 baseEnd_3402269 := by
    simpa [prefixWord, tailWord_3402269, baseEnd_3402269] using wordTrace_append hprefix tailTrace_3402269
  have hstable : (prefixWord ++ tailWord_3402269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402269).length < 2 ^ (prefixWord ++ tailWord_3402269).sum := by decide
  have hdescent : baseEnd_3402269 < baseStart_3402269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402348 : List Nat := [2, 2, 1, 1, 3, 1, 4, 4, 1, 3]
def baseStart_3402348 : Nat := 118140960795 + 3402348 * 2 ^ 59
def prefixEnd_3402348 : Nat := 4983230072969 + 3 ^ 40 * 3402348 * 2
def baseEnd_3402348 : Nat := 1164693251909039687668595

theorem tailTrace_3402348 : CollatzResearch.WordTrace tailWord_3402348 prefixEnd_3402348 1164693251909039687668595 := by
  unfold tailWord_3402348
  simp only [CollatzResearch.WordTrace]
  refine ⟨62046913138940872810891849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82729217518587830414522465 62046913138940872810891849)
  ·
    refine ⟨46535184854205654608168887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62046913138940872810891849 46535184854205654608168887)
    ·
      refine ⟨69802777281308481912253331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46535184854205654608168887 69802777281308481912253331)
      ·
        refine ⟨104704165921962722868379997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69802777281308481912253331 104704165921962722868379997)
        ·
          refine ⟨39264062220736021075642499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104704165921962722868379997 39264062220736021075642499)
          ·
            refine ⟨58896093331104031613463749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39264062220736021075642499 58896093331104031613463749)
            ·
              refine ⟨11043017499582005927524453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58896093331104031613463749 11043017499582005927524453)
              ·
                refine ⟨2070565781171626111410835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11043017499582005927524453 2070565781171626111410835)
                ·
                  refine ⟨3105848671757439167116253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2070565781171626111410835 3105848671757439167116253)
                  ·
                    refine ⟨1164693251909039687668595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3105848671757439167116253 1164693251909039687668595)
                    ·
                      rfl

theorem cell22_3402348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 1, 3].length) (baseStart_3402348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402348 prefixEnd_3402348 := by exact prefixLift 3402348
  have htrace : WordTrace (prefixWord ++ tailWord_3402348) baseStart_3402348 baseEnd_3402348 := by
    simpa [prefixWord, tailWord_3402348, baseEnd_3402348] using wordTrace_append hprefix tailTrace_3402348
  have hstable : (prefixWord ++ tailWord_3402348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402348).length < 2 ^ (prefixWord ++ tailWord_3402348).sum := by decide
  have hdescent : baseEnd_3402348 < baseStart_3402348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402359 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 2, 5]
def baseStart_3402359 : Nat := 118140960795 + 3402359 * 2 ^ 59
def prefixEnd_3402359 : Nat := 4983230072969 + 3 ^ 40 * 3402359 * 2
def baseEnd_3402359 : Nat := 1164697017433839325643561

theorem tailTrace_3402359 : CollatzResearch.WordTrace tailWord_3402359 prefixEnd_3402359 1164697017433839325643561 := by
  unfold tailWord_3402359
  simp only [CollatzResearch.WordTrace]
  refine ⟨124094227480841894500434131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82729484987227929666956087 124094227480841894500434131)
  ·
    refine ⟨186141341221262841750651197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124094227480841894500434131 186141341221262841750651197)
    ·
      refine ⟨69803002957973565656494199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186141341221262841750651197 69803002957973565656494199)
      ·
        refine ⟨104704504436960348484741299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69803002957973565656494199 104704504436960348484741299)
        ·
          refine ⟨157056756655440522727111949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104704504436960348484741299 157056756655440522727111949)
          ·
            refine ⟨58896283745790196022666981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157056756655440522727111949 58896283745790196022666981)
            ·
              refine ⟨11043053202335661754250059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58896283745790196022666981 11043053202335661754250059)
              ·
                refine ⟨16564579803503492631375089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11043053202335661754250059 16564579803503492631375089)
                ·
                  refine ⟨12423434852627619473531317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16564579803503492631375089 12423434852627619473531317)
                  ·
                    refine ⟨1164697017433839325643561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12423434852627619473531317 1164697017433839325643561)
                    ·
                      rfl

theorem cell22_3402359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_3402359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402359 prefixEnd_3402359 := by exact prefixLift 3402359
  have htrace : WordTrace (prefixWord ++ tailWord_3402359) baseStart_3402359 baseEnd_3402359 := by
    simpa [prefixWord, tailWord_3402359, baseEnd_3402359] using wordTrace_append hprefix tailTrace_3402359
  have hstable : (prefixWord ++ tailWord_3402359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402359).length < 2 ^ (prefixWord ++ tailWord_3402359).sum := by decide
  have hdescent : baseEnd_3402359 < baseStart_3402359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402391 : List Nat := [1, 1, 3, 3, 2, 1, 1, 5, 1, 4]
def baseStart_3402391 : Nat := 118140960795 + 3402391 * 2 ^ 59
def prefixEnd_3402391 : Nat := 4983230072969 + 3 ^ 40 * 3402391 * 2
def baseEnd_3402391 : Nat := 1164707971687801908843463

theorem tailTrace_3402391 : CollatzResearch.WordTrace tailWord_3402391 prefixEnd_3402391 1164707971687801908843463 := by
  unfold tailWord_3402391
  simp only [CollatzResearch.WordTrace]
  refine ⟨124095394616725963965599027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82730263077817309310399351 124095394616725963965599027)
  ·
    refine ⟨186143091925088945948398541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124095394616725963965599027 186143091925088945948398541)
    ·
      refine ⟨69803659471908354730649453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186143091925088945948398541 69803659471908354730649453)
      ·
        refine ⟨26176372301965633023993545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69803659471908354730649453 26176372301965633023993545)
        ·
          refine ⟨19632279226474224767995159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26176372301965633023993545 19632279226474224767995159)
          ·
            refine ⟨29448418839711337151992739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19632279226474224767995159 29448418839711337151992739)
            ·
              refine ⟨44172628259567005727989109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29448418839711337151992739 44172628259567005727989109)
              ·
                refine ⟨4141183899334406786998979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44172628259567005727989109 4141183899334406786998979)
                ·
                  refine ⟨6211775849001610180498469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4141183899334406786998979 6211775849001610180498469)
                  ·
                    refine ⟨1164707971687801908843463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6211775849001610180498469 1164707971687801908843463)
                    ·
                      rfl

theorem cell22_3402391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_3402391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402391 prefixEnd_3402391 := by exact prefixLift 3402391
  have htrace : WordTrace (prefixWord ++ tailWord_3402391) baseStart_3402391 baseEnd_3402391 := by
    simpa [prefixWord, tailWord_3402391, baseEnd_3402391] using wordTrace_append hprefix tailTrace_3402391
  have hstable : (prefixWord ++ tailWord_3402391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402391).length < 2 ^ (prefixWord ++ tailWord_3402391).sum := by decide
  have hdescent : baseEnd_3402391 < baseStart_3402391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402530 : List Nat := [3, 3, 1, 1, 2, 3, 3, 1, 5]
def baseStart_3402530 : Nat := 118140960795 + 3402530 * 2 ^ 59
def prefixEnd_3402530 : Nat := 4983230072969 + 3 ^ 40 * 3402530 * 2
def baseEnd_3402530 : Nat := 388251851409483959872679

theorem tailTrace_3402530 : CollatzResearch.WordTrace tailWord_3402530 prefixEnd_3402530 388251851409483959872679 := by
  unfold tailWord_3402530
  simp only [CollatzResearch.WordTrace]
  refine ⟨31025116090805597676227261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82733642908814927136606029 31025116090805597676227261)
  ·
    refine ⟨11634418534052099128585223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31025116090805597676227261 11634418534052099128585223)
    ·
      refine ⟨17451627801078148692877835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11634418534052099128585223 17451627801078148692877835)
      ·
        refine ⟨26177441701617223039316753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17451627801078148692877835 26177441701617223039316753)
        ·
          refine ⟨19633081276212917279487565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26177441701617223039316753 19633081276212917279487565)
          ·
            refine ⟨7362405478579843979807837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19633081276212917279487565 7362405478579843979807837)
            ·
              refine ⟨2760902054467441492427939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7362405478579843979807837 2760902054467441492427939)
              ·
                refine ⟨4141353081701162238641909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2760902054467441492427939 4141353081701162238641909)
                ·
                  refine ⟨388251851409483959872679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4141353081701162238641909 388251851409483959872679)
                  ·
                    rfl

theorem cell22_3402530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_3402530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402530 prefixEnd_3402530 := by exact prefixLift 3402530
  have htrace : WordTrace (prefixWord ++ tailWord_3402530) baseStart_3402530 baseEnd_3402530 := by
    simpa [prefixWord, tailWord_3402530, baseEnd_3402530] using wordTrace_append hprefix tailTrace_3402530
  have hstable : (prefixWord ++ tailWord_3402530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402530).length < 2 ^ (prefixWord ++ tailWord_3402530).sum := by decide
  have hdescent : baseEnd_3402530 < baseStart_3402530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402556 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 3, 5]
def baseStart_3402556 : Nat := 118140960795 + 3402556 * 2 ^ 59
def prefixEnd_3402556 : Nat := 4983230072969 + 3 ^ 40 * 3402556 * 2
def baseEnd_3402556 : Nat := 1164764454559796478467957

theorem tailTrace_3402556 : CollatzResearch.WordTrace tailWord_3402556 prefixEnd_3402556 1164764454559796478467957 := by
  unfold tailWord_3402556
  simp only [CollatzResearch.WordTrace]
  refine ⟨62050706330564098572677761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82734275107418798096903681 62050706330564098572677761)
  ·
    refine ⟨46538029747923073929508321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62050706330564098572677761 46538029747923073929508321)
    ·
      refine ⟨34903522310942305447131241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46538029747923073929508321 34903522310942305447131241)
      ·
        refine ⟨26177641733206729085348431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34903522310942305447131241 26177641733206729085348431)
        ·
          refine ⟨39266462599810093628022647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26177641733206729085348431 39266462599810093628022647)
          ·
            refine ⟨58899693899715140442033971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39266462599810093628022647 58899693899715140442033971)
            ·
              refine ⟨88349540849572710663050957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58899693899715140442033971 88349540849572710663050957)
              ·
                refine ⟨33131077818589766498644109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88349540849572710663050957 33131077818589766498644109)
                ·
                  refine ⟨12424154181971162436991541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33131077818589766498644109 12424154181971162436991541)
                  ·
                    refine ⟨1164764454559796478467957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12424154181971162436991541 1164764454559796478467957)
                    ·
                      rfl

theorem cell22_3402556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_3402556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402556 prefixEnd_3402556 := by exact prefixLift 3402556
  have htrace : WordTrace (prefixWord ++ tailWord_3402556) baseStart_3402556 baseEnd_3402556 := by
    simpa [prefixWord, tailWord_3402556, baseEnd_3402556] using wordTrace_append hprefix tailTrace_3402556
  have hstable : (prefixWord ++ tailWord_3402556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402556).length < 2 ^ (prefixWord ++ tailWord_3402556).sum := by decide
  have hdescent : baseEnd_3402556 < baseStart_3402556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402586 : List Nat := [3, 1, 1, 2, 1, 4, 1, 9]
def baseStart_3402586 : Nat := 118140960795 + 3402586 * 2 ^ 59
def prefixEnd_3402586 : Nat := 4983230072969 + 3 ^ 40 * 3402586 * 2
def baseEnd_3402586 : Nat := 129419413796987377801985

theorem tailTrace_3402586 : CollatzResearch.WordTrace tailWord_3402586 prefixEnd_3402586 129419413796987377801985 := by
  unfold tailWord_3402586
  simp only [CollatzResearch.WordTrace]
  refine ⟨31025626712754878067236903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82735004567346341512631741 31025626712754878067236903)
  ·
    refine ⟨46538440069132317100855355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31025626712754878067236903 46538440069132317100855355)
    ·
      refine ⟨69807660103698475651283033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46538440069132317100855355 69807660103698475651283033)
      ·
        refine ⟨52355745077773856738462275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69807660103698475651283033 52355745077773856738462275)
        ·
          refine ⟨78533617616660785107693413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52355745077773856738462275 78533617616660785107693413)
          ·
            refine ⟨14725053303123897207692515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78533617616660785107693413 14725053303123897207692515)
            ·
              refine ⟨22087579954685845811538773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14725053303123897207692515 22087579954685845811538773)
              ·
                refine ⟨129419413796987377801985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22087579954685845811538773 129419413796987377801985)
                ·
                  rfl

theorem cell22_3402586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 9].length) (baseStart_3402586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402586 prefixEnd_3402586 := by exact prefixLift 3402586
  have htrace : WordTrace (prefixWord ++ tailWord_3402586) baseStart_3402586 baseEnd_3402586 := by
    simpa [prefixWord, tailWord_3402586, baseEnd_3402586] using wordTrace_append hprefix tailTrace_3402586
  have hstable : (prefixWord ++ tailWord_3402586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402586).length < 2 ^ (prefixWord ++ tailWord_3402586).sum := by decide
  have hdescent : baseEnd_3402586 < baseStart_3402586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402594 : List Nat := [3, 3, 2, 1, 4, 1, 1, 2, 1, 4]
def baseStart_3402594 : Nat := 118140960795 + 3402594 * 2 ^ 59
def prefixEnd_3402594 : Nat := 4983230072969 + 3 ^ 40 * 3402594 * 2
def baseEnd_3402594 : Nat := 1164777462736377046017841

theorem tailTrace_3402594 : CollatzResearch.WordTrace tailWord_3402594 prefixEnd_3402594 1164777462736377046017841 := by
  unfold tailWord_3402594
  simp only [CollatzResearch.WordTrace]
  refine ⟨31025699658747632408809709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82735199089993686423492557 31025699658747632408809709)
  ·
    refine ⟨11634637372030362153303641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31025699658747632408809709 11634637372030362153303641)
    ·
      refine ⟨8725978029022771614977731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11634637372030362153303641 8725978029022771614977731)
      ·
        refine ⟨13088967043534157422466597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8725978029022771614977731 13088967043534157422466597)
        ·
          refine ⟨2454181320662654516712487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13088967043534157422466597 2454181320662654516712487)
          ·
            refine ⟨3681271980993981775068731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2454181320662654516712487 3681271980993981775068731)
            ·
              refine ⟨5521907971490972662603097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3681271980993981775068731 5521907971490972662603097)
              ·
                refine ⟨4141430978618229496952323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5521907971490972662603097 4141430978618229496952323)
                ·
                  refine ⟨6212146467927344245428485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4141430978618229496952323 6212146467927344245428485)
                  ·
                    refine ⟨1164777462736377046017841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6212146467927344245428485 1164777462736377046017841)
                    ·
                      rfl

theorem cell22_3402594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_3402594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402594 prefixEnd_3402594 := by exact prefixLift 3402594
  have htrace : WordTrace (prefixWord ++ tailWord_3402594) baseStart_3402594 baseEnd_3402594 := by
    simpa [prefixWord, tailWord_3402594, baseEnd_3402594] using wordTrace_append hprefix tailTrace_3402594
  have hstable : (prefixWord ++ tailWord_3402594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402594).length < 2 ^ (prefixWord ++ tailWord_3402594).sum := by decide
  have hdescent : baseEnd_3402594 < baseStart_3402594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402652 : List Nat := [2, 2, 3, 3, 2, 1, 1, 2, 3, 3]
def baseStart_3402652 : Nat := 118140960795 + 3402652 * 2 ^ 59
def prefixEnd_3402652 : Nat := 4983230072969 + 3 ^ 40 * 3402652 * 2
def baseEnd_3402652 : Nat := 1164797317321684228067663

theorem tailTrace_3402652 : CollatzResearch.WordTrace tailWord_3402652 prefixEnd_3402652 1164797317321684228067663 := by
  unfold tailWord_3402652
  simp only [CollatzResearch.WordTrace]
  refine ⟨62052457034390202770425105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82736609379186937027233473 62052457034390202770425105)
  ·
    refine ⟨46539342775792652077818829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62052457034390202770425105 46539342775792652077818829)
    ·
      refine ⟨17452253540922244529182061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46539342775792652077818829 17452253540922244529182061)
      ·
        refine ⟨6544595077845841698443273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17452253540922244529182061 6544595077845841698443273)
        ·
          refine ⟨4908446308384381273832455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6544595077845841698443273 4908446308384381273832455)
          ·
            refine ⟨7362669462576571910748683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4908446308384381273832455 7362669462576571910748683)
            ·
              refine ⟨11044004193864857866123025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7362669462576571910748683 11044004193864857866123025)
              ·
                refine ⟨8283003145398643399592269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11044004193864857866123025 8283003145398643399592269)
                ·
                  refine ⟨3106126179524491274847101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8283003145398643399592269 3106126179524491274847101)
                  ·
                    refine ⟨1164797317321684228067663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3106126179524491274847101 1164797317321684228067663)
                    ·
                      rfl

theorem cell22_3402652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_3402652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402652 prefixEnd_3402652 := by exact prefixLift 3402652
  have htrace : WordTrace (prefixWord ++ tailWord_3402652) baseStart_3402652 baseEnd_3402652 := by
    simpa [prefixWord, tailWord_3402652, baseEnd_3402652] using wordTrace_append hprefix tailTrace_3402652
  have hstable : (prefixWord ++ tailWord_3402652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402652).length < 2 ^ (prefixWord ++ tailWord_3402652).sum := by decide
  have hdescent : baseEnd_3402652 < baseStart_3402652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402723 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 1, 6]
def baseStart_3402723 : Nat := 118140960795 + 3402723 * 2 ^ 59
def prefixEnd_3402723 : Nat := 4983230072969 + 3 ^ 40 * 3402723 * 2
def baseEnd_3402723 : Nat := 1164821622072663709542445

theorem tailTrace_3402723 : CollatzResearch.WordTrace tailWord_3402723 prefixEnd_3402723 1164821622072663709542445 := by
  unfold tailWord_3402723
  simp only [CollatzResearch.WordTrace]
  refine ⟨124107503651523184666684823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82738335767682123111123215 124107503651523184666684823)
  ·
    refine ⟨186161255477284777000027235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124107503651523184666684823 186161255477284777000027235)
    ·
      refine ⟨279241883215927165500040853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186161255477284777000027235 279241883215927165500040853)
      ·
        refine ⟨13089463275746585882814415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 279241883215927165500040853 13089463275746585882814415)
        ·
          refine ⟨19634194913619878824221623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13089463275746585882814415 19634194913619878824221623)
          ·
            refine ⟨29451292370429818236332435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19634194913619878824221623 29451292370429818236332435)
            ·
              refine ⟨44176938555644727354498653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29451292370429818236332435 44176938555644727354498653)
              ·
                refine ⟨16566351958366772757936995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44176938555644727354498653 16566351958366772757936995)
                ·
                  refine ⟨24849527937550159136905493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16566351958366772757936995 24849527937550159136905493)
                  ·
                    refine ⟨1164821622072663709542445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24849527937550159136905493 1164821622072663709542445)
                    ·
                      rfl

theorem cell22_3402723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 6].length) (baseStart_3402723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402723 prefixEnd_3402723 := by exact prefixLift 3402723
  have htrace : WordTrace (prefixWord ++ tailWord_3402723) baseStart_3402723 baseEnd_3402723 := by
    simpa [prefixWord, tailWord_3402723, baseEnd_3402723] using wordTrace_append hprefix tailTrace_3402723
  have hstable : (prefixWord ++ tailWord_3402723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402723).length < 2 ^ (prefixWord ++ tailWord_3402723).sum := by decide
  have hdescent : baseEnd_3402723 < baseStart_3402723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402727 : List Nat := [1, 1, 5, 2, 2, 1, 3, 3, 4]
def baseStart_3402727 : Nat := 118140960795 + 3402727 * 2 ^ 59
def prefixEnd_3402727 : Nat := 4983230072969 + 3 ^ 40 * 3402727 * 2
def baseEnd_3402727 : Nat := 388274330451469677480811

theorem tailTrace_3402727 : CollatzResearch.WordTrace tailWord_3402727 prefixEnd_3402727 388274330451469677480811 := by
  unfold tailWord_3402727
  simp only [CollatzResearch.WordTrace]
  refine ⟨124107649543508693349830435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82738433029005795566553623 124107649543508693349830435)
  ·
    refine ⟨186161474315263040024745653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124107649543508693349830435 186161474315263040024745653)
    ·
      refine ⟨17452638217055910002319905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186161474315263040024745653 17452638217055910002319905)
      ·
        refine ⟨13089478662791932501739929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17452638217055910002319905 13089478662791932501739929)
        ·
          refine ⟨9817108997093949376304947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13089478662791932501739929 9817108997093949376304947)
          ·
            refine ⟨14725663495640924064457421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9817108997093949376304947 14725663495640924064457421)
            ·
              refine ⟨5522123810865346524171533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14725663495640924064457421 5522123810865346524171533)
              ·
                refine ⟨2070796429074504946564325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5522123810865346524171533 2070796429074504946564325)
                ·
                  refine ⟨388274330451469677480811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2070796429074504946564325 388274330451469677480811)
                  ·
                    rfl

theorem cell22_3402727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 4].length) (baseStart_3402727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402727 prefixEnd_3402727 := by exact prefixLift 3402727
  have htrace : WordTrace (prefixWord ++ tailWord_3402727) baseStart_3402727 baseEnd_3402727 := by
    simpa [prefixWord, tailWord_3402727, baseEnd_3402727] using wordTrace_append hprefix tailTrace_3402727
  have hstable : (prefixWord ++ tailWord_3402727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402727).length < 2 ^ (prefixWord ++ tailWord_3402727).sum := by decide
  have hdescent : baseEnd_3402727 < baseStart_3402727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402742 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_3402742 : Nat := 118140960795 + 3402742 * 2 ^ 59
def prefixEnd_3402742 : Nat := 4983230072969 + 3 ^ 40 * 3402742 * 2
def baseEnd_3402742 : Nat := 1164828126160953993317387

theorem tailTrace_3402742 : CollatzResearch.WordTrace tailWord_3402742 prefixEnd_3402742 1164828126160953993317387 := by
  unfold tailWord_3402742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7756762289903396931976655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82738797758969567274417653 7756762289903396931976655)
  ·
    refine ⟨11635143434855095397964983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7756762289903396931976655 11635143434855095397964983)
    ·
      refine ⟨17452715152282643096947475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11635143434855095397964983 17452715152282643096947475)
      ·
        refine ⟨26179072728423964645421213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17452715152282643096947475 26179072728423964645421213)
        ·
          refine ⟨9817152273158986742032955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26179072728423964645421213 9817152273158986742032955)
          ·
            refine ⟨14725728409738480113049433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9817152273158986742032955 14725728409738480113049433)
            ·
              refine ⟨11044296307303860084787075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14725728409738480113049433 11044296307303860084787075)
              ·
                refine ⟨16566444460955790127180613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11044296307303860084787075 16566444460955790127180613)
                ·
                  refine ⟨3106208336429210648846365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16566444460955790127180613 3106208336429210648846365)
                  ·
                    refine ⟨1164828126160953993317387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3106208336429210648846365 1164828126160953993317387)
                    ·
                      rfl

theorem cell22_3402742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_3402742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402742 prefixEnd_3402742 := by exact prefixLift 3402742
  have htrace : WordTrace (prefixWord ++ tailWord_3402742) baseStart_3402742 baseEnd_3402742 := by
    simpa [prefixWord, tailWord_3402742, baseEnd_3402742] using wordTrace_append hprefix tailTrace_3402742
  have hstable : (prefixWord ++ tailWord_3402742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402742).length < 2 ^ (prefixWord ++ tailWord_3402742).sum := by decide
  have hdescent : baseEnd_3402742 < baseStart_3402742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402800 : List Nat := [2, 1, 1, 1, 2, 4, 4, 2, 5]
def baseStart_3402800 : Nat := 118140960795 + 3402800 * 2 ^ 59
def prefixEnd_3402800 : Nat := 4983230072969 + 3 ^ 40 * 3402800 * 2
def baseEnd_3402800 : Nat := 388282660248753725122403

theorem tailTrace_3402800 : CollatzResearch.WordTrace tailWord_3402800 prefixEnd_3402800 388282660248753725122403 := by
  unfold tailWord_3402800
  simp only [CollatzResearch.WordTrace]
  refine ⟨62055156036122113408618927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82740208048162817878158569 62055156036122113408618927)
  ·
    refine ⟨93082734054183170112928391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62055156036122113408618927 93082734054183170112928391)
    ·
      refine ⟨139624101081274755169392587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93082734054183170112928391 139624101081274755169392587)
      ·
        refine ⟨209436151621912132754088881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139624101081274755169392587 209436151621912132754088881)
        ·
          refine ⟨157077113716434099565566661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209436151621912132754088881 157077113716434099565566661)
          ·
            refine ⟨29451958821831393668543749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157077113716434099565566661 29451958821831393668543749)
            ·
              refine ⟨5522242279093386312851953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29451958821831393668543749 5522242279093386312851953)
              ·
                refine ⟨4141681709320039734638965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5522242279093386312851953 4141681709320039734638965)
                ·
                  refine ⟨388282660248753725122403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4141681709320039734638965 388282660248753725122403)
                  ·
                    rfl

theorem cell22_3402800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 5].length) (baseStart_3402800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402800 prefixEnd_3402800 := by exact prefixLift 3402800
  have htrace : WordTrace (prefixWord ++ tailWord_3402800) baseStart_3402800 baseEnd_3402800 := by
    simpa [prefixWord, tailWord_3402800, baseEnd_3402800] using wordTrace_append hprefix tailTrace_3402800
  have hstable : (prefixWord ++ tailWord_3402800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402800).length < 2 ^ (prefixWord ++ tailWord_3402800).sum := by decide
  have hdescent : baseEnd_3402800 < baseStart_3402800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402830 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_3402830 : Nat := 118140960795 + 3402830 * 2 ^ 59
def prefixEnd_3402830 : Nat := 4983230072969 + 3 ^ 40 * 3402830 * 2
def baseEnd_3402830 : Nat := 1164858250359351097117117

theorem tailTrace_3402830 : CollatzResearch.WordTrace tailWord_3402830 prefixEnd_3402830 1164858250359351097117117 := by
  unfold tailWord_3402830
  simp only [CollatzResearch.WordTrace]
  refine ⟨15513925782766942742603743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82740937508090361293886629 15513925782766942742603743)
  ·
    refine ⟨23270888674150414113905615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15513925782766942742603743 23270888674150414113905615)
    ·
      refine ⟨34906333011225621170858423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23270888674150414113905615 34906333011225621170858423)
      ·
        refine ⟨52359499516838431756287635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34906333011225621170858423 52359499516838431756287635)
        ·
          refine ⟨78539249275257647634431453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52359499516838431756287635 78539249275257647634431453)
          ·
            refine ⟨29452218478221617862911795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78539249275257647634431453 29452218478221617862911795)
            ·
              refine ⟨44178327717332426794367693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29452218478221617862911795 44178327717332426794367693)
              ·
                refine ⟨16566872893999660047887885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44178327717332426794367693 16566872893999660047887885)
                ·
                  refine ⟨6212577335249872517957957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16566872893999660047887885 6212577335249872517957957)
                  ·
                    refine ⟨1164858250359351097117117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6212577335249872517957957 1164858250359351097117117)
                    ·
                      rfl

theorem cell22_3402830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_3402830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402830 prefixEnd_3402830 := by exact prefixLift 3402830
  have htrace : WordTrace (prefixWord ++ tailWord_3402830) baseStart_3402830 baseEnd_3402830 := by
    simpa [prefixWord, tailWord_3402830, baseEnd_3402830] using wordTrace_append hprefix tailTrace_3402830
  have hstable : (prefixWord ++ tailWord_3402830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402830).length < 2 ^ (prefixWord ++ tailWord_3402830).sum := by decide
  have hdescent : baseEnd_3402830 < baseStart_3402830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402862 : List Nat := [4, 1, 2, 2, 1, 3, 2, 1, 6]
def baseStart_3402862 : Nat := 118140960795 + 3402862 * 2 ^ 59
def prefixEnd_3402862 : Nat := 4983230072969 + 3 ^ 40 * 3402862 * 2
def baseEnd_3402862 : Nat := 388289734871104560105673

theorem tailTrace_3402862 : CollatzResearch.WordTrace tailWord_3402862 prefixEnd_3402862 388289734871104560105673 := by
  unfold tailWord_3402862
  simp only [CollatzResearch.WordTrace]
  refine ⟨15514071674752451425749355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82741715598679740937329893 15514071674752451425749355)
  ·
    refine ⟨23271107512128677138624033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15514071674752451425749355 23271107512128677138624033)
    ·
      refine ⟨17453330634096507853968025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23271107512128677138624033 17453330634096507853968025)
      ·
        refine ⟨13089997975572380890476019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17453330634096507853968025 13089997975572380890476019)
        ·
          refine ⟨19634996963358571335714029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13089997975572380890476019 19634996963358571335714029)
          ·
            refine ⟨7363123861259464250892761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19634996963358571335714029 7363123861259464250892761)
            ·
              refine ⟨5522342895944598188169571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7363123861259464250892761 5522342895944598188169571)
              ·
                refine ⟨8283514343916897282254357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5522342895944598188169571 8283514343916897282254357)
                ·
                  refine ⟨388289734871104560105673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8283514343916897282254357 388289734871104560105673)
                  ·
                    rfl

theorem cell22_3402862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_3402862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402862 prefixEnd_3402862 := by exact prefixLift 3402862
  have htrace : WordTrace (prefixWord ++ tailWord_3402862) baseStart_3402862 baseEnd_3402862 := by
    simpa [prefixWord, tailWord_3402862, baseEnd_3402862] using wordTrace_append hprefix tailTrace_3402862
  have hstable : (prefixWord ++ tailWord_3402862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402862).length < 2 ^ (prefixWord ++ tailWord_3402862).sum := by decide
  have hdescent : baseEnd_3402862 < baseStart_3402862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402890 : List Nat := [3, 1, 2, 3, 1, 1, 3, 8]
def baseStart_3402890 : Nat := 118140960795 + 3402890 * 2 ^ 59
def prefixEnd_3402890 : Nat := 4983230072969 + 3 ^ 40 * 3402890 * 2
def baseEnd_3402890 : Nat := 129430976620614548957437

theorem tailTrace_3402890 : CollatzResearch.WordTrace tailWord_3402890 prefixEnd_3402890 129430976620614548957437 := by
  unfold tailWord_3402890
  simp only [CollatzResearch.WordTrace]
  refine ⟨31028398660479543047003531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82742396427945448125342749 31028398660479543047003531)
  ·
    refine ⟨46542597990719314570505297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31028398660479543047003531 46542597990719314570505297)
    ·
      refine ⟨34906948493039485927878973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46542597990719314570505297 34906948493039485927878973)
      ·
        refine ⟨13090105684889807222954615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34906948493039485927878973 13090105684889807222954615)
        ·
          refine ⟨19635158527334710834431923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13090105684889807222954615 19635158527334710834431923)
          ·
            refine ⟨29452737791002066251647885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19635158527334710834431923 29452737791002066251647885)
            ·
              refine ⟨11044776671625774844367957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29452737791002066251647885 11044776671625774844367957)
              ·
                refine ⟨129430976620614548957437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11044776671625774844367957 129430976620614548957437)
                ·
                  rfl

theorem cell22_3402890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 8].length) (baseStart_3402890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402890 prefixEnd_3402890 := by exact prefixLift 3402890
  have htrace : WordTrace (prefixWord ++ tailWord_3402890) baseStart_3402890 baseEnd_3402890 := by
    simpa [prefixWord, tailWord_3402890, baseEnd_3402890] using wordTrace_append hprefix tailTrace_3402890
  have hstable : (prefixWord ++ tailWord_3402890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402890).length < 2 ^ (prefixWord ++ tailWord_3402890).sum := by decide
  have hdescent : baseEnd_3402890 < baseStart_3402890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402973 : List Nat := [1, 4, 3, 2, 2, 1, 1, 4, 1, 3]
def baseStart_3402973 : Nat := 118140960795 + 3402973 * 2 ^ 59
def prefixEnd_3402973 : Nat := 4983230072969 + 3 ^ 40 * 3402973 * 2
def baseEnd_3402973 : Nat := 1164907202181746390791679

theorem tailTrace_3402973 : CollatzResearch.WordTrace tailWord_3402973 prefixEnd_3402973 1164907202181746390791679 := by
  unfold tailWord_3402973
  simp only [CollatzResearch.WordTrace]
  refine ⟨124116621900617477363285573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82744414600411651575523715 124116621900617477363285573)
  ·
    refine ⟨23271866606365777005616045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124116621900617477363285573 23271866606365777005616045)
    ·
      refine ⟨8726949977387166377106017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23271866606365777005616045 8726949977387166377106017)
      ·
        refine ⟨6545212483040374782829513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8726949977387166377106017 6545212483040374782829513)
        ·
          refine ⟨4908909362280281087122135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6545212483040374782829513 4908909362280281087122135)
          ·
            refine ⟨7363364043420421630683203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4908909362280281087122135 7363364043420421630683203)
            ·
              refine ⟨11045046065130632446024805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7363364043420421630683203 11045046065130632446024805)
              ·
                refine ⟨2070946137211993583629651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11045046065130632446024805 2070946137211993583629651)
                ·
                  refine ⟨3106419205817990375444477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2070946137211993583629651 3106419205817990375444477)
                  ·
                    refine ⟨1164907202181746390791679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3106419205817990375444477 1164907202181746390791679)
                    ·
                      rfl

theorem cell22_3402973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_3402973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3402973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3402973 prefixEnd_3402973 := by exact prefixLift 3402973
  have htrace : WordTrace (prefixWord ++ tailWord_3402973) baseStart_3402973 baseEnd_3402973 := by
    simpa [prefixWord, tailWord_3402973, baseEnd_3402973] using wordTrace_append hprefix tailTrace_3402973
  have hstable : (prefixWord ++ tailWord_3402973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402973).length < 2 ^ (prefixWord ++ tailWord_3402973).sum := by decide
  have hdescent : baseEnd_3402973 < baseStart_3402973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403025 : List Nat := [1, 2, 2, 1, 1, 4, 11]
def baseStart_3403025 : Nat := 118140960795 + 3403025 * 2 ^ 59
def prefixEnd_3403025 : Nat := 4983230072969 + 3 ^ 40 * 3403025 * 2
def baseEnd_3403025 : Nat := 43145370475719836610797

theorem tailTrace_3403025 : CollatzResearch.WordTrace tailWord_3403025 prefixEnd_3403025 43145370475719836610797 := by
  unfold tailWord_3403025
  simp only [CollatzResearch.WordTrace]
  refine ⟨124118518496429090244178529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82745678997619393496119019 124118518496429090244178529)
  ·
    refine ⟨93088888872321817683133897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124118518496429090244178529 93088888872321817683133897)
    ·
      refine ⟨69816666654241363262350423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93088888872321817683133897 69816666654241363262350423)
      ·
        refine ⟨104724999981362044893525635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69816666654241363262350423 104724999981362044893525635)
        ·
          refine ⟨157087499972043067340288453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104724999981362044893525635 157087499972043067340288453)
          ·
            refine ⟨29453906244758075126304085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157087499972043067340288453 29453906244758075126304085)
            ·
              refine ⟨43145370475719836610797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29453906244758075126304085 43145370475719836610797)
              ·
                rfl

theorem cell22_3403025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 11].length) (baseStart_3403025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403025 prefixEnd_3403025 := by exact prefixLift 3403025
  have htrace : WordTrace (prefixWord ++ tailWord_3403025) baseStart_3403025 baseEnd_3403025 := by
    simpa [prefixWord, tailWord_3403025, baseEnd_3403025] using wordTrace_append hprefix tailTrace_3403025
  have hstable : (prefixWord ++ tailWord_3403025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403025).length < 2 ^ (prefixWord ++ tailWord_3403025).sum := by decide
  have hdescent : baseEnd_3403025 < baseStart_3403025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403059 : List Nat := [1, 1, 1, 2, 5, 4, 2, 6]
def baseStart_3403059 : Nat := 118140960795 + 3403059 * 2 ^ 59
def prefixEnd_3403059 : Nat := 4983230072969 + 3 ^ 40 * 3403059 * 2
def baseEnd_3403059 : Nat := 129437404637696759237935

theorem tailTrace_3403059 : CollatzResearch.WordTrace tailWord_3403059 prefixEnd_3403059 129437404637696759237935 := by
  unfold tailWord_3403059
  simp only [CollatzResearch.WordTrace]
  refine ⟨124119758578305914050916231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82746505718870609367277487 124119758578305914050916231)
  ·
    refine ⟨186179637867458871076374347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124119758578305914050916231 186179637867458871076374347)
    ·
      refine ⟨279269456801188306614561521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186179637867458871076374347 279269456801188306614561521)
      ·
        refine ⟨209452092600891229960921141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279269456801188306614561521 209452092600891229960921141)
        ·
          refine ⟨19636133681333552808836357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 209452092600891229960921141 19636133681333552808836357)
          ·
            refine ⟨3681775065250041151656817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19636133681333552808836357 3681775065250041151656817)
            ·
              refine ⟨2761331298937530863742613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3681775065250041151656817 2761331298937530863742613)
              ·
                refine ⟨129437404637696759237935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2761331298937530863742613 129437404637696759237935)
                ·
                  rfl

theorem cell22_3403059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 6].length) (baseStart_3403059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403059 prefixEnd_3403059 := by exact prefixLift 3403059
  have htrace : WordTrace (prefixWord ++ tailWord_3403059) baseStart_3403059 baseEnd_3403059 := by
    simpa [prefixWord, tailWord_3403059, baseEnd_3403059] using wordTrace_append hprefix tailTrace_3403059
  have hstable : (prefixWord ++ tailWord_3403059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403059).length < 2 ^ (prefixWord ++ tailWord_3403059).sum := by decide
  have hdescent : baseEnd_3403059 < baseStart_3403059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403104 : List Nat := [2, 1, 1, 3, 4, 2, 1, 3, 5]
def baseStart_3403104 : Nat := 118140960795 + 3403104 * 2 ^ 59
def prefixEnd_3403104 : Nat := 4983230072969 + 3 ^ 40 * 3403104 * 2
def baseEnd_3403104 : Nat := 388317348719635238588759

theorem tailTrace_3403104 : CollatzResearch.WordTrace tailWord_3403104 prefixEnd_3403104 388317348719635238588759 := by
  unfold tailWord_3403104
  simp only [CollatzResearch.WordTrace]
  refine ⟨62060699931571443368152183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82747599908761924490869577 62060699931571443368152183)
  ·
    refine ⟨93091049897357165052228275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62060699931571443368152183 93091049897357165052228275)
    ·
      refine ⟨139636574846035747578342413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93091049897357165052228275 139636574846035747578342413)
      ·
        refine ⟨52363715567263405341878405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139636574846035747578342413 52363715567263405341878405)
        ·
          refine ⟨9818196668861888501602201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52363715567263405341878405 9818196668861888501602201)
          ·
            refine ⟨7363647501646416376201651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9818196668861888501602201 7363647501646416376201651)
            ·
              refine ⟨11045471252469624564302477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7363647501646416376201651 11045471252469624564302477)
              ·
                refine ⟨4142051719676109211613429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11045471252469624564302477 4142051719676109211613429)
                ·
                  refine ⟨388317348719635238588759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4142051719676109211613429 388317348719635238588759)
                  ·
                    rfl

theorem cell22_3403104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 5].length) (baseStart_3403104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403104 prefixEnd_3403104 := by exact prefixLift 3403104
  have htrace : WordTrace (prefixWord ++ tailWord_3403104) baseStart_3403104 baseEnd_3403104 := by
    simpa [prefixWord, tailWord_3403104, baseEnd_3403104] using wordTrace_append hprefix tailTrace_3403104
  have hstable : (prefixWord ++ tailWord_3403104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403104).length < 2 ^ (prefixWord ++ tailWord_3403104).sum := by decide
  have hdescent : baseEnd_3403104 < baseStart_3403104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403138 : List Nat := [3, 4, 2, 1, 1, 2, 2, 2, 5]
def baseStart_3403138 : Nat := 118140960795 + 3403138 * 2 ^ 59
def prefixEnd_3403138 : Nat := 4983230072969 + 3 ^ 40 * 3403138 * 2
def baseEnd_3403138 : Nat := 388321228351246986805391

theorem tailTrace_3403138 : CollatzResearch.WordTrace tailWord_3403138 prefixEnd_3403138 388321228351246986805391 := by
  unfold tailWord_3403138
  simp only [CollatzResearch.WordTrace]
  refine ⟨31030659986254927635760517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82748426630013140362028045 31030659986254927635760517)
  ·
    refine ⟨5818248747422798931705097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31030659986254927635760517 5818248747422798931705097)
    ·
      refine ⟨4363686560567099198778823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5818248747422798931705097 4363686560567099198778823)
      ·
        refine ⟨6545529840850648798168235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4363686560567099198778823 6545529840850648798168235)
        ·
          refine ⟨9818294761275973197252353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6545529840850648798168235 9818294761275973197252353)
          ·
            refine ⟨7363721070956979897939265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9818294761275973197252353 7363721070956979897939265)
            ·
              refine ⟨5522790803217734923454449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7363721070956979897939265 5522790803217734923454449)
              ·
                refine ⟨4142093102413301192590837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5522790803217734923454449 4142093102413301192590837)
                ·
                  refine ⟨388321228351246986805391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4142093102413301192590837 388321228351246986805391)
                  ·
                    rfl

theorem cell22_3403138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_3403138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403138 prefixEnd_3403138 := by exact prefixLift 3403138
  have htrace : WordTrace (prefixWord ++ tailWord_3403138) baseStart_3403138 baseEnd_3403138 := by
    simpa [prefixWord, tailWord_3403138, baseEnd_3403138] using wordTrace_append hprefix tailTrace_3403138
  have hstable : (prefixWord ++ tailWord_3403138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403138).length < 2 ^ (prefixWord ++ tailWord_3403138).sum := by decide
  have hdescent : baseEnd_3403138 < baseStart_3403138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403147 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 3, 5]
def baseStart_3403147 : Nat := 118140960795 + 3403147 * 2 ^ 59
def prefixEnd_3403147 : Nat := 4983230072969 + 3 ^ 40 * 3403147 * 2
def baseEnd_3403147 : Nat := 1164966765937667936941145

theorem tailTrace_3403147 : CollatzResearch.WordTrace tailWord_3403147 prefixEnd_3403147 1164966765937667936941145 := by
  unfold tailWord_3403147
  simp only [CollatzResearch.WordTrace]
  refine ⟨124122968201987105080119695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82748645467991403386746463 124122968201987105080119695)
  ·
    refine ⟨186184452302980657620179543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124122968201987105080119695 186184452302980657620179543)
    ·
      refine ⟨279276678454470986430269315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186184452302980657620179543 279276678454470986430269315)
      ·
        refine ⟨418915017681706479645403973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279276678454470986430269315 418915017681706479645403973)
        ·
          refine ⟨78546565815319964933513245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 418915017681706479645403973 78546565815319964933513245)
          ·
            refine ⟨29454962180744986850067467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78546565815319964933513245 29454962180744986850067467)
            ·
              refine ⟨44182443271117480275101201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29454962180744986850067467 44182443271117480275101201)
              ·
                refine ⟨33136832453338110206325901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44182443271117480275101201 33136832453338110206325901)
                ·
                  refine ⟨12426312170001791327372213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33136832453338110206325901 12426312170001791327372213)
                  ·
                    refine ⟨1164966765937667936941145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12426312170001791327372213 1164966765937667936941145)
                    ·
                      rfl

theorem cell22_3403147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 5].length) (baseStart_3403147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403147 prefixEnd_3403147 := by exact prefixLift 3403147
  have htrace : WordTrace (prefixWord ++ tailWord_3403147) baseStart_3403147 baseEnd_3403147 := by
    simpa [prefixWord, tailWord_3403147, baseEnd_3403147] using wordTrace_append hprefix tailTrace_3403147
  have hstable : (prefixWord ++ tailWord_3403147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403147).length < 2 ^ (prefixWord ++ tailWord_3403147).sum := by decide
  have hdescent : baseEnd_3403147 < baseStart_3403147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403181 : List Nat := [1, 5, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_3403181 : Nat := 118140960795 + 3403181 * 2 ^ 59
def prefixEnd_3403181 : Nat := 4983230072969 + 3 ^ 40 * 3403181 * 2
def baseEnd_3403181 : Nat := 1164978404832503181591041

theorem tailTrace_3403181 : CollatzResearch.WordTrace tailWord_3403181 prefixEnd_3403181 1164978404832503181591041 := by
  unfold tailWord_3403181
  simp only [CollatzResearch.WordTrace]
  refine ⟨124124208283863928886857397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82749472189242619257904931 124124208283863928886857397)
  ·
    refine ⟨11636644526612243333142881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124124208283863928886857397 11636644526612243333142881)
    ·
      refine ⟨8727483394959182499857161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11636644526612243333142881 8727483394959182499857161)
      ·
        refine ⟨6545612546219386874892871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8727483394959182499857161 6545612546219386874892871)
        ·
          refine ⟨9818418819329080312339307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6545612546219386874892871 9818418819329080312339307)
          ·
            refine ⟨14727628228993620468508961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9818418819329080312339307 14727628228993620468508961)
            ·
              refine ⟨11045721171745215351381721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14727628228993620468508961 11045721171745215351381721)
              ·
                refine ⟨8284290878808911513536291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11045721171745215351381721 8284290878808911513536291)
                ·
                  refine ⟨12426436318213367270304437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8284290878808911513536291 12426436318213367270304437)
                  ·
                    refine ⟨1164978404832503181591041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12426436318213367270304437 1164978404832503181591041)
                    ·
                      rfl

theorem cell22_3403181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_3403181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403181 prefixEnd_3403181 := by exact prefixLift 3403181
  have htrace : WordTrace (prefixWord ++ tailWord_3403181) baseStart_3403181 baseEnd_3403181 := by
    simpa [prefixWord, tailWord_3403181, baseEnd_3403181] using wordTrace_append hprefix tailTrace_3403181
  have hstable : (prefixWord ++ tailWord_3403181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403181).length < 2 ^ (prefixWord ++ tailWord_3403181).sum := by decide
  have hdescent : baseEnd_3403181 < baseStart_3403181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403226 : List Nat := [3, 1, 1, 2, 3, 2, 2, 2, 3, 3]
def baseStart_3403226 : Nat := 118140960795 + 3403226 * 2 ^ 59
def prefixEnd_3403226 : Nat := 4983230072969 + 3 ^ 40 * 3403226 * 2
def baseEnd_3403226 : Nat := 1164993809252138064215903

theorem tailTrace_3403226 : CollatzResearch.WordTrace tailWord_3403226 prefixEnd_3403226 1164993809252138064215903 := by
  unfold tailWord_3403226
  simp only [CollatzResearch.WordTrace]
  refine ⟨31031462392175225393061383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82750566379133934381497021 31031462392175225393061383)
  ·
    refine ⟨46547193588262838089592075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31031462392175225393061383 46547193588262838089592075)
    ·
      refine ⟨69820790382394257134388113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46547193588262838089592075 69820790382394257134388113)
      ·
        refine ⟨52365592786795692850791085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69820790382394257134388113 52365592786795692850791085)
        ·
          refine ⟨19637097295048384819046657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52365592786795692850791085 19637097295048384819046657)
          ·
            refine ⟨14727822971286288614284993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19637097295048384819046657 14727822971286288614284993)
            ·
              refine ⟨11045867228464716460713745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14727822971286288614284993 11045867228464716460713745)
              ·
                refine ⟨8284400421348537345535309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11045867228464716460713745 8284400421348537345535309)
                ·
                  refine ⟨3106650158005701504575741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8284400421348537345535309 3106650158005701504575741)
                  ·
                    refine ⟨1164993809252138064215903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3106650158005701504575741 1164993809252138064215903)
                    ·
                      rfl

theorem cell22_3403226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_3403226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403226 prefixEnd_3403226 := by exact prefixLift 3403226
  have htrace : WordTrace (prefixWord ++ tailWord_3403226) baseStart_3403226 baseEnd_3403226 := by
    simpa [prefixWord, tailWord_3403226, baseEnd_3403226] using wordTrace_append hprefix tailTrace_3403226
  have hstable : (prefixWord ++ tailWord_3403226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403226).length < 2 ^ (prefixWord ++ tailWord_3403226).sum := by decide
  have hdescent : baseEnd_3403226 < baseStart_3403226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403239 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 7]
def baseStart_3403239 : Nat := 118140960795 + 3403239 * 2 ^ 59
def prefixEnd_3403239 : Nat := 4983230072969 + 3 ^ 40 * 3403239 * 2
def baseEnd_3403239 : Nat := 388332753139270121213621

theorem tailTrace_3403239 : CollatzResearch.WordTrace tailWord_3403239 prefixEnd_3403239 388332753139270121213621 := by
  unfold tailWord_3403239
  simp only [CollatzResearch.WordTrace]
  refine ⟨124126323717653804792468771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82750882478435869861645847 124126323717653804792468771)
  ·
    refine ⟨186189485576480707188703157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124126323717653804792468771 186189485576480707188703157)
    ·
      refine ⟨17455264272795066298940921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186189485576480707188703157 17455264272795066298940921)
      ·
        refine ⟨13091448204596299724205691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17455264272795066298940921 13091448204596299724205691)
        ·
          refine ⟨19637172306894449586308537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13091448204596299724205691 19637172306894449586308537)
          ·
            refine ⟨14727879230170837189731403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19637172306894449586308537 14727879230170837189731403)
            ·
              refine ⟨22091818845256255784597105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14727879230170837189731403 22091818845256255784597105)
              ·
                refine ⟨16568864133942191838447829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22091818845256255784597105 16568864133942191838447829)
                ·
                  refine ⟨388332753139270121213621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16568864133942191838447829 388332753139270121213621)
                  ·
                    rfl

theorem cell22_3403239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 7].length) (baseStart_3403239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403239 prefixEnd_3403239 := by exact prefixLift 3403239
  have htrace : WordTrace (prefixWord ++ tailWord_3403239) baseStart_3403239 baseEnd_3403239 := by
    simpa [prefixWord, tailWord_3403239, baseEnd_3403239] using wordTrace_append hprefix tailTrace_3403239
  have hstable : (prefixWord ++ tailWord_3403239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403239).length < 2 ^ (prefixWord ++ tailWord_3403239).sum := by decide
  have hdescent : baseEnd_3403239 < baseStart_3403239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403269 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 3, 4]
def baseStart_3403269 : Nat := 118140960795 + 3403269 * 2 ^ 59
def prefixEnd_3403269 : Nat := 4983230072969 + 3 ^ 40 * 3403269 * 2
def baseEnd_3403269 : Nat := 1165008529030900285390771

theorem tailTrace_3403269 : CollatzResearch.WordTrace tailWord_3403269 prefixEnd_3403269 1165008529030900285390771 := by
  unfold tailWord_3403269
  simp only [CollatzResearch.WordTrace]
  refine ⟨124127417907545119916060861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82751611938363413277373907 124127417907545119916060861)
  ·
    refine ⟨46547781715329419968522823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124127417907545119916060861 46547781715329419968522823)
    ·
      refine ⟨69821672572994129952784235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46547781715329419968522823 69821672572994129952784235)
      ·
        refine ⟨104732508859491194929176353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69821672572994129952784235 104732508859491194929176353)
        ·
          refine ⟨78549381644618396196882265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104732508859491194929176353 78549381644618396196882265)
          ·
            refine ⟨58912036233463797147661699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78549381644618396196882265 58912036233463797147661699)
            ·
              refine ⟨88368054350195695721492549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58912036233463797147661699 88368054350195695721492549)
              ·
                refine ⟨16569010190661692947779853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88368054350195695721492549 16569010190661692947779853)
                ·
                  refine ⟨6213378821498134855417445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16569010190661692947779853 6213378821498134855417445)
                  ·
                    refine ⟨1165008529030900285390771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6213378821498134855417445 1165008529030900285390771)
                    ·
                      rfl

theorem cell22_3403269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_3403269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403269 prefixEnd_3403269 := by exact prefixLift 3403269
  have htrace : WordTrace (prefixWord ++ tailWord_3403269) baseStart_3403269 baseEnd_3403269 := by
    simpa [prefixWord, tailWord_3403269, baseEnd_3403269] using wordTrace_append hprefix tailTrace_3403269
  have hstable : (prefixWord ++ tailWord_3403269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403269).length < 2 ^ (prefixWord ++ tailWord_3403269).sum := by decide
  have hdescent : baseEnd_3403269 < baseStart_3403269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403301 : List Nat := [1, 3, 1, 2, 2, 1, 1, 7, 4]
def baseStart_3403301 : Nat := 118140960795 + 3403301 * 2 ^ 59
def prefixEnd_3403301 : Nat := 4983230072969 + 3 ^ 40 * 3403301 * 2
def baseEnd_3403301 : Nat := 388339827761620956196891

theorem tailTrace_3403301 : CollatzResearch.WordTrace tailWord_3403301 prefixEnd_3403301 388339827761620956196891 := by
  unfold tailWord_3403301
  simp only [CollatzResearch.WordTrace]
  refine ⟨124128585043429189381225757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82752390028952792920817171 124128585043429189381225757)
  ·
    refine ⟨46548219391285946017959659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124128585043429189381225757 46548219391285946017959659)
    ·
      refine ⟨69822329086928919026939489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46548219391285946017959659 69822329086928919026939489)
      ·
        refine ⟨52366746815196689270204617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69822329086928919026939489 52366746815196689270204617)
        ·
          refine ⟨39275060111397516952653463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52366746815196689270204617 39275060111397516952653463)
          ·
            refine ⟨58912590167096275428980195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39275060111397516952653463 58912590167096275428980195)
            ·
              refine ⟨88368885250644413143470293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58912590167096275428980195 88368885250644413143470293)
              ·
                refine ⟨2071145748061978433050085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 88368885250644413143470293 2071145748061978433050085)
                ·
                  refine ⟨388339827761620956196891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2071145748061978433050085 388339827761620956196891)
                  ·
                    rfl

theorem cell22_3403301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 4].length) (baseStart_3403301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403301 prefixEnd_3403301 := by exact prefixLift 3403301
  have htrace : WordTrace (prefixWord ++ tailWord_3403301) baseStart_3403301 baseEnd_3403301 := by
    simpa [prefixWord, tailWord_3403301, baseEnd_3403301] using wordTrace_append hprefix tailTrace_3403301
  have hstable : (prefixWord ++ tailWord_3403301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403301).length < 2 ^ (prefixWord ++ tailWord_3403301).sum := by decide
  have hdescent : baseEnd_3403301 < baseStart_3403301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403314 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_3403314 : Nat := 118140960795 + 3403314 * 2 ^ 59
def prefixEnd_3403314 : Nat := 4983230072969 + 3 ^ 40 * 3403314 * 2
def baseEnd_3403314 : Nat := 1165023933450535168015633

theorem tailTrace_3403314 : CollatzResearch.WordTrace tailWord_3403314 prefixEnd_3403314 1165023933450535168015633 := by
  unfold tailWord_3403314
  simp only [CollatzResearch.WordTrace]
  refine ⟨31032264798095523150362249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82752706128254728400965997 31032264798095523150362249)
  ·
    refine ⟨23274198598571642362771687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31032264798095523150362249 23274198598571642362771687)
    ·
      refine ⟨34911297897857463544157531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23274198598571642362771687 34911297897857463544157531)
      ·
        refine ⟨52366946846786195316236297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34911297897857463544157531 52366946846786195316236297)
        ·
          refine ⟨39275210135089646487177223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52366946846786195316236297 39275210135089646487177223)
          ·
            refine ⟨58912815202634469730765835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39275210135089646487177223 58912815202634469730765835)
            ·
              refine ⟨88369222803951704596148753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58912815202634469730765835 88369222803951704596148753)
              ·
                refine ⟨66276917102963778447111565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88369222803951704596148753 66276917102963778447111565)
                ·
                  refine ⟨24853843913611416917666837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66276917102963778447111565 24853843913611416917666837)
                  ·
                    refine ⟨1165023933450535168015633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24853843913611416917666837 1165023933450535168015633)
                    ·
                      rfl

theorem cell22_3403314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_3403314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403314 prefixEnd_3403314 := by exact prefixLift 3403314
  have htrace : WordTrace (prefixWord ++ tailWord_3403314) baseStart_3403314 baseEnd_3403314 := by
    simpa [prefixWord, tailWord_3403314, baseEnd_3403314] using wordTrace_append hprefix tailTrace_3403314
  have hstable : (prefixWord ++ tailWord_3403314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403314).length < 2 ^ (prefixWord ++ tailWord_3403314).sum := by decide
  have hdescent : baseEnd_3403314 < baseStart_3403314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403361 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 5, 3]
def baseStart_3403361 : Nat := 118140960795 + 3403361 * 2 ^ 59
def prefixEnd_3403361 : Nat := 4983230072969 + 3 ^ 40 * 3403361 * 2
def baseEnd_3403361 : Nat := 1165040022511042712090489

theorem tailTrace_3403361 : CollatzResearch.WordTrace tailWord_3403361 prefixEnd_3403361 1165040022511042712090489 := by
  unfold tailWord_3403361
  simp only [CollatzResearch.WordTrace]
  refine ⟨124130773423211819628409937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82753848948807879752273291 124130773423211819628409937)
  ·
    refine ⟨93098080067408864721307453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124130773423211819628409937 93098080067408864721307453)
    ·
      refine ⟨34911780025278324270490295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93098080067408864721307453 34911780025278324270490295)
      ·
        refine ⟨52367670037917486405735443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34911780025278324270490295 52367670037917486405735443)
        ·
          refine ⟨78551505056876229608603165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52367670037917486405735443 78551505056876229608603165)
          ·
            refine ⟨29456814396328586103226187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78551505056876229608603165 29456814396328586103226187)
            ·
              refine ⟨44185221594492879154839281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29456814396328586103226187 44185221594492879154839281)
              ·
                refine ⟨33138916195869659366129461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44185221594492879154839281 33138916195869659366129461)
                ·
                  refine ⟨3106773393362780565574637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33138916195869659366129461 3106773393362780565574637)
                  ·
                    refine ⟨1165040022511042712090489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3106773393362780565574637 1165040022511042712090489)
                    ·
                      rfl

theorem cell22_3403361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_3403361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403361 prefixEnd_3403361 := by exact prefixLift 3403361
  have htrace : WordTrace (prefixWord ++ tailWord_3403361) baseStart_3403361 baseEnd_3403361 := by
    simpa [prefixWord, tailWord_3403361, baseEnd_3403361] using wordTrace_append hprefix tailTrace_3403361
  have hstable : (prefixWord ++ tailWord_3403361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403361).length < 2 ^ (prefixWord ++ tailWord_3403361).sum := by decide
  have hdescent : baseEnd_3403361 < baseStart_3403361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403378 : List Nat := [3, 2, 1, 2, 3, 1, 1, 3, 3, 3]
def baseStart_3403378 : Nat := 118140960795 + 3403378 * 2 ^ 59
def prefixEnd_3403378 : Nat := 4983230072969 + 3 ^ 40 * 3403378 * 2
def baseEnd_3403378 : Nat := 1165045841958460334415437

theorem tailTrace_3403378 : CollatzResearch.WordTrace tailWord_3403378 prefixEnd_3403378 1165045841958460334415437 := by
  unfold tailWord_3403378
  simp only [CollatzResearch.WordTrace]
  refine ⟨31032848366037557882944697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82754262309433487687852525 31032848366037557882944697)
  ·
    refine ⟨23274636274528168412208523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31032848366037557882944697 23274636274528168412208523)
    ·
      refine ⟨34911954411792252618312785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23274636274528168412208523 34911954411792252618312785)
      ·
        refine ⟨26183965808844189463734589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34911954411792252618312785 26183965808844189463734589)
        ·
          refine ⟨9818987178316571048900471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26183965808844189463734589 9818987178316571048900471)
          ·
            refine ⟨14728480767474856573350707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9818987178316571048900471 14728480767474856573350707)
            ·
              refine ⟨22092721151212284860026061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14728480767474856573350707 22092721151212284860026061)
              ·
                refine ⟨8284770431704606822509773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22092721151212284860026061 8284770431704606822509773)
                ·
                  refine ⟨3106788911889227558441165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8284770431704606822509773 3106788911889227558441165)
                  ·
                    refine ⟨1165045841958460334415437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3106788911889227558441165 1165045841958460334415437)
                    ·
                      rfl

theorem cell22_3403378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_3403378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403378 prefixEnd_3403378 := by exact prefixLift 3403378
  have htrace : WordTrace (prefixWord ++ tailWord_3403378) baseStart_3403378 baseEnd_3403378 := by
    simpa [prefixWord, tailWord_3403378, baseEnd_3403378] using wordTrace_append hprefix tailTrace_3403378
  have hstable : (prefixWord ++ tailWord_3403378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403378).length < 2 ^ (prefixWord ++ tailWord_3403378).sum := by decide
  have hdescent : baseEnd_3403378 < baseStart_3403378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403421 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_3403421 : Nat := 118140960795 + 3403421 * 2 ^ 59
def prefixEnd_3403421 : Nat := 4983230072969 + 3 ^ 40 * 3403421 * 2
def baseEnd_3403421 : Nat := 1165060561737222555590305

theorem tailTrace_3403421 : CollatzResearch.WordTrace tailWord_3403421 prefixEnd_3403421 1165060561737222555590305 := by
  unfold tailWord_3403421
  simp only [CollatzResearch.WordTrace]
  refine ⟨124132961802994449875594117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82755307868662966583729411 124132961802994449875594117)
  ·
    refine ⟨23274930338061459351673897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124132961802994449875594117 23274930338061459351673897)
    ·
      refine ⟨17456197753546094513755423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23274930338061459351673897 17456197753546094513755423)
      ·
        refine ⟨26184296630319141770633135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17456197753546094513755423 26184296630319141770633135)
        ·
          refine ⟨39276444945478712655949703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26184296630319141770633135 39276444945478712655949703)
          ·
            refine ⟨58914667418218068983924555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39276444945478712655949703 58914667418218068983924555)
            ·
              refine ⟨88372001127327103475886833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58914667418218068983924555 88372001127327103475886833)
              ·
                refine ⟨66279000845495327606915125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88372001127327103475886833 66279000845495327606915125)
                ·
                  refine ⟨6213656329265186963148293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66279000845495327606915125 6213656329265186963148293)
                  ·
                    refine ⟨1165060561737222555590305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6213656329265186963148293 1165060561737222555590305)
                    ·
                      rfl

theorem cell22_3403421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_3403421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403421 prefixEnd_3403421 := by exact prefixLift 3403421
  have htrace : WordTrace (prefixWord ++ tailWord_3403421) baseStart_3403421 baseEnd_3403421 := by
    simpa [prefixWord, tailWord_3403421, baseEnd_3403421] using wordTrace_append hprefix tailTrace_3403421
  have hstable : (prefixWord ++ tailWord_3403421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403421).length < 2 ^ (prefixWord ++ tailWord_3403421).sum := by decide
  have hdescent : baseEnd_3403421 < baseStart_3403421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403543 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 7]
def baseStart_3403543 : Nat := 118140960795 + 3403543 * 2 ^ 59
def prefixEnd_3403543 : Nat := 4983230072969 + 3 ^ 40 * 3403543 * 2
def baseEnd_3403543 : Nat := 388367441610151634679977

theorem tailTrace_3403543 : CollatzResearch.WordTrace tailWord_3403543 prefixEnd_3403543 388367441610151634679977 := by
  unfold tailWord_3403543
  simp only [CollatzResearch.WordTrace]
  refine ⟨124137411508552464711535283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82758274339034976474356855 124137411508552464711535283)
  ·
    refine ⟨186206117262828697067302925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124137411508552464711535283 186206117262828697067302925)
    ·
      refine ⟨69827293973560761400238597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186206117262828697067302925 69827293973560761400238597)
      ·
        refine ⟨13092617620042642762544737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69827293973560761400238597 13092617620042642762544737)
        ·
          refine ⟨9819463215031982071908553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13092617620042642762544737 9819463215031982071908553)
          ·
            refine ⟨7364597411273986553931415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9819463215031982071908553 7364597411273986553931415)
            ·
              refine ⟨11046896116910979830897123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7364597411273986553931415 11046896116910979830897123)
              ·
                refine ⟨16570344175366469746345685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11046896116910979830897123 16570344175366469746345685)
                ·
                  refine ⟨388367441610151634679977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16570344175366469746345685 388367441610151634679977)
                  ·
                    rfl

theorem cell22_3403543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 7].length) (baseStart_3403543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403543 prefixEnd_3403543 := by exact prefixLift 3403543
  have htrace : WordTrace (prefixWord ++ tailWord_3403543) baseStart_3403543 baseEnd_3403543 := by
    simpa [prefixWord, tailWord_3403543, baseEnd_3403543] using wordTrace_append hprefix tailTrace_3403543
  have hstable : (prefixWord ++ tailWord_3403543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403543).length < 2 ^ (prefixWord ++ tailWord_3403543).sum := by decide
  have hdescent : baseEnd_3403543 < baseStart_3403543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403605 : List Nat := [1, 3, 2, 2, 2, 4, 1, 1, 6]
def baseStart_3403605 : Nat := 118140960795 + 3403605 * 2 ^ 59
def prefixEnd_3403605 : Nat := 4983230072969 + 3 ^ 40 * 3403605 * 2
def baseEnd_3403605 : Nat := 388374516232502469663247

theorem tailTrace_3403605 : CollatzResearch.WordTrace tailWord_3403605 prefixEnd_3403605 388374516232502469663247 := by
  unfold tailWord_3403605
  simp only [CollatzResearch.WordTrace]
  refine ⟨124139672834327849300292269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82759781889551899533528179 124139672834327849300292269)
  ·
    refine ⟨46552377312872943487609601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124139672834327849300292269 46552377312872943487609601)
    ·
      refine ⟨34914282984654707615707201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46552377312872943487609601 34914282984654707615707201)
      ·
        refine ⟨26185712238491030711780401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34914282984654707615707201 26185712238491030711780401)
        ·
          refine ⟨19639284178868273033835301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26185712238491030711780401 19639284178868273033835301)
          ·
            refine ⟨3682365783537801193844119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19639284178868273033835301 3682365783537801193844119)
            ·
              refine ⟨5523548675306701790766179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3682365783537801193844119 5523548675306701790766179)
              ·
                refine ⟨8285323012960052686149269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5523548675306701790766179 8285323012960052686149269)
                ·
                  refine ⟨388374516232502469663247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8285323012960052686149269 388374516232502469663247)
                  ·
                    rfl

theorem cell22_3403605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_3403605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403605 prefixEnd_3403605 := by exact prefixLift 3403605
  have htrace : WordTrace (prefixWord ++ tailWord_3403605) baseStart_3403605 baseEnd_3403605 := by
    simpa [prefixWord, tailWord_3403605, baseEnd_3403605] using wordTrace_append hprefix tailTrace_3403605
  have hstable : (prefixWord ++ tailWord_3403605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403605).length < 2 ^ (prefixWord ++ tailWord_3403605).sum := by decide
  have hdescent : baseEnd_3403605 < baseStart_3403605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403656 : List Nat := [2, 1, 3, 3, 4, 1, 2, 2, 4]
def baseStart_3403656 : Nat := 118140960795 + 3403656 * 2 ^ 59
def prefixEnd_3403656 : Nat := 4983230072969 + 3 ^ 40 * 3403656 * 2
def baseEnd_3403656 : Nat := 388380335679920091988195

theorem tailTrace_3403656 : CollatzResearch.WordTrace tailWord_3403656 prefixEnd_3403656 388380335679920091988195 := by
  unfold tailWord_3403656
  simp only [CollatzResearch.WordTrace]
  refine ⟨62070766478571542505199411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82761021971428723340265881 62070766478571542505199411)
  ·
    refine ⟨93106149717857313757799117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62070766478571542505199411 93106149717857313757799117)
    ·
      refine ⟨34914806144196492659174669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93106149717857313757799117 34914806144196492659174669)
      ·
        refine ⟨13093052304073684747190501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34914806144196492659174669 13093052304073684747190501)
        ·
          refine ⟨2454947307013815890098219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13093052304073684747190501 2454947307013815890098219)
          ·
            refine ⟨3682420960520723835147329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2454947307013815890098219 3682420960520723835147329)
            ·
              refine ⟨2761815720390542876360497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3682420960520723835147329 2761815720390542876360497)
              ·
                refine ⟨2071361790292907157270373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2761815720390542876360497 2071361790292907157270373)
                ·
                  refine ⟨388380335679920091988195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2071361790292907157270373 388380335679920091988195)
                  ·
                    rfl

theorem cell22_3403656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 4].length) (baseStart_3403656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403656 prefixEnd_3403656 := by exact prefixLift 3403656
  have htrace : WordTrace (prefixWord ++ tailWord_3403656) baseStart_3403656 baseEnd_3403656 := by
    simpa [prefixWord, tailWord_3403656, baseEnd_3403656] using wordTrace_append hprefix tailTrace_3403656
  have hstable : (prefixWord ++ tailWord_3403656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403656).length < 2 ^ (prefixWord ++ tailWord_3403656).sum := by decide
  have hdescent : baseEnd_3403656 < baseStart_3403656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403710 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_3403710 : Nat := 118140960795 + 3403710 * 2 ^ 59
def prefixEnd_3403710 : Nat := 4983230072969 + 3 ^ 40 * 3403710 * 2
def baseEnd_3403710 : Nat := 1165159492343322135114419

theorem tailTrace_3403710 : CollatzResearch.WordTrace tailWord_3403710 prefixEnd_3403710 1165159492343322135114419 := by
  unfold tailWord_3403710
  simp only [CollatzResearch.WordTrace]
  refine ⟨15517937812368431529108073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82762334999298301488576389 15517937812368431529108073)
  ·
    refine ⟨11638453359276323646831055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15517937812368431529108073 11638453359276323646831055)
    ·
      refine ⟨17457680038914485470246583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11638453359276323646831055 17457680038914485470246583)
      ·
        refine ⟨26186520058371728205369875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17457680038914485470246583 26186520058371728205369875)
        ·
          refine ⟨39279780087557592308054813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26186520058371728205369875 39279780087557592308054813)
          ·
            refine ⟨14729917532834097115520555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39279780087557592308054813 14729917532834097115520555)
            ·
              refine ⟨22094876299251145673280833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14729917532834097115520555 22094876299251145673280833)
              ·
                refine ⟨16571157224438359254960625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22094876299251145673280833 16571157224438359254960625)
                ·
                  refine ⟨12428367918328769441220469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16571157224438359254960625 12428367918328769441220469)
                  ·
                    refine ⟨1165159492343322135114419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12428367918328769441220469 1165159492343322135114419)
                    ·
                      rfl

theorem cell22_3403710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_3403710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403710 prefixEnd_3403710 := by exact prefixLift 3403710
  have htrace : WordTrace (prefixWord ++ tailWord_3403710) baseStart_3403710 baseEnd_3403710 := by
    simpa [prefixWord, tailWord_3403710, baseEnd_3403710] using wordTrace_append hprefix tailTrace_3403710
  have hstable : (prefixWord ++ tailWord_3403710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403710).length < 2 ^ (prefixWord ++ tailWord_3403710).sum := by decide
  have hdescent : baseEnd_3403710 < baseStart_3403710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403768 : List Nat := [2, 1, 2, 1, 1, 3, 12]
def baseStart_3403768 : Nat := 118140960795 + 3403768 * 2 ^ 59
def prefixEnd_3403768 : Nat := 4983230072969 + 3 ^ 40 * 3403768 * 2
def baseEnd_3403768 : Nat := 43154790626986271006083

theorem tailTrace_3403768 : CollatzResearch.WordTrace tailWord_3403768 prefixEnd_3403768 43154790626986271006083 := by
  unfold tailWord_3403768
  simp only [CollatzResearch.WordTrace]
  refine ⟨62072808966368664069237979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82763745288491552092317305 62072808966368664069237979)
  ·
    refine ⟨93109213449552996103856969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62072808966368664069237979 93109213449552996103856969)
    ·
      refine ⟨69831910087164747077892727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93109213449552996103856969 69831910087164747077892727)
      ·
        refine ⟨104747865130747120616839091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69831910087164747077892727 104747865130747120616839091)
        ·
          refine ⟨157121797696120680925258637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104747865130747120616839091 157121797696120680925258637)
          ·
            refine ⟨58920674136045255346971989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157121797696120680925258637 58920674136045255346971989)
            ·
              refine ⟨43154790626986271006083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 58920674136045255346971989 43154790626986271006083)
              ·
                rfl

theorem cell22_3403768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 12].length) (baseStart_3403768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403768 prefixEnd_3403768 := by exact prefixLift 3403768
  have htrace : WordTrace (prefixWord ++ tailWord_3403768) baseStart_3403768 baseEnd_3403768 := by
    simpa [prefixWord, tailWord_3403768, baseEnd_3403768] using wordTrace_append hprefix tailTrace_3403768
  have hstable : (prefixWord ++ tailWord_3403768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403768).length < 2 ^ (prefixWord ++ tailWord_3403768).sum := by decide
  have hdescent : baseEnd_3403768 < baseStart_3403768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403772 : List Nat := [2, 2, 2, 1, 2, 2, 2, 4, 2, 3]
def baseStart_3403772 : Nat := 118140960795 + 3403772 * 2 ^ 59
def prefixEnd_3403772 : Nat := 4983230072969 + 3 ^ 40 * 3403772 * 2
def baseEnd_3403772 : Nat := 1165180716210374640064229

theorem tailTrace_3403772 : CollatzResearch.WordTrace tailWord_3403772 prefixEnd_3403772 1165180716210374640064229 := by
  unfold tailWord_3403772
  simp only [CollatzResearch.WordTrace]
  refine ⟨62072881912361418410810785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82763842549815224547747713 62072881912361418410810785)
  ·
    refine ⟨46554661434271063808108089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62072881912361418410810785 46554661434271063808108089)
    ·
      refine ⟨34915996075703297856081067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46554661434271063808108089 34915996075703297856081067)
      ·
        refine ⟨52373994113554946784121601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34915996075703297856081067 52373994113554946784121601)
        ·
          refine ⟨39280495585166210088091201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52373994113554946784121601 39280495585166210088091201)
          ·
            refine ⟨29460371688874657566068401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39280495585166210088091201 29460371688874657566068401)
            ·
              refine ⟨22095278766655993174551301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29460371688874657566068401 22095278766655993174551301)
              ·
                refine ⟨4142864768747998720228369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22095278766655993174551301 4142864768747998720228369)
                ·
                  refine ⟨3107148576560999040171277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4142864768747998720228369 3107148576560999040171277)
                  ·
                    refine ⟨1165180716210374640064229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3107148576560999040171277 1165180716210374640064229)
                    ·
                      rfl

theorem cell22_3403772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_3403772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403772 prefixEnd_3403772 := by exact prefixLift 3403772
  have htrace : WordTrace (prefixWord ++ tailWord_3403772) baseStart_3403772 baseEnd_3403772 := by
    simpa [prefixWord, tailWord_3403772, baseEnd_3403772] using wordTrace_append hprefix tailTrace_3403772
  have hstable : (prefixWord ++ tailWord_3403772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403772).length < 2 ^ (prefixWord ++ tailWord_3403772).sum := by decide
  have hdescent : baseEnd_3403772 < baseStart_3403772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403774 : List Nat := [4, 2, 2, 2, 1, 3, 1, 1, 6]
def baseStart_3403774 : Nat := 118140960795 + 3403774 * 2 ^ 59
def prefixEnd_3403774 : Nat := 4983230072969 + 3 ^ 40 * 3403774 * 2
def baseEnd_3403774 : Nat := 388393800283749100504741

theorem tailTrace_3403774 : CollatzResearch.WordTrace tailWord_3403774 prefixEnd_3403774 388393800283749100504741 := by
  unfold tailWord_3403774
  simp only [CollatzResearch.WordTrace]
  refine ⟨15518229596339448895399297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82763891180477060775462917 15518229596339448895399297)
  ·
    refine ⟨11638672197254586671549473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15518229596339448895399297 11638672197254586671549473)
    ·
      refine ⟨8729004147940940003662105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11638672197254586671549473 8729004147940940003662105)
      ·
        refine ⟨6546753110955705002746579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8729004147940940003662105 6546753110955705002746579)
        ·
          refine ⟨9820129666433557504119869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6546753110955705002746579 9820129666433557504119869)
          ·
            refine ⟨3682548624912584064044951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9820129666433557504119869 3682548624912584064044951)
            ·
              refine ⟨5523822937368876096067427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3682548624912584064044951 5523822937368876096067427)
              ·
                refine ⟨8285734406053314144101141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5523822937368876096067427 8285734406053314144101141)
                ·
                  refine ⟨388393800283749100504741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8285734406053314144101141 388393800283749100504741)
                  ·
                    rfl

theorem cell22_3403774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_3403774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403774 prefixEnd_3403774 := by exact prefixLift 3403774
  have htrace : WordTrace (prefixWord ++ tailWord_3403774) baseStart_3403774 baseEnd_3403774 := by
    simpa [prefixWord, tailWord_3403774, baseEnd_3403774] using wordTrace_append hprefix tailTrace_3403774
  have hstable : (prefixWord ++ tailWord_3403774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403774).length < 2 ^ (prefixWord ++ tailWord_3403774).sum := by decide
  have hdescent : baseEnd_3403774 < baseStart_3403774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403907 : List Nat := [1, 1, 1, 3, 3, 3, 3, 1, 1, 5]
def baseStart_3403907 : Nat := 118140960795 + 3403907 * 2 ^ 59
def prefixEnd_3403907 : Nat := 4983230072969 + 3 ^ 40 * 3403907 * 2
def baseEnd_3403907 : Nat := 1165226929469279287938815

theorem tailTrace_3403907 : CollatzResearch.WordTrace tailWord_3403907 prefixEnd_3403907 1165226929469279287938815 := by
  unfold tailWord_3403907
  simp only [CollatzResearch.WordTrace]
  refine ⟨124150687679233754877785975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82767125119489169918523983 124150687679233754877785975)
  ·
    refine ⟨186226031518850632316678963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124150687679233754877785975 186226031518850632316678963)
    ·
      refine ⟨279339047278275948475018445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186226031518850632316678963 279339047278275948475018445)
      ·
        refine ⟨104752142729353480678131917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279339047278275948475018445 104752142729353480678131917)
        ·
          refine ⟨39282053523507555254299469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104752142729353480678131917 39282053523507555254299469)
          ·
            refine ⟨14730770071315333220362301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39282053523507555254299469 14730770071315333220362301)
            ·
              refine ⟨5524038776743249957635863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14730770071315333220362301 5524038776743249957635863)
              ·
                refine ⟨8286058165114874936453795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5524038776743249957635863 8286058165114874936453795)
                ·
                  refine ⟨12429087247672312404680693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8286058165114874936453795 12429087247672312404680693)
                  ·
                    refine ⟨1165226929469279287938815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12429087247672312404680693 1165226929469279287938815)
                    ·
                      rfl

theorem cell22_3403907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 5].length) (baseStart_3403907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403907 prefixEnd_3403907 := by exact prefixLift 3403907
  have htrace : WordTrace (prefixWord ++ tailWord_3403907) baseStart_3403907 baseEnd_3403907 := by
    simpa [prefixWord, tailWord_3403907, baseEnd_3403907] using wordTrace_append hprefix tailTrace_3403907
  have hstable : (prefixWord ++ tailWord_3403907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403907).length < 2 ^ (prefixWord ++ tailWord_3403907).sum := by decide
  have hdescent : baseEnd_3403907 < baseStart_3403907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403920 : List Nat := [2, 1, 1, 1, 1, 1, 7, 8]
def baseStart_3403920 : Nat := 118140960795 + 3403920 * 2 ^ 59
def prefixEnd_3403920 : Nat := 4983230072969 + 3 ^ 40 * 3403920 * 2
def baseEnd_3403920 : Nat := 129470153292772398595975

theorem tailTrace_3403920 : CollatzResearch.WordTrace tailWord_3403920 prefixEnd_3403920 129470153292772398595975 := by
  unfold tailWord_3403920
  simp only [CollatzResearch.WordTrace]
  refine ⟨62075580914093329049004607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82767441218791105398672809 62075580914093329049004607)
  ·
    refine ⟨93113371371139993573506911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62075580914093329049004607 93113371371139993573506911)
    ·
      refine ⟨139670057056709990360260367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93113371371139993573506911 139670057056709990360260367)
      ·
        refine ⟨209505085585064985540390551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139670057056709990360260367 209505085585064985540390551)
        ·
          refine ⟨314257628377597478310585827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209505085585064985540390551 314257628377597478310585827)
          ·
            refine ⟨471386442566396217465878741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314257628377597478310585827 471386442566396217465878741)
            ·
              refine ⟨11048119747649911346856533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 471386442566396217465878741 11048119747649911346856533)
              ·
                refine ⟨129470153292772398595975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11048119747649911346856533 129470153292772398595975)
                ·
                  rfl

theorem cell22_3403920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 8].length) (baseStart_3403920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403920 prefixEnd_3403920 := by exact prefixLift 3403920
  have htrace : WordTrace (prefixWord ++ tailWord_3403920) baseStart_3403920 baseEnd_3403920 := by
    simpa [prefixWord, tailWord_3403920, baseEnd_3403920] using wordTrace_append hprefix tailTrace_3403920
  have hstable : (prefixWord ++ tailWord_3403920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403920).length < 2 ^ (prefixWord ++ tailWord_3403920).sum := by decide
  have hdescent : baseEnd_3403920 < baseStart_3403920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403922 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_3403922 : Nat := 118140960795 + 3403922 * 2 ^ 59
def prefixEnd_3403922 : Nat := 4983230072969 + 3 ^ 40 * 3403922 * 2
def baseEnd_3403922 : Nat := 1165232064275824248813769

theorem tailTrace_3403922 : CollatzResearch.WordTrace tailWord_3403922 prefixEnd_3403922 1165232064275824248813769 := by
  unfold tailWord_3403922
  simp only [CollatzResearch.WordTrace]
  refine ⟨31037808693544853109895505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82767489849452941626388013 31037808693544853109895505)
  ·
    refine ⟨23278356520158639832421629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31037808693544853109895505 23278356520158639832421629)
    ·
      refine ⟨8729383695059489937158111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23278356520158639832421629 8729383695059489937158111)
      ·
        refine ⟨13094075542589234905737167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8729383695059489937158111 13094075542589234905737167)
        ·
          refine ⟨19641113313883852358605751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13094075542589234905737167 19641113313883852358605751)
          ·
            refine ⟨29461669970825778537908627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19641113313883852358605751 29461669970825778537908627)
            ·
              refine ⟨44192504956238667806862941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29461669970825778537908627 44192504956238667806862941)
              ·
                refine ⟨16572189358589500427573603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44192504956238667806862941 16572189358589500427573603)
                ·
                  refine ⟨24858284037884250641360405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16572189358589500427573603 24858284037884250641360405)
                  ·
                    refine ⟨1165232064275824248813769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24858284037884250641360405 1165232064275824248813769)
                    ·
                      rfl

theorem cell22_3403922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_3403922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403922 prefixEnd_3403922 := by exact prefixLift 3403922
  have htrace : WordTrace (prefixWord ++ tailWord_3403922) baseStart_3403922 baseEnd_3403922 := by
    simpa [prefixWord, tailWord_3403922, baseEnd_3403922] using wordTrace_append hprefix tailTrace_3403922
  have hstable : (prefixWord ++ tailWord_3403922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403922).length < 2 ^ (prefixWord ++ tailWord_3403922).sum := by decide
  have hdescent : baseEnd_3403922 < baseStart_3403922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403937 : List Nat := [1, 2, 3, 3, 1, 4, 8]
def baseStart_3403937 : Nat := 118140960795 + 3403937 * 2 ^ 59
def prefixEnd_3403937 : Nat := 4983230072969 + 3 ^ 40 * 3403937 * 2
def baseEnd_3403937 : Nat := 43156933299347007766249

theorem tailTrace_3403937 : CollatzResearch.WordTrace tailWord_3403937 prefixEnd_3403937 43156933299347007766249 := by
  unfold tailWord_3403937
  simp only [CollatzResearch.WordTrace]
  refine ⟨124151781869125070001378065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82767854579416713334252043 124151781869125070001378065)
  ·
    refine ⟨93113836401843802501033549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124151781869125070001378065 93113836401843802501033549)
    ·
      refine ⟨34917688650691425937887581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93113836401843802501033549 34917688650691425937887581)
      ·
        refine ⟨13094133244009284726707843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34917688650691425937887581 13094133244009284726707843)
        ·
          refine ⟨19641199866013927090061765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13094133244009284726707843 19641199866013927090061765)
          ·
            refine ⟨3682724974877611329386581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19641199866013927090061765 3682724974877611329386581)
            ·
              refine ⟨43156933299347007766249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3682724974877611329386581 43156933299347007766249)
              ·
                rfl

theorem cell22_3403937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 8].length) (baseStart_3403937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403937 prefixEnd_3403937 := by exact prefixLift 3403937
  have htrace : WordTrace (prefixWord ++ tailWord_3403937) baseStart_3403937 baseEnd_3403937 := by
    simpa [prefixWord, tailWord_3403937, baseEnd_3403937] using wordTrace_append hprefix tailTrace_3403937
  have hstable : (prefixWord ++ tailWord_3403937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403937).length < 2 ^ (prefixWord ++ tailWord_3403937).sum := by decide
  have hdescent : baseEnd_3403937 < baseStart_3403937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403943 : List Nat := [1, 1, 6, 2, 2, 1, 3, 2, 4]
def baseStart_3403943 : Nat := 118140960795 + 3403943 * 2 ^ 59
def prefixEnd_3403943 : Nat := 4983230072969 + 3 ^ 40 * 3403943 * 2
def baseEnd_3403943 : Nat := 388413084334995731346235

theorem tailTrace_3403943 : CollatzResearch.WordTrace tailWord_3403943 prefixEnd_3403943 388413084334995731346235 := by
  unfold tailWord_3403943
  simp only [CollatzResearch.WordTrace]
  refine ⟨124152000707103333026096483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82768000471402222017397655 124152000707103333026096483)
  ·
    refine ⟨186228001060654999539144725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124152000707103333026096483 186228001060654999539144725)
    ·
      refine ⟨8729437549718203103397409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 186228001060654999539144725 8729437549718203103397409)
      ·
        refine ⟨6547078162288652327548057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8729437549718203103397409 6547078162288652327548057)
        ·
          refine ⟨4910308621716489245661043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6547078162288652327548057 4910308621716489245661043)
          ·
            refine ⟨7365462932574733868491565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4910308621716489245661043 7365462932574733868491565)
            ·
              refine ⟨2762048599715525200684337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7365462932574733868491565 2762048599715525200684337)
              ·
                refine ⟨2071536449786643900513253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2762048599715525200684337 2071536449786643900513253)
                ·
                  refine ⟨388413084334995731346235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2071536449786643900513253 388413084334995731346235)
                  ·
                    rfl

theorem cell22_3403943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 4].length) (baseStart_3403943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3403943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3403943 prefixEnd_3403943 := by exact prefixLift 3403943
  have htrace : WordTrace (prefixWord ++ tailWord_3403943) baseStart_3403943 baseEnd_3403943 := by
    simpa [prefixWord, tailWord_3403943, baseEnd_3403943] using wordTrace_append hprefix tailTrace_3403943
  have hstable : (prefixWord ++ tailWord_3403943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403943).length < 2 ^ (prefixWord ++ tailWord_3403943).sum := by decide
  have hdescent : baseEnd_3403943 < baseStart_3403943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404012 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 5, 4]
def baseStart_3404012 : Nat := 118140960795 + 3404012 * 2 ^ 59
def prefixEnd_3404012 : Nat := 4983230072969 + 3 ^ 40 * 3404012 * 2
def baseEnd_3404012 : Nat := 1165262873115094014063493

theorem tailTrace_3404012 : CollatzResearch.WordTrace tailWord_3404012 prefixEnd_3404012 1165262873115094014063493 := by
  unfold tailWord_3404012
  simp only [CollatzResearch.WordTrace]
  refine ⟨62077258671926678905179145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82769678229235571873572193 62077258671926678905179145)
  ·
    refine ⟨46557944003945009178884359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62077258671926678905179145 46557944003945009178884359)
    ·
      refine ⟨69836916005917513768326539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46557944003945009178884359 69836916005917513768326539)
      ·
        refine ⟨104755374008876270652489809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69836916005917513768326539 104755374008876270652489809)
        ·
          refine ⟨78566530506657202989367357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104755374008876270652489809 78566530506657202989367357)
          ·
            refine ⟨29462448939996451121012759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78566530506657202989367357 29462448939996451121012759)
            ·
              refine ⟨44193673409994676681519139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29462448939996451121012759 44193673409994676681519139)
              ·
                refine ⟨66290510114992015022278709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44193673409994676681519139 66290510114992015022278709)
                ·
                  refine ⟨6214735323280501408338629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66290510114992015022278709 6214735323280501408338629)
                  ·
                    refine ⟨1165262873115094014063493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6214735323280501408338629 1165262873115094014063493)
                    ·
                      rfl

theorem cell22_3404012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_3404012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404012 prefixEnd_3404012 := by exact prefixLift 3404012
  have htrace : WordTrace (prefixWord ++ tailWord_3404012) baseStart_3404012 baseEnd_3404012 := by
    simpa [prefixWord, tailWord_3404012, baseEnd_3404012] using wordTrace_append hprefix tailTrace_3404012
  have hstable : (prefixWord ++ tailWord_3404012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404012).length < 2 ^ (prefixWord ++ tailWord_3404012).sum := by decide
  have hdescent : baseEnd_3404012 < baseStart_3404012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404061 : List Nat := [1, 4, 2, 3, 2, 1, 2, 1, 6]
def baseStart_3404061 : Nat := 118140960795 + 3404061 * 2 ^ 59
def prefixEnd_3404061 : Nat := 4983230072969 + 3 ^ 40 * 3404061 * 2
def baseEnd_3404061 : Nat := 388426548938824739862781

theorem tailTrace_3404061 : CollatzResearch.WordTrace tailWord_3404061 prefixEnd_3404061 388426548938824739862781 := by
  unfold tailWord_3404061
  simp only [CollatzResearch.WordTrace]
  refine ⟨124156304520675839178892037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82770869680450559452594691 124156304520675839178892037)
  ·
    refine ⟨23279307097626719846042257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124156304520675839178892037 23279307097626719846042257)
    ·
      refine ⟨17459480323220039884531693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23279307097626719846042257 17459480323220039884531693)
      ·
        refine ⟨6547305121207514956699385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17459480323220039884531693 6547305121207514956699385)
        ·
          refine ⟨4910478840905636217524539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6547305121207514956699385 4910478840905636217524539)
          ·
            refine ⟨7365718261358454326286809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4910478840905636217524539 7365718261358454326286809)
            ·
              refine ⟨5524288696018840744715107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7365718261358454326286809 5524288696018840744715107)
              ·
                refine ⟨8286433044028261117072661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5524288696018840744715107 8286433044028261117072661)
                ·
                  refine ⟨388426548938824739862781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8286433044028261117072661 388426548938824739862781)
                  ·
                    rfl

theorem cell22_3404061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_3404061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404061 prefixEnd_3404061 := by exact prefixLift 3404061
  have htrace : WordTrace (prefixWord ++ tailWord_3404061) baseStart_3404061 baseEnd_3404061 := by
    simpa [prefixWord, tailWord_3404061, baseEnd_3404061] using wordTrace_append hprefix tailTrace_3404061
  have hstable : (prefixWord ++ tailWord_3404061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404061).length < 2 ^ (prefixWord ++ tailWord_3404061).sum := by decide
  have hdescent : baseEnd_3404061 < baseStart_3404061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404089 : List Nat := [1, 2, 1, 6, 1, 2, 1, 8]
def baseStart_3404089 : Nat := 118140960795 + 3404089 * 2 ^ 59
def prefixEnd_3404089 : Nat := 4983230072969 + 3 ^ 40 * 3404089 * 2
def baseEnd_3404089 : Nat := 129476581309854608876473

theorem tailTrace_3404089 : CollatzResearch.WordTrace tailWord_3404089 prefixEnd_3404089 129476581309854608876473 := by
  unfold tailWord_3404089
  simp only [CollatzResearch.WordTrace]
  refine ⟨124157325764574399960911321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82771550509716266640607547 124157325764574399960911321)
  ·
    refine ⟨93117994323430799970683491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124157325764574399960911321 93117994323430799970683491)
    ·
      refine ⟨139676991485146199956025237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93117994323430799970683491 139676991485146199956025237)
      ·
        refine ⟨6547358975866228122938683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139676991485146199956025237 6547358975866228122938683)
        ·
          refine ⟨9821038463799342184408025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6547358975866228122938683 9821038463799342184408025)
          ·
            refine ⟨7365778847849506638306019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9821038463799342184408025 7365778847849506638306019)
            ·
              refine ⟨11048668271774259957459029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7365778847849506638306019 11048668271774259957459029)
              ·
                refine ⟨129476581309854608876473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11048668271774259957459029 129476581309854608876473)
                ·
                  rfl

theorem cell22_3404089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 8].length) (baseStart_3404089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404089 prefixEnd_3404089 := by exact prefixLift 3404089
  have htrace : WordTrace (prefixWord ++ tailWord_3404089) baseStart_3404089 baseEnd_3404089 := by
    simpa [prefixWord, tailWord_3404089, baseEnd_3404089] using wordTrace_append hprefix tailTrace_3404089
  have hstable : (prefixWord ++ tailWord_3404089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404089).length < 2 ^ (prefixWord ++ tailWord_3404089).sum := by decide
  have hdescent : baseEnd_3404089 < baseStart_3404089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404104 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 5, 3]
def baseStart_3404104 : Nat := 118140960795 + 3404104 * 2 ^ 59
def prefixEnd_3404104 : Nat := 4983230072969 + 3 ^ 40 * 3404104 * 2
def baseEnd_3404104 : Nat := 1165294366595236440763211

theorem tailTrace_3404104 : CollatzResearch.WordTrace tailWord_3404104 prefixEnd_3404104 1165294366595236440763211 := by
  unfold tailWord_3404104
  simp only [CollatzResearch.WordTrace]
  refine ⟨62078936429760028761353683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82771915239680038348471577 62078936429760028761353683)
  ·
    refine ⟨93118404644640043142030525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62078936429760028761353683 93118404644640043142030525)
    ·
      refine ⟨34919401741740016178261447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93118404644640043142030525 34919401741740016178261447)
      ·
        refine ⟨52379102612610024267392171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34919401741740016178261447 52379102612610024267392171)
        ·
          refine ⟨78568653918915036401088257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52379102612610024267392171 78568653918915036401088257)
          ·
            refine ⟨58926490439186277300816193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78568653918915036401088257 58926490439186277300816193)
            ·
              refine ⟨44194867829389707975612145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58926490439186277300816193 44194867829389707975612145)
              ·
                refine ⟨33146150872042280981709109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44194867829389707975612145 33146150872042280981709109)
                ·
                  refine ⟨3107451644253963842035229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33146150872042280981709109 3107451644253963842035229)
                  ·
                    refine ⟨1165294366595236440763211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3107451644253963842035229 1165294366595236440763211)
                    ·
                      rfl

theorem cell22_3404104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_3404104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404104 prefixEnd_3404104 := by exact prefixLift 3404104
  have htrace : WordTrace (prefixWord ++ tailWord_3404104) baseStart_3404104 baseEnd_3404104 := by
    simpa [prefixWord, tailWord_3404104, baseEnd_3404104] using wordTrace_append hprefix tailTrace_3404104
  have hstable : (prefixWord ++ tailWord_3404104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404104).length < 2 ^ (prefixWord ++ tailWord_3404104).sum := by decide
  have hdescent : baseEnd_3404104 < baseStart_3404104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404147 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 2, 8]
def baseStart_3404147 : Nat := 118140960795 + 3404147 * 2 ^ 59
def prefixEnd_3404147 : Nat := 4983230072969 + 3 ^ 40 * 3404147 * 2
def baseEnd_3404147 : Nat := 1165309086373998661938079

theorem tailTrace_3404147 : CollatzResearch.WordTrace tailWord_3404147 prefixEnd_3404147 1165309086373998661938079 := by
  unfold tailWord_3404147
  simp only [CollatzResearch.WordTrace]
  refine ⟨124159441198364275866522695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82772960798909517244348463 124159441198364275866522695)
  ·
    refine ⟨186239161797546413799784043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124159441198364275866522695 186239161797546413799784043)
    ·
      refine ⟨279358742696319620699676065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186239161797546413799784043 279358742696319620699676065)
      ·
        refine ⟨209519057022239715524757049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279358742696319620699676065 209519057022239715524757049)
        ·
          refine ⟨157139292766679786643567787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209519057022239715524757049 157139292766679786643567787)
          ·
            refine ⟨235708939150019679965351681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157139292766679786643567787 235708939150019679965351681)
            ·
              refine ⟨176781704362514759974013761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235708939150019679965351681 176781704362514759974013761)
              ·
                refine ⟨132586278271886069980510321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176781704362514759974013761 132586278271886069980510321)
                ·
                  refine ⟨99439708703914552485382741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132586278271886069980510321 99439708703914552485382741)
                  ·
                    refine ⟨1165309086373998661938079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99439708703914552485382741 1165309086373998661938079)
                    ·
                      rfl

theorem cell22_3404147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 8].length) (baseStart_3404147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404147 prefixEnd_3404147 := by exact prefixLift 3404147
  have htrace : WordTrace (prefixWord ++ tailWord_3404147) baseStart_3404147 baseEnd_3404147 := by
    simpa [prefixWord, tailWord_3404147, baseEnd_3404147] using wordTrace_append hprefix tailTrace_3404147
  have hstable : (prefixWord ++ tailWord_3404147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404147).length < 2 ^ (prefixWord ++ tailWord_3404147).sum := by decide
  have hdescent : baseEnd_3404147 < baseStart_3404147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404245 : List Nat := [1, 3, 2, 3, 1, 3, 3, 1, 2, 3]
def baseStart_3404245 : Nat := 118140960795 + 3404245 * 2 ^ 59
def prefixEnd_3404245 : Nat := 4983230072969 + 3 ^ 40 * 3404245 * 2
def baseEnd_3404245 : Nat := 1165342633776759072987779

theorem tailTrace_3404245 : CollatzResearch.WordTrace tailWord_3404245 prefixEnd_3404245 1165342633776759072987779 := by
  unfold tailWord_3404245
  simp only [CollatzResearch.WordTrace]
  refine ⟨124163015552009238603590189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82775343701339492402393459 124163015552009238603590189)
  ·
    refine ⟨46561130832003464476346321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124163015552009238603590189 46561130832003464476346321)
    ·
      refine ⟨34920848124002598357259741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46561130832003464476346321 34920848124002598357259741)
      ·
        refine ⟨13095318046500974383972403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34920848124002598357259741 13095318046500974383972403)
        ·
          refine ⟨19642977069751461575958605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13095318046500974383972403 19642977069751461575958605)
          ·
            refine ⟨7366116401156798090984477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19642977069751461575958605 7366116401156798090984477)
            ·
              refine ⟨2762293650433799284119179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7366116401156798090984477 2762293650433799284119179)
              ·
                refine ⟨4143440475650698926178769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2762293650433799284119179 4143440475650698926178769)
                ·
                  refine ⟨3107580356738024194634077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4143440475650698926178769 3107580356738024194634077)
                  ·
                    refine ⟨1165342633776759072987779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3107580356738024194634077 1165342633776759072987779)
                    ·
                      rfl

theorem cell22_3404245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_3404245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404245 prefixEnd_3404245 := by exact prefixLift 3404245
  have htrace : WordTrace (prefixWord ++ tailWord_3404245) baseStart_3404245 baseEnd_3404245 := by
    simpa [prefixWord, tailWord_3404245, baseEnd_3404245] using wordTrace_append hprefix tailTrace_3404245
  have hstable : (prefixWord ++ tailWord_3404245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404245).length < 2 ^ (prefixWord ++ tailWord_3404245).sum := by decide
  have hdescent : baseEnd_3404245 < baseStart_3404245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404256 : List Nat := [2, 1, 1, 3, 1, 1, 3, 4, 3, 3]
def baseStart_3404256 : Nat := 118140960795 + 3404256 * 2 ^ 59
def prefixEnd_3404256 : Nat := 4983230072969 + 3 ^ 40 * 3404256 * 2
def baseEnd_3404256 : Nat := 1165346399301558710962745

theorem tailTrace_3404256 : CollatzResearch.WordTrace tailWord_3404256 prefixEnd_3404256 1165346399301558710962745 := by
  unfold tailWord_3404256
  simp only [CollatzResearch.WordTrace]
  refine ⟨62081708377484693741120311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82775611169979591654827081 62081708377484693741120311)
  ·
    refine ⟨93122562566227040611680467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62081708377484693741120311 93122562566227040611680467)
    ·
      refine ⟨139683843849340560917520701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93122562566227040611680467 139683843849340560917520701)
      ·
        refine ⟨52381441443502710344070263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139683843849340560917520701 52381441443502710344070263)
        ·
          refine ⟨78572162165254065516105395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52381441443502710344070263 78572162165254065516105395)
          ·
            refine ⟨117858243247881098274158093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78572162165254065516105395 117858243247881098274158093)
            ·
              refine ⟨44196841217955411852809285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117858243247881098274158093 44196841217955411852809285)
              ·
                refine ⟨8286907728366639722401741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44196841217955411852809285 8286907728366639722401741)
                ·
                  refine ⟨3107590398137489895900653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8286907728366639722401741 3107590398137489895900653)
                  ·
                    refine ⟨1165346399301558710962745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3107590398137489895900653 1165346399301558710962745)
                    ·
                      rfl

theorem cell22_3404256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 3, 3].length) (baseStart_3404256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404256 prefixEnd_3404256 := by exact prefixLift 3404256
  have htrace : WordTrace (prefixWord ++ tailWord_3404256) baseStart_3404256 baseEnd_3404256 := by
    simpa [prefixWord, tailWord_3404256, baseEnd_3404256] using wordTrace_append hprefix tailTrace_3404256
  have hstable : (prefixWord ++ tailWord_3404256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404256).length < 2 ^ (prefixWord ++ tailWord_3404256).sum := by decide
  have hdescent : baseEnd_3404256 < baseStart_3404256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404363 : List Nat := [1, 1, 1, 1, 3, 1, 6, 3, 2, 3]
def baseStart_3404363 : Nat := 118140960795 + 3404363 * 2 ^ 59
def prefixEnd_3404363 : Nat := 4983230072969 + 3 ^ 40 * 3404363 * 2
def baseEnd_3404363 : Nat := 1165383027588246098537417

theorem tailTrace_3404363 : CollatzResearch.WordTrace tailWord_3404363 prefixEnd_3404363 1165383027588246098537417 := by
  unfold tailWord_3404363
  simp only [CollatzResearch.WordTrace]
  refine ⟨124167319365581744756385743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82778212910387829837590495 124167319365581744756385743)
  ·
    refine ⟨186250979048372617134578615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124167319365581744756385743 186250979048372617134578615)
    ·
      refine ⟨279376468572558925701867923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186250979048372617134578615 279376468572558925701867923)
      ·
        refine ⟨419064702858838388552801885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279376468572558925701867923 419064702858838388552801885)
        ·
          refine ⟨157149263572064395707300707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 419064702858838388552801885 157149263572064395707300707)
          ·
            refine ⟨235723895358096593560951061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157149263572064395707300707 235723895358096593560951061)
            ·
              refine ⟨11049557594910777823169581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 235723895358096593560951061 11049557594910777823169581)
              ·
                refine ⟨4143584098091541683688593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11049557594910777823169581 4143584098091541683688593)
                ·
                  refine ⟨3107688073568656262766445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4143584098091541683688593 3107688073568656262766445)
                  ·
                    refine ⟨1165383027588246098537417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3107688073568656262766445 1165383027588246098537417)
                    ·
                      rfl

theorem cell22_3404363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 3].length) (baseStart_3404363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404363 prefixEnd_3404363 := by exact prefixLift 3404363
  have htrace : WordTrace (prefixWord ++ tailWord_3404363) baseStart_3404363 baseEnd_3404363 := by
    simpa [prefixWord, tailWord_3404363, baseEnd_3404363] using wordTrace_append hprefix tailTrace_3404363
  have hstable : (prefixWord ++ tailWord_3404363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404363).length < 2 ^ (prefixWord ++ tailWord_3404363).sum := by decide
  have hdescent : baseEnd_3404363 < baseStart_3404363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404397 : List Nat := [1, 5, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_3404397 : Nat := 118140960795 + 3404397 * 2 ^ 59
def prefixEnd_3404397 : Nat := 4983230072969 + 3 ^ 40 * 3404397 * 2
def baseEnd_3404397 : Nat := 1165394666483081343187313

theorem tailTrace_3404397 : CollatzResearch.WordTrace tailWord_3404397 prefixEnd_3404397 1165394666483081343187313 := by
  unfold tailWord_3404397
  simp only [CollatzResearch.WordTrace]
  refine ⟨124168559447458568563123445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82779039631639045708748963 124168559447458568563123445)
  ·
    refine ⟨11640802448199240802792823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124168559447458568563123445 11640802448199240802792823)
    ·
      refine ⟨17461203672298861204189235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11640802448199240802792823 17461203672298861204189235)
      ·
        refine ⟨26191805508448291806283853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17461203672298861204189235 26191805508448291806283853)
        ·
          refine ⟨9821927065668109427356445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26191805508448291806283853 9821927065668109427356445)
          ·
            refine ⟨3683222649625541035258667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9821927065668109427356445 3683222649625541035258667)
            ·
              refine ⟨5524833974438311552888001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3683222649625541035258667 5524833974438311552888001)
              ·
                refine ⟨4143625480828733664666001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5524833974438311552888001 4143625480828733664666001)
                ·
                  refine ⟨3107719110621550248499501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4143625480828733664666001 3107719110621550248499501)
                  ·
                    refine ⟨1165394666483081343187313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3107719110621550248499501 1165394666483081343187313)
                    ·
                      rfl

theorem cell22_3404397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_3404397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404397 prefixEnd_3404397 := by exact prefixLift 3404397
  have htrace : WordTrace (prefixWord ++ tailWord_3404397) baseStart_3404397 baseEnd_3404397 := by
    simpa [prefixWord, tailWord_3404397, baseEnd_3404397] using wordTrace_append hprefix tailTrace_3404397
  have hstable : (prefixWord ++ tailWord_3404397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404397).length < 2 ^ (prefixWord ++ tailWord_3404397).sum := by decide
  have hdescent : baseEnd_3404397 < baseStart_3404397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404496 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 5, 6]
def baseStart_3404496 : Nat := 118140960795 + 3404496 * 2 ^ 59
def prefixEnd_3404496 : Nat := 4983230072969 + 3 ^ 40 * 3404496 * 2
def baseEnd_3404496 : Nat := 1165428556206278084962009

theorem tailTrace_3404496 : CollatzResearch.WordTrace tailWord_3404496 prefixEnd_3404496 1165428556206278084962009 := by
  unfold tailWord_3404496
  simp only [CollatzResearch.WordTrace]
  refine ⟨62086085137049954235488671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82781446849399938980651561 62086085137049954235488671)
  ·
    refine ⟨93129127705574931353233007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62086085137049954235488671 93129127705574931353233007)
    ·
      refine ⟨139693691558362397029849511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93129127705574931353233007 139693691558362397029849511)
      ·
        refine ⟨209540537337543595544774267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139693691558362397029849511 209540537337543595544774267)
        ·
          refine ⟨314310806006315393317161401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209540537337543595544774267 314310806006315393317161401)
          ·
            refine ⟨235733104504736544987871051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314310806006315393317161401 235733104504736544987871051)
            ·
              refine ⟨353599656757104817481806577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235733104504736544987871051 353599656757104817481806577)
              ·
                refine ⟨265199742567828613111354933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353599656757104817481806577 265199742567828613111354933)
                ·
                  refine ⟨24862475865733932479189525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 265199742567828613111354933 24862475865733932479189525)
                  ·
                    refine ⟨1165428556206278084962009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24862475865733932479189525 1165428556206278084962009)
                    ·
                      rfl

theorem cell22_3404496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_3404496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404496 prefixEnd_3404496 := by exact prefixLift 3404496
  have htrace : WordTrace (prefixWord ++ tailWord_3404496) baseStart_3404496 baseEnd_3404496 := by
    simpa [prefixWord, tailWord_3404496, baseEnd_3404496] using wordTrace_append hprefix tailTrace_3404496
  have hstable : (prefixWord ++ tailWord_3404496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404496).length < 2 ^ (prefixWord ++ tailWord_3404496).sum := by decide
  have hdescent : baseEnd_3404496 < baseStart_3404496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404511 : List Nat := [1, 1, 2, 3, 2, 13]
def baseStart_3404511 : Nat := 118140960795 + 3404511 * 2 ^ 59
def prefixEnd_3404511 : Nat := 4983230072969 + 3 ^ 40 * 3404511 * 2
def baseEnd_3404511 : Nat := 14388070259417568467123

theorem tailTrace_3404511 : CollatzResearch.WordTrace tailWord_3404511 prefixEnd_3404511 14388070259417568467123 := by
  unfold tailWord_3404511
  simp only [CollatzResearch.WordTrace]
  refine ⟨124172717369045566032773387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82781811579363710688515591 124172717369045566032773387)
  ·
    refine ⟨186259076053568349049160081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124172717369045566032773387 186259076053568349049160081)
    ·
      refine ⟨139694307040176261786870061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186259076053568349049160081 139694307040176261786870061)
      ·
        refine ⟨52385365140066098170076273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139694307040176261786870061 52385365140066098170076273)
        ·
          refine ⟨39289023855049573627557205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52385365140066098170076273 39289023855049573627557205)
          ·
            refine ⟨14388070259417568467123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 39289023855049573627557205 14388070259417568467123)
            ·
              rfl

theorem cell22_3404511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 13].length) (baseStart_3404511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404511 prefixEnd_3404511 := by exact prefixLift 3404511
  have htrace : WordTrace (prefixWord ++ tailWord_3404511) baseStart_3404511 baseEnd_3404511 := by
    simpa [prefixWord, tailWord_3404511, baseEnd_3404511] using wordTrace_append hprefix tailTrace_3404511
  have hstable : (prefixWord ++ tailWord_3404511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404511).length < 2 ^ (prefixWord ++ tailWord_3404511).sum := by decide
  have hdescent : baseEnd_3404511 < baseStart_3404511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404517 : List Nat := [1, 3, 1, 4, 1, 2, 4, 2, 4]
def baseStart_3404517 : Nat := 118140960795 + 3404517 * 2 ^ 59
def prefixEnd_3404517 : Nat := 4983230072969 + 3 ^ 40 * 3404517 * 2
def baseEnd_3404517 : Nat := 388478581645147010062315

theorem tailTrace_3404517 : CollatzResearch.WordTrace tailWord_3404517 prefixEnd_3404517 388478581645147010062315 := by
  unfold tailWord_3404517
  simp only [CollatzResearch.WordTrace]
  refine ⟨124172936207023829057491805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82781957471349219371661203 124172936207023829057491805)
  ·
    refine ⟨46564851077633935896559427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124172936207023829057491805 46564851077633935896559427)
    ·
      refine ⟨69847276616450903844839141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46564851077633935896559427 69847276616450903844839141)
      ·
        refine ⟨13096364365584544470907339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69847276616450903844839141 13096364365584544470907339)
        ·
          refine ⟨19644546548376816706361009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13096364365584544470907339 19644546548376816706361009)
          ·
            refine ⟨14733409911282612529770757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19644546548376816706361009 14733409911282612529770757)
            ·
              refine ⟨2762514358365489849332017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14733409911282612529770757 2762514358365489849332017)
              ·
                refine ⟨2071885768774117386999013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2762514358365489849332017 2071885768774117386999013)
                ·
                  refine ⟨388478581645147010062315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2071885768774117386999013 388478581645147010062315)
                  ·
                    rfl

theorem cell22_3404517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 4].length) (baseStart_3404517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404517 prefixEnd_3404517 := by exact prefixLift 3404517
  have htrace : WordTrace (prefixWord ++ tailWord_3404517) baseStart_3404517 baseEnd_3404517 := by
    simpa [prefixWord, tailWord_3404517, baseEnd_3404517] using wordTrace_append hprefix tailTrace_3404517
  have hstable : (prefixWord ++ tailWord_3404517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404517).length < 2 ^ (prefixWord ++ tailWord_3404517).sum := by decide
  have hdescent : baseEnd_3404517 < baseStart_3404517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404577 : List Nat := [1, 2, 3, 2, 1, 2, 1, 6, 1, 3]
def baseStart_3404577 : Nat := 118140960795 + 3404577 * 2 ^ 59
def prefixEnd_3404577 : Nat := 4983230072969 + 3 ^ 40 * 3404577 * 2
def baseEnd_3404577 : Nat := 1165456284161620873686761

theorem tailTrace_3404577 : CollatzResearch.WordTrace tailWord_3404577 prefixEnd_3404577 1165456284161620873686761 := by
  unfold tailWord_3404577
  simp only [CollatzResearch.WordTrace]
  refine ⟨124175124586806459304675985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82783416391204306203117323 124175124586806459304675985)
  ·
    refine ⟨93131343440104844478506989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124175124586806459304675985 93131343440104844478506989)
    ·
      refine ⟨34924253790039316679440121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93131343440104844478506989 34924253790039316679440121)
      ·
        refine ⟨26193190342529487509580091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34924253790039316679440121 26193190342529487509580091)
        ·
          refine ⟨39289785513794231264370137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26193190342529487509580091 39289785513794231264370137)
          ·
            refine ⟨29467339135345673448277603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39289785513794231264370137 29467339135345673448277603)
            ·
              refine ⟨44201008703018510172416405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29467339135345673448277603 44201008703018510172416405)
              ·
                refine ⟨2071922282953992664332019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44201008703018510172416405 2071922282953992664332019)
                ·
                  refine ⟨3107883424430988996498029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2071922282953992664332019 3107883424430988996498029)
                  ·
                    refine ⟨1165456284161620873686761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3107883424430988996498029 1165456284161620873686761)
                    ·
                      rfl

theorem cell22_3404577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_3404577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404577 prefixEnd_3404577 := by exact prefixLift 3404577
  have htrace : WordTrace (prefixWord ++ tailWord_3404577) baseStart_3404577 baseEnd_3404577 := by
    simpa [prefixWord, tailWord_3404577, baseEnd_3404577] using wordTrace_append hprefix tailTrace_3404577
  have hstable : (prefixWord ++ tailWord_3404577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404577).length < 2 ^ (prefixWord ++ tailWord_3404577).sum := by decide
  have hdescent : baseEnd_3404577 < baseStart_3404577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404588 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 2, 5]
def baseStart_3404588 : Nat := 118140960795 + 3404588 * 2 ^ 59
def prefixEnd_3404588 : Nat := 4983230072969 + 3 ^ 40 * 3404588 * 2
def baseEnd_3404588 : Nat := 1165460049686420511661727

theorem tailTrace_3404588 : CollatzResearch.WordTrace tailWord_3404588 prefixEnd_3404588 1165460049686420511661727 := by
  unfold tailWord_3404588
  simp only [CollatzResearch.WordTrace]
  refine ⟨62087762894883304091663209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82783683859844405455550945 62087762894883304091663209)
  ·
    refine ⟨46565822171162478068747407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62087762894883304091663209 46565822171162478068747407)
    ·
      refine ⟨69848733256743717103121111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46565822171162478068747407 69848733256743717103121111)
      ·
        refine ⟨104773099885115575654681667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69848733256743717103121111 104773099885115575654681667)
        ·
          refine ⟨157159649827673363482022501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104773099885115575654681667 157159649827673363482022501)
          ·
            refine ⟨29467434342688755652879219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157159649827673363482022501 29467434342688755652879219)
            ·
              refine ⟨44201151514033133479318829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29467434342688755652879219 44201151514033133479318829)
              ·
                refine ⟨16575431817762425054744561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44201151514033133479318829 16575431817762425054744561)
                ·
                  refine ⟨12431573863321818791058421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16575431817762425054744561 12431573863321818791058421)
                  ·
                    refine ⟨1165460049686420511661727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12431573863321818791058421 1165460049686420511661727)
                    ·
                      rfl

theorem cell22_3404588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_3404588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404588 prefixEnd_3404588 := by exact prefixLift 3404588
  have htrace : WordTrace (prefixWord ++ tailWord_3404588) baseStart_3404588 baseEnd_3404588 := by
    simpa [prefixWord, tailWord_3404588, baseEnd_3404588] using wordTrace_append hprefix tailTrace_3404588
  have hstable : (prefixWord ++ tailWord_3404588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404588).length < 2 ^ (prefixWord ++ tailWord_3404588).sum := by decide
  have hdescent : baseEnd_3404588 < baseStart_3404588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404665 : List Nat := [1, 2, 1, 3, 2, 3, 1, 3, 2, 4]
def baseStart_3404665 : Nat := 118140960795 + 3404665 * 2 ^ 59
def prefixEnd_3404665 : Nat := 4983230072969 + 3 ^ 40 * 3404665 * 2
def baseEnd_3404665 : Nat := 1165486408360017977486491

theorem tailTrace_3404665 : CollatzResearch.WordTrace tailWord_3404665 prefixEnd_3404665 1165486408360017977486491 := by
  unfold tailWord_3404665
  simp only [CollatzResearch.WordTrace]
  refine ⟨124178334210487650333879449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82785556140325100222586299 124178334210487650333879449)
  ·
    refine ⟨93133750657865737750409587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124178334210487650333879449 93133750657865737750409587)
    ·
      refine ⟨139700625986798606625614381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93133750657865737750409587 139700625986798606625614381)
      ·
        refine ⟨52387734745049477484605393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139700625986798606625614381 52387734745049477484605393)
        ·
          refine ⟨39290801058787108113454045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52387734745049477484605393 39290801058787108113454045)
          ·
            refine ⟨14734050397045165542545267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39290801058787108113454045 14734050397045165542545267)
            ·
              refine ⟨22101075595567748313817901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14734050397045165542545267 22101075595567748313817901)
              ·
                refine ⟨8287903348337905617681713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22101075595567748313817901 8287903348337905617681713)
                ·
                  refine ⟨6215927511253429213261285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8287903348337905617681713 6215927511253429213261285)
                  ·
                    refine ⟨1165486408360017977486491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6215927511253429213261285 1165486408360017977486491)
                    ·
                      rfl

theorem cell22_3404665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 4].length) (baseStart_3404665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404665 prefixEnd_3404665 := by exact prefixLift 3404665
  have htrace : WordTrace (prefixWord ++ tailWord_3404665) baseStart_3404665 baseEnd_3404665 := by
    simpa [prefixWord, tailWord_3404665, baseEnd_3404665] using wordTrace_append hprefix tailTrace_3404665
  have hstable : (prefixWord ++ tailWord_3404665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404665).length < 2 ^ (prefixWord ++ tailWord_3404665).sum := by decide
  have hdescent : baseEnd_3404665 < baseStart_3404665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404682 : List Nat := [3, 1, 2, 4, 1, 1, 2, 2, 2, 4]
def baseStart_3404682 : Nat := 118140960795 + 3404682 * 2 ^ 59
def prefixEnd_3404682 : Nat := 4983230072969 + 3 ^ 40 * 3404682 * 2
def baseEnd_3404682 : Nat := 1165492227807435599811439

theorem tailTrace_3404682 : CollatzResearch.WordTrace tailWord_3404682 prefixEnd_3404682 1165492227807435599811439 := by
  unfold tailWord_3404682
  simp only [CollatzResearch.WordTrace]
  refine ⟨31044738562856515559312075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82785969500950708158165533 31044738562856515559312075)
  ·
    refine ⟨46567107844284773338968113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31044738562856515559312075 46567107844284773338968113)
    ·
      refine ⟨34925330883213580004226085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46567107844284773338968113 34925330883213580004226085)
      ·
        refine ⟨6548499540602546250792391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34925330883213580004226085 6548499540602546250792391)
        ·
          refine ⟨9822749310903819376188587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6548499540602546250792391 9822749310903819376188587)
          ·
            refine ⟨14734123966355729064282881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9822749310903819376188587 14734123966355729064282881)
            ·
              refine ⟨11050592974766796798212161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14734123966355729064282881 11050592974766796798212161)
              ·
                refine ⟨8287944731075097598659121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11050592974766796798212161 8287944731075097598659121)
                ·
                  refine ⟨6215958548306323198994341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8287944731075097598659121 6215958548306323198994341)
                  ·
                    refine ⟨1165492227807435599811439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6215958548306323198994341 1165492227807435599811439)
                    ·
                      rfl

theorem cell22_3404682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_3404682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404682 prefixEnd_3404682 := by exact prefixLift 3404682
  have htrace : WordTrace (prefixWord ++ tailWord_3404682) baseStart_3404682 baseEnd_3404682 := by
    simpa [prefixWord, tailWord_3404682, baseEnd_3404682] using wordTrace_append hprefix tailTrace_3404682
  have hstable : (prefixWord ++ tailWord_3404682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404682).length < 2 ^ (prefixWord ++ tailWord_3404682).sum := by decide
  have hdescent : baseEnd_3404682 < baseStart_3404682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404725 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 7]
def baseStart_3404725 : Nat := 118140960795 + 3404725 * 2 ^ 59
def prefixEnd_3404725 : Nat := 4983230072969 + 3 ^ 40 * 3404725 * 2
def baseEnd_3404725 : Nat := 388502315862065940328769

theorem tailTrace_3404725 : CollatzResearch.WordTrace tailWord_3404725 prefixEnd_3404725 388502315862065940328769 := by
  unfold tailWord_3404725
  simp only [CollatzResearch.WordTrace]
  refine ⟨124180522590270280581063629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82787015060180187054042419 124180522590270280581063629)
  ·
    refine ⟨46567695971351355217898861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124180522590270280581063629 46567695971351355217898861)
    ·
      refine ⟨17462885989256758206712073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46567695971351355217898861 17462885989256758206712073)
      ·
        refine ⟨13097164491942568655034055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17462885989256758206712073 13097164491942568655034055)
        ·
          refine ⟨19645746737913852982551083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13097164491942568655034055 19645746737913852982551083)
          ·
            refine ⟨29468620106870779473826625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19645746737913852982551083 29468620106870779473826625)
            ·
              refine ⟨22101465080153084605369969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29468620106870779473826625 22101465080153084605369969)
              ·
                refine ⟨16576098810114813454027477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22101465080153084605369969 16576098810114813454027477)
                ·
                  refine ⟨388502315862065940328769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16576098810114813454027477 388502315862065940328769)
                  ·
                    rfl

theorem cell22_3404725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_3404725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404725 prefixEnd_3404725 := by exact prefixLift 3404725
  have htrace : WordTrace (prefixWord ++ tailWord_3404725) baseStart_3404725 baseEnd_3404725 := by
    simpa [prefixWord, tailWord_3404725, baseEnd_3404725] using wordTrace_append hprefix tailTrace_3404725
  have hstable : (prefixWord ++ tailWord_3404725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404725).length < 2 ^ (prefixWord ++ tailWord_3404725).sum := by decide
  have hdescent : baseEnd_3404725 < baseStart_3404725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404729 : List Nat := [1, 2, 1, 4, 2, 2, 1, 5, 1, 3]
def baseStart_3404729 : Nat := 118140960795 + 3404729 * 2 ^ 59
def prefixEnd_3404729 : Nat := 4983230072969 + 3 ^ 40 * 3404729 * 2
def baseEnd_3404729 : Nat := 1165508316867943143886295

theorem tailTrace_3404729 : CollatzResearch.WordTrace tailWord_3404729 prefixEnd_3404729 1165508316867943143886295 := by
  unfold tailWord_3404729
  simp only [CollatzResearch.WordTrace]
  refine ⟨124180668482255789264209241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82787112321503859509472827 124180668482255789264209241)
  ·
    refine ⟨93135501361691841948156931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124180668482255789264209241 93135501361691841948156931)
    ·
      refine ⟨139703252042537762922235397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93135501361691841948156931 139703252042537762922235397)
      ·
        refine ⟨26194359757975830547919137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139703252042537762922235397 26194359757975830547919137)
        ·
          refine ⟨19645769818481872910939353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26194359757975830547919137 19645769818481872910939353)
          ·
            refine ⟨14734327363861404683204515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19645769818481872910939353 14734327363861404683204515)
            ·
              refine ⟨22101491045792107024806773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14734327363861404683204515 22101491045792107024806773)
              ·
                refine ⟨2072014785543010033575635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22101491045792107024806773 2072014785543010033575635)
                ·
                  refine ⟨3108022178314515050363453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2072014785543010033575635 3108022178314515050363453)
                  ·
                    refine ⟨1165508316867943143886295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3108022178314515050363453 1165508316867943143886295)
                    ·
                      rfl

theorem cell22_3404729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 1, 3].length) (baseStart_3404729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404729 prefixEnd_3404729 := by exact prefixLift 3404729
  have htrace : WordTrace (prefixWord ++ tailWord_3404729) baseStart_3404729 baseEnd_3404729 := by
    simpa [prefixWord, tailWord_3404729, baseEnd_3404729] using wordTrace_append hprefix tailTrace_3404729
  have hstable : (prefixWord ++ tailWord_3404729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404729).length < 2 ^ (prefixWord ++ tailWord_3404729).sum := by decide
  have hdescent : baseEnd_3404729 < baseStart_3404729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404834 : List Nat := [3, 3, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_3404834 : Nat := 118140960795 + 3404834 * 2 ^ 59
def prefixEnd_3404834 : Nat := 4983230072969 + 3 ^ 40 * 3404834 * 2
def baseEnd_3404834 : Nat := 1165544260513757870010973

theorem tailTrace_3404834 : CollatzResearch.WordTrace tailWord_3404834 prefixEnd_3404834 1165544260513757870010973 := by
  unfold tailWord_3404834
  simp only [CollatzResearch.WordTrace]
  refine ⟨31046124536718848049195389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82789665431250261464521037 31046124536718848049195389)
  ·
    refine ⟨11642296701269568018448271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31046124536718848049195389 11642296701269568018448271)
    ·
      refine ⟨17463445051904352027672407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11642296701269568018448271 17463445051904352027672407)
      ·
        refine ⟨26195167577856528041508611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17463445051904352027672407 26195167577856528041508611)
        ·
          refine ⟨39292751366784792062262917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26195167577856528041508611 39292751366784792062262917)
          ·
            refine ⟨7367390881272148511674297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39292751366784792062262917 7367390881272148511674297)
            ·
              refine ⟨5525543160954111383755723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7367390881272148511674297 5525543160954111383755723)
              ·
                refine ⟨8288314741431167075633585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5525543160954111383755723 8288314741431167075633585)
                ·
                  refine ⟨6216236056073375306725189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8288314741431167075633585 6216236056073375306725189)
                  ·
                    refine ⟨1165544260513757870010973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6216236056073375306725189 1165544260513757870010973)
                    ·
                      rfl

theorem cell22_3404834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_3404834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404834 prefixEnd_3404834 := by exact prefixLift 3404834
  have htrace : WordTrace (prefixWord ++ tailWord_3404834) baseStart_3404834 baseEnd_3404834 := by
    simpa [prefixWord, tailWord_3404834, baseEnd_3404834] using wordTrace_append hprefix tailTrace_3404834
  have hstable : (prefixWord ++ tailWord_3404834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404834).length < 2 ^ (prefixWord ++ tailWord_3404834).sum := by decide
  have hdescent : baseEnd_3404834 < baseStart_3404834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404892 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 1, 7]
def baseStart_3404892 : Nat := 118140960795 + 3404892 * 2 ^ 59
def prefixEnd_3404892 : Nat := 4983230072969 + 3 ^ 40 * 3404892 * 2
def baseEnd_3404892 : Nat := 1165564115099065052060795

theorem tailTrace_3404892 : CollatzResearch.WordTrace tailWord_3404892 prefixEnd_3404892 1165564115099065052060795 := by
  unfold tailWord_3404892
  simp only [CollatzResearch.WordTrace]
  refine ⟨62093306790332634051196465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82791075720443512068261953 62093306790332634051196465)
  ·
    refine ⟨46569980092749475538397349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62093306790332634051196465 46569980092749475538397349)
    ·
      refine ⟨8731871267390526663449503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46569980092749475538397349 8731871267390526663449503)
      ·
        refine ⟨13097806901085789995174255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8731871267390526663449503 13097806901085789995174255)
        ·
          refine ⟨19646710351628684992761383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13097806901085789995174255 19646710351628684992761383)
          ·
            refine ⟨29470065527443027489142075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19646710351628684992761383 29470065527443027489142075)
            ·
              refine ⟨44205098291164541233713113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29470065527443027489142075 44205098291164541233713113)
              ·
                refine ⟨33153823718373405925284835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44205098291164541233713113 33153823718373405925284835)
                ·
                  refine ⟨49730735577560108887927253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33153823718373405925284835 49730735577560108887927253)
                  ·
                    refine ⟨1165564115099065052060795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49730735577560108887927253 1165564115099065052060795)
                    ·
                      rfl

theorem cell22_3404892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_3404892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404892 prefixEnd_3404892 := by exact prefixLift 3404892
  have htrace : WordTrace (prefixWord ++ tailWord_3404892) baseStart_3404892 baseEnd_3404892 := by
    simpa [prefixWord, tailWord_3404892, baseEnd_3404892] using wordTrace_append hprefix tailTrace_3404892
  have hstable : (prefixWord ++ tailWord_3404892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404892).length < 2 ^ (prefixWord ++ tailWord_3404892).sum := by decide
  have hdescent : baseEnd_3404892 < baseStart_3404892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404898 : List Nat := [3, 3, 2, 2, 1, 1, 1, 5, 1, 3]
def baseStart_3404898 : Nat := 118140960795 + 3404898 * 2 ^ 59
def prefixEnd_3404898 : Nat := 4983230072969 + 3 ^ 40 * 3404898 * 2
def baseEnd_3404898 : Nat := 1165566169021683036410777

theorem tailTrace_3404898 : CollatzResearch.WordTrace tailWord_3404898 prefixEnd_3404898 1165566169021683036410777 := by
  unfold tailWord_3404898
  simp only [CollatzResearch.WordTrace]
  refine ⟨31046708104660882781777837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82791221612429020751407565 31046708104660882781777837)
  ·
    refine ⟨11642515539247831043166689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31046708104660882781777837 11642515539247831043166689)
    ·
      refine ⟨8731886654435873282375017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11642515539247831043166689 8731886654435873282375017)
      ·
        refine ⟨6548914990826904961781263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8731886654435873282375017 6548914990826904961781263)
        ·
          refine ⟨9823372486240357442671895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6548914990826904961781263 9823372486240357442671895)
          ·
            refine ⟨14735058729360536164007843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9823372486240357442671895 14735058729360536164007843)
            ·
              refine ⟨22102588094040804246011765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14735058729360536164007843 22102588094040804246011765)
              ·
                refine ⟨2072117633816325398063603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22102588094040804246011765 2072117633816325398063603)
                ·
                  refine ⟨3108176450724488097095405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2072117633816325398063603 3108176450724488097095405)
                  ·
                    refine ⟨1165566169021683036410777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3108176450724488097095405 1165566169021683036410777)
                    ·
                      rfl

theorem cell22_3404898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_3404898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404898 prefixEnd_3404898 := by exact prefixLift 3404898
  have htrace : WordTrace (prefixWord ++ tailWord_3404898) baseStart_3404898 baseEnd_3404898 := by
    simpa [prefixWord, tailWord_3404898, baseEnd_3404898] using wordTrace_append hprefix tailTrace_3404898
  have hstable : (prefixWord ++ tailWord_3404898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404898).length < 2 ^ (prefixWord ++ tailWord_3404898).sum := by decide
  have hdescent : baseEnd_3404898 < baseStart_3404898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404956 : List Nat := [2, 2, 3, 2, 1, 2, 3, 3, 4]
def baseStart_3404956 : Nat := 118140960795 + 3404956 * 2 ^ 59
def prefixEnd_3404956 : Nat := 4983230072969 + 3 ^ 40 * 3404956 * 2
def baseEnd_3404956 : Nat := 388528674535663406153533

theorem tailTrace_3404956 : CollatzResearch.WordTrace tailWord_3404956 prefixEnd_3404956 388528674535663406153533 := by
  unfold tailWord_3404956
  simp only [CollatzResearch.WordTrace]
  refine ⟨62094473926216703516361361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82792631901622271355148481 62094473926216703516361361)
  ·
    refine ⟨46570855444662527637271021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62094473926216703516361361 46570855444662527637271021)
    ·
      refine ⟨17464070791748447863976633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46570855444662527637271021 17464070791748447863976633)
      ·
        refine ⟨13098053093811335897982475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17464070791748447863976633 13098053093811335897982475)
        ·
          refine ⟨19647079640717003846973713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13098053093811335897982475 19647079640717003846973713)
          ·
            refine ⟨14735309730537752885230285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19647079640717003846973713 14735309730537752885230285)
            ·
              refine ⟨5525741148951657331961357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14735309730537752885230285 5525741148951657331961357)
              ·
                refine ⟨2072152930856871499485509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5525741148951657331961357 2072152930856871499485509)
                ·
                  refine ⟨388528674535663406153533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2072152930856871499485509 388528674535663406153533)
                  ·
                    rfl

theorem cell22_3404956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 4].length) (baseStart_3404956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404956 prefixEnd_3404956 := by exact prefixLift 3404956
  have htrace : WordTrace (prefixWord ++ tailWord_3404956) baseStart_3404956 baseEnd_3404956 := by
    simpa [prefixWord, tailWord_3404956, baseEnd_3404956] using wordTrace_append hprefix tailTrace_3404956
  have hstable : (prefixWord ++ tailWord_3404956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404956).length < 2 ^ (prefixWord ++ tailWord_3404956).sum := by decide
  have hdescent : baseEnd_3404956 < baseStart_3404956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404973 : List Nat := [1, 5, 2, 1, 4, 1, 1, 1, 6]
def baseStart_3404973 : Nat := 118140960795 + 3404973 * 2 ^ 59
def prefixEnd_3404973 : Nat := 4983230072969 + 3 ^ 40 * 3404973 * 2
def baseEnd_3404973 : Nat := 388530614351469280261849

theorem tailTrace_3404973 : CollatzResearch.WordTrace tailWord_3404973 prefixEnd_3404973 388530614351469280261849 := by
  unfold tailWord_3404973
  simp only [CollatzResearch.WordTrace]
  refine ⟨124189567893371818936091573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82793045262247879290727715 124189567893371818936091573)
  ·
    refine ⟨11642771990003608025258585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124189567893371818936091573 11642771990003608025258585)
    ·
      refine ⟨8732078992502706018943939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11642771990003608025258585 8732078992502706018943939)
      ·
        refine ⟨13098118488754059028415909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8732078992502706018943939 13098118488754059028415909)
        ·
          refine ⟨2455897216641386067827983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13098118488754059028415909 2455897216641386067827983)
          ·
            refine ⟨3683845824962079101741975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2455897216641386067827983 3683845824962079101741975)
            ·
              refine ⟨5525768737443118652612963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3683845824962079101741975 5525768737443118652612963)
              ·
                refine ⟨8288653106164677978919445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5525768737443118652612963 8288653106164677978919445)
                ·
                  refine ⟨388530614351469280261849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8288653106164677978919445 388530614351469280261849)
                  ·
                    rfl

theorem cell22_3404973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_3404973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404973 prefixEnd_3404973 := by exact prefixLift 3404973
  have htrace : WordTrace (prefixWord ++ tailWord_3404973) baseStart_3404973 baseEnd_3404973 := by
    simpa [prefixWord, tailWord_3404973, baseEnd_3404973] using wordTrace_append hprefix tailTrace_3404973
  have hstable : (prefixWord ++ tailWord_3404973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404973).length < 2 ^ (prefixWord ++ tailWord_3404973).sum := by decide
  have hdescent : baseEnd_3404973 < baseStart_3404973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404988 : List Nat := [2, 2, 2, 3, 2, 1, 4, 1, 2, 3]
def baseStart_3404988 : Nat := 118140960795 + 3404988 * 2 ^ 59
def prefixEnd_3404988 : Nat := 4983230072969 + 3 ^ 40 * 3404988 * 2
def baseEnd_3404988 : Nat := 1165596977860952801660501

theorem tailTrace_3404988 : CollatzResearch.WordTrace tailWord_3404988 prefixEnd_3404988 1165596977860952801660501 := by
  unfold tailWord_3404988
  simp only [CollatzResearch.WordTrace]
  refine ⟨62095057494158738248943809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82793409992211650998591745 62095057494158738248943809)
  ·
    refine ⟨46571293120619053686707857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62095057494158738248943809 46571293120619053686707857)
    ·
      refine ⟨34928469840464290265030893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46571293120619053686707857 34928469840464290265030893)
      ·
        refine ⟨13098176190174108849386585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34928469840464290265030893 13098176190174108849386585)
        ·
          refine ⟨9823632142630581637039939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13098176190174108849386585 9823632142630581637039939)
          ·
            refine ⟨14735448213945872455559909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9823632142630581637039939 14735448213945872455559909)
            ·
              refine ⟨2762896540114851085417483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14735448213945872455559909 2762896540114851085417483)
              ·
                refine ⟨4144344810172276628126225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2762896540114851085417483 4144344810172276628126225)
                ·
                  refine ⟨3108258607629207471094669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4144344810172276628126225 3108258607629207471094669)
                  ·
                    refine ⟨1165596977860952801660501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3108258607629207471094669 1165596977860952801660501)
                    ·
                      rfl

theorem cell22_3404988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_3404988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404988 prefixEnd_3404988 := by exact prefixLift 3404988
  have htrace : WordTrace (prefixWord ++ tailWord_3404988) baseStart_3404988 baseEnd_3404988 := by
    simpa [prefixWord, tailWord_3404988, baseEnd_3404988] using wordTrace_append hprefix tailTrace_3404988
  have hstable : (prefixWord ++ tailWord_3404988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404988).length < 2 ^ (prefixWord ++ tailWord_3404988).sum := by decide
  have hdescent : baseEnd_3404988 < baseStart_3404988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404999 : List Nat := [1, 1, 4, 1, 1, 1, 1, 6, 3, 3]
def baseStart_3404999 : Nat := 118140960795 + 3404999 * 2 ^ 59
def prefixEnd_3404999 : Nat := 4983230072969 + 3 ^ 40 * 3404999 * 2
def baseEnd_3404999 : Nat := 1165600743385752439635467

theorem tailTrace_3404999 : CollatzResearch.WordTrace tailWord_3404999 prefixEnd_3404999 1165600743385752439635467 := by
  unfold tailWord_3404999
  simp only [CollatzResearch.WordTrace]
  refine ⟨124190516191277625376538051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82793677460851750251025367 124190516191277625376538051)
  ·
    refine ⟨186285774286916438064807077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124190516191277625376538051 186285774286916438064807077)
    ·
      refine ⟨34928582678796832137151327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186285774286916438064807077 34928582678796832137151327)
      ·
        refine ⟨52392874018195248205726991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34928582678796832137151327 52392874018195248205726991)
        ·
          refine ⟨78589311027292872308590487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52392874018195248205726991 78589311027292872308590487)
          ·
            refine ⟨117883966540939308462885731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78589311027292872308590487 117883966540939308462885731)
            ·
              refine ⟨176825949811408962694328597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117883966540939308462885731 176825949811408962694328597)
              ·
                refine ⟨8288716397409795126296653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 176825949811408962694328597 8288716397409795126296653)
                ·
                  refine ⟨3108268649028673172361245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8288716397409795126296653 3108268649028673172361245)
                  ·
                    refine ⟨1165600743385752439635467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3108268649028673172361245 1165600743385752439635467)
                    ·
                      rfl

theorem cell22_3404999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_3404999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3404999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3404999 prefixEnd_3404999 := by exact prefixLift 3404999
  have htrace : WordTrace (prefixWord ++ tailWord_3404999) baseStart_3404999 baseEnd_3404999 := by
    simpa [prefixWord, tailWord_3404999, baseEnd_3404999] using wordTrace_append hprefix tailTrace_3404999
  have hstable : (prefixWord ++ tailWord_3404999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404999).length < 2 ^ (prefixWord ++ tailWord_3404999).sum := by decide
  have hdescent : baseEnd_3404999 < baseStart_3404999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405059 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 3, 4]
def baseStart_3405059 : Nat := 118140960795 + 3405059 * 2 ^ 59
def prefixEnd_3405059 : Nat := 4983230072969 + 3 ^ 40 * 3405059 * 2
def baseEnd_3405059 : Nat := 1165621282611932283135283

theorem tailTrace_3405059 : CollatzResearch.WordTrace tailWord_3405059 prefixEnd_3405059 1165621282611932283135283 := by
  unfold tailWord_3405059
  simp only [CollatzResearch.WordTrace]
  refine ⟨124192704571060255623722231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82795136380706837082481487 124192704571060255623722231)
  ·
    refine ⟨186289056856590383435583347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124192704571060255623722231 186289056856590383435583347)
    ·
      refine ⟨279433585284885575153375021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186289056856590383435583347 279433585284885575153375021)
      ·
        refine ⟨104787594481832090682515633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279433585284885575153375021 104787594481832090682515633)
        ·
          refine ⟨78590695861374068011886725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104787594481832090682515633 78590695861374068011886725)
          ·
            refine ⟨14735755474007637752228761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78590695861374068011886725 14735755474007637752228761)
            ·
              refine ⟨11051816605505728314171571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14735755474007637752228761 11051816605505728314171571)
              ·
                refine ⟨16577724908258592471257357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11051816605505728314171571 16577724908258592471257357)
                ·
                  refine ⟨6216646840596972176721509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16577724908258592471257357 6216646840596972176721509)
                  ·
                    refine ⟨1165621282611932283135283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6216646840596972176721509 1165621282611932283135283)
                    ·
                      rfl

theorem cell22_3405059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 4].length) (baseStart_3405059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3405059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3405059 prefixEnd_3405059 := by exact prefixLift 3405059
  have htrace : WordTrace (prefixWord ++ tailWord_3405059) baseStart_3405059 baseEnd_3405059 := by
    simpa [prefixWord, tailWord_3405059, baseEnd_3405059] using wordTrace_append hprefix tailTrace_3405059
  have hstable : (prefixWord ++ tailWord_3405059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405059).length < 2 ^ (prefixWord ++ tailWord_3405059).sum := by decide
  have hdescent : baseEnd_3405059 < baseStart_3405059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405072 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 4, 9]
def baseStart_3405072 : Nat := 118140960795 + 3405072 * 2 ^ 59
def prefixEnd_3405072 : Nat := 4983230072969 + 3 ^ 40 * 3405072 * 2
def baseEnd_3405072 : Nat := 1165625732777604582560243

theorem tailTrace_3405072 : CollatzResearch.WordTrace tailWord_3405072 prefixEnd_3405072 1165625732777604582560243 := by
  unfold tailWord_3405072
  simp only [CollatzResearch.WordTrace]
  refine ⟨62096589360006579421972735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82795452480008772562630313 62096589360006579421972735)
  ·
    refine ⟨93144884040009869132959103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62096589360006579421972735 93144884040009869132959103)
    ·
      refine ⟨139717326060014803699438655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93144884040009869132959103 139717326060014803699438655)
      ·
        refine ⟨209575989090022205549157983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139717326060014803699438655 209575989090022205549157983)
        ·
          refine ⟨314363983635033308323736975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209575989090022205549157983 314363983635033308323736975)
          ·
            refine ⟨471545975452549962485605463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314363983635033308323736975 471545975452549962485605463)
            ·
              refine ⟨707318963178824943728408195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471545975452549962485605463 707318963178824943728408195)
              ·
                refine ⟨1060978444768237415592612293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 707318963178824943728408195 1060978444768237415592612293)
                ·
                  refine ⟨198933458394044515423614805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1060978444768237415592612293 198933458394044515423614805)
                  ·
                    refine ⟨1165625732777604582560243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 198933458394044515423614805 1165625732777604582560243)
                    ·
                      rfl

theorem cell22_3405072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_3405072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3405072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3405072 prefixEnd_3405072 := by exact prefixLift 3405072
  have htrace : WordTrace (prefixWord ++ tailWord_3405072) baseStart_3405072 baseEnd_3405072 := by
    simpa [prefixWord, tailWord_3405072, baseEnd_3405072] using wordTrace_append hprefix tailTrace_3405072
  have hstable : (prefixWord ++ tailWord_3405072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405072).length < 2 ^ (prefixWord ++ tailWord_3405072).sum := by decide
  have hdescent : baseEnd_3405072 < baseStart_3405072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405091 : List Nat := [1, 1, 1, 4, 2, 3, 2, 4, 4]
def baseStart_3405091 : Nat := 118140960795 + 3405091 * 2 ^ 59
def prefixEnd_3405091 : Nat := 4983230072969 + 3 ^ 40 * 3405091 * 2
def baseEnd_3405091 : Nat := 388544078955298288778395

theorem tailTrace_3405091 : CollatzResearch.WordTrace tailWord_3405091 prefixEnd_3405091 388544078955298288778395 := by
  unfold tailWord_3405091
  simp only [CollatzResearch.WordTrace]
  refine ⟨124193871706944325088887127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82795914471296216725924751 124193871706944325088887127)
  ·
    refine ⟨186290807560416487633330691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124193871706944325088887127 186290807560416487633330691)
    ·
      refine ⟨279436211340624731449996037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186290807560416487633330691 279436211340624731449996037)
      ·
        refine ⟨52394289626367137146874257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279436211340624731449996037 52394289626367137146874257)
        ·
          refine ⟨39295717219775352860155693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52394289626367137146874257 39295717219775352860155693)
          ·
            refine ⟨14735893957415757322558385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39295717219775352860155693 14735893957415757322558385)
            ·
              refine ⟨11051920468061817991918789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14735893957415757322558385 11051920468061817991918789)
              ·
                refine ⟨2072235087761590873484773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11051920468061817991918789 2072235087761590873484773)
                ·
                  refine ⟨388544078955298288778395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2072235087761590873484773 388544078955298288778395)
                  ·
                    rfl

theorem cell22_3405091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 4].length) (baseStart_3405091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3405091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3405091 prefixEnd_3405091 := by exact prefixLift 3405091
  have htrace : WordTrace (prefixWord ++ tailWord_3405091) baseStart_3405091 baseEnd_3405091 := by
    simpa [prefixWord, tailWord_3405091, baseEnd_3405091] using wordTrace_append hprefix tailTrace_3405091
  have hstable : (prefixWord ++ tailWord_3405091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405091).length < 2 ^ (prefixWord ++ tailWord_3405091).sum := by decide
  have hdescent : baseEnd_3405091 < baseStart_3405091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405106 : List Nat := [3, 2, 1, 1, 4, 1, 3, 1, 1, 5]
def baseStart_3405106 : Nat := 118140960795 + 3405106 * 2 ^ 59
def prefixEnd_3405106 : Nat := 4983230072969 + 3 ^ 40 * 3405106 * 2
def baseEnd_3405106 : Nat := 1165637371672439827210139

theorem tailTrace_3405106 : CollatzResearch.WordTrace tailWord_3405106 prefixEnd_3405106 1165637371672439827210139 := by
  unfold tailWord_3405106
  simp only [CollatzResearch.WordTrace]
  refine ⟨31048604700472495662670793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82796279201259988433788781 31048604700472495662670793)
  ·
    refine ⟨23286453525354371747003095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31048604700472495662670793 23286453525354371747003095)
    ·
      refine ⟨34929680288031557620504643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23286453525354371747003095 34929680288031557620504643)
      ·
        refine ⟨52394520432047336430756965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34929680288031557620504643 52394520432047336430756965)
        ·
          refine ⟨9823972581008875580766931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52394520432047336430756965 9823972581008875580766931)
          ·
            refine ⟨14735958871513313371150397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9823972581008875580766931 14735958871513313371150397)
            ·
              refine ⟨5525984576817492514181399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14735958871513313371150397 5525984576817492514181399)
              ·
                refine ⟨8288976865226238771272099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5525984576817492514181399 8288976865226238771272099)
                ·
                  refine ⟨12433465297839358156908149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8288976865226238771272099 12433465297839358156908149)
                  ·
                    refine ⟨1165637371672439827210139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12433465297839358156908149 1165637371672439827210139)
                    ·
                      rfl

theorem cell22_3405106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_3405106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3405106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3405106 prefixEnd_3405106 := by exact prefixLift 3405106
  have htrace : WordTrace (prefixWord ++ tailWord_3405106) baseStart_3405106 baseEnd_3405106 := by
    simpa [prefixWord, tailWord_3405106, baseEnd_3405106] using wordTrace_append hprefix tailTrace_3405106
  have hstable : (prefixWord ++ tailWord_3405106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405106).length < 2 ^ (prefixWord ++ tailWord_3405106).sum := by decide
  have hdescent : baseEnd_3405106 < baseStart_3405106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405119 : List Nat := [1, 1, 2, 2, 4, 3, 1, 8]
def baseStart_3405119 : Nat := 118140960795 + 3405119 * 2 ^ 59
def prefixEnd_3405119 : Nat := 4983230072969 + 3 ^ 40 * 3405119 * 2
def baseEnd_3405119 : Nat := 129515757982012458515011

theorem tailTrace_3405119 : CollatzResearch.WordTrace tailWord_3405119 prefixEnd_3405119 129515757982012458515011 := by
  unfold tailWord_3405119
  simp only [CollatzResearch.WordTrace]
  refine ⟨124194892950842885870906411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82796595300561923913937607 124194892950842885870906411)
  ·
    refine ⟨186292339426264328806359617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124194892950842885870906411 186292339426264328806359617)
    ·
      refine ⟨139719254569698246604769713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186292339426264328806359617 139719254569698246604769713)
      ·
        refine ⟨104789440927273684953577285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139719254569698246604769713 104789440927273684953577285)
        ·
          refine ⟨19648020173863815928795741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104789440927273684953577285 19648020173863815928795741)
          ·
            refine ⟨7368007565198930973298403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19648020173863815928795741 7368007565198930973298403)
            ·
              refine ⟨11052011347798396459947605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7368007565198930973298403 11052011347798396459947605)
              ·
                refine ⟨129515757982012458515011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11052011347798396459947605 129515757982012458515011)
                ·
                  rfl

theorem cell22_3405119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 8].length) (baseStart_3405119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3405119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3405119 prefixEnd_3405119 := by exact prefixLift 3405119
  have htrace : WordTrace (prefixWord ++ tailWord_3405119) baseStart_3405119 baseEnd_3405119 := by
    simpa [prefixWord, tailWord_3405119, baseEnd_3405119] using wordTrace_append hprefix tailTrace_3405119
  have hstable : (prefixWord ++ tailWord_3405119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405119).length < 2 ^ (prefixWord ++ tailWord_3405119).sum := by decide
  have hdescent : baseEnd_3405119 < baseStart_3405119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405121 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 1, 6]
def baseStart_3405121 : Nat := 118140960795 + 3405121 * 2 ^ 59
def prefixEnd_3405121 : Nat := 4983230072969 + 3 ^ 40 * 3405121 * 2
def baseEnd_3405121 : Nat := 1165642506478984788085093

theorem tailTrace_3405121 : CollatzResearch.WordTrace tailWord_3405121 prefixEnd_3405121 1165642506478984788085093 := by
  unfold tailWord_3405121
  simp only [CollatzResearch.WordTrace]
  refine ⟨124194965896835640212479217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82796643931223760141652811 124194965896835640212479217)
  ·
    refine ⟨93146224422626730159359413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124194965896835640212479217 93146224422626730159359413)
    ·
      refine ⟨8732458539621255952439945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93146224422626730159359413 8732458539621255952439945)
      ·
        refine ⟨6549343904715941964329959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8732458539621255952439945 6549343904715941964329959)
        ·
          refine ⟨9824015857073912946494939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6549343904715941964329959 9824015857073912946494939)
          ·
            refine ⟨14736023785610869419742409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9824015857073912946494939 14736023785610869419742409)
            ·
              refine ⟨11052017839208152064806807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14736023785610869419742409 11052017839208152064806807)
              ·
                refine ⟨16578026758812228097210211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11052017839208152064806807 16578026758812228097210211)
                ·
                  refine ⟨24867040138218342145815317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16578026758812228097210211 24867040138218342145815317)
                  ·
                    refine ⟨1165642506478984788085093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24867040138218342145815317 1165642506478984788085093)
                    ·
                      rfl

theorem cell22_3405121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_3405121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3405121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3405121 prefixEnd_3405121 := by exact prefixLift 3405121
  have htrace : WordTrace (prefixWord ++ tailWord_3405121) baseStart_3405121 baseEnd_3405121 := by
    simpa [prefixWord, tailWord_3405121, baseEnd_3405121] using wordTrace_append hprefix tailTrace_3405121
  have hstable : (prefixWord ++ tailWord_3405121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405121).length < 2 ^ (prefixWord ++ tailWord_3405121).sum := by decide
  have hdescent : baseEnd_3405121 < baseStart_3405121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405256 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 4, 4]
def baseStart_3405256 : Nat := 118140960795 + 3405256 * 2 ^ 59
def prefixEnd_3405256 : Nat := 4983230072969 + 3 ^ 40 * 3405256 * 2
def baseEnd_3405256 : Nat := 1165688719737889435959679

theorem tailTrace_3405256 : CollatzResearch.WordTrace tailWord_3405256 prefixEnd_3405256 1165688719737889435959679 := by
  unfold tailWord_3405256
  simp only [CollatzResearch.WordTrace]
  refine ⟨62099944875673279134321811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82799926500897705512429081 62099944875673279134321811)
  ·
    refine ⟨93149917313509918701482717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62099944875673279134321811 93149917313509918701482717)
    ·
      refine ⟨34931218992566219513056019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93149917313509918701482717 34931218992566219513056019)
      ·
        refine ⟨52396828488849329269584029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34931218992566219513056019 52396828488849329269584029)
        ·
          refine ⟨19648810683318498476094011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52396828488849329269584029 19648810683318498476094011)
          ·
            refine ⟨29473216024977747714141017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19648810683318498476094011 29473216024977747714141017)
            ·
              refine ⟨22104912018733310785605763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29473216024977747714141017 22104912018733310785605763)
              ·
                refine ⟨33157368028099966178408645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22104912018733310785605763 33157368028099966178408645)
                ·
                  refine ⟨6217006505268743658451621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33157368028099966178408645 6217006505268743658451621)
                  ·
                    refine ⟨1165688719737889435959679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6217006505268743658451621 1165688719737889435959679)
                    ·
                      rfl

theorem cell22_3405256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_3405256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3405256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3405256 prefixEnd_3405256 := by exact prefixLift 3405256
  have htrace : WordTrace (prefixWord ++ tailWord_3405256) baseStart_3405256 baseEnd_3405256 := by
    simpa [prefixWord, tailWord_3405256, baseEnd_3405256] using wordTrace_append hprefix tailTrace_3405256
  have hstable : (prefixWord ++ tailWord_3405256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405256).length < 2 ^ (prefixWord ++ tailWord_3405256).sum := by decide
  have hdescent : baseEnd_3405256 < baseStart_3405256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405258 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 4, 3]
def baseStart_3405258 : Nat := 118140960795 + 3405258 * 2 ^ 59
def prefixEnd_3405258 : Nat := 4983230072969 + 3 ^ 40 * 3405258 * 2
def baseEnd_3405258 : Nat := 1165689404378762097409673

theorem tailTrace_3405258 : CollatzResearch.WordTrace tailWord_3405258 prefixEnd_3405258 1165689404378762097409673 := by
  unfold tailWord_3405258
  simp only [CollatzResearch.WordTrace]
  refine ⟨31049990674334828152554107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82799975131559541740144285 31049990674334828152554107)
  ·
    refine ⟨46574986011502242228831161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31049990674334828152554107 46574986011502242228831161)
    ·
      refine ⟨34931239508626681671623371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46574986011502242228831161 34931239508626681671623371)
      ·
        refine ⟨52396859262940022507435057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34931239508626681671623371 52396859262940022507435057)
        ·
          refine ⟨39297644447205016880576293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52396859262940022507435057 39297644447205016880576293)
          ·
            refine ⟨7368308333850940665108055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39297644447205016880576293 7368308333850940665108055)
            ·
              refine ⟨11052462500776410997662083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7368308333850940665108055 11052462500776410997662083)
              ·
                refine ⟨16578693751164616496493125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11052462500776410997662083 16578693751164616496493125)
                ·
                  refine ⟨3108505078343365593092461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16578693751164616496493125 3108505078343365593092461)
                  ·
                    refine ⟨1165689404378762097409673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3108505078343365593092461 1165689404378762097409673)
                    ·
                      rfl

theorem cell22_3405258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_3405258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3405258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3405258 prefixEnd_3405258 := by exact prefixLift 3405258
  have htrace : WordTrace (prefixWord ++ tailWord_3405258) baseStart_3405258 baseEnd_3405258 := by
    simpa [prefixWord, tailWord_3405258, baseEnd_3405258] using wordTrace_append hprefix tailTrace_3405258
  have hstable : (prefixWord ++ tailWord_3405258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405258).length < 2 ^ (prefixWord ++ tailWord_3405258).sum := by decide
  have hdescent : baseEnd_3405258 < baseStart_3405258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405320 : List Nat := [2, 1, 3, 2, 1, 1, 2, 6, 1, 3]
def baseStart_3405320 : Nat := 118140960795 + 3405320 * 2 ^ 59
def prefixEnd_3405320 : Nat := 4983230072969 + 3 ^ 40 * 3405320 * 2
def baseEnd_3405320 : Nat := 1165710628245814602359483

theorem tailTrace_3405320 : CollatzResearch.WordTrace tailWord_3405320 prefixEnd_3405320 1165710628245814602359483 := by
  unfold tailWord_3405320
  simp only [CollatzResearch.WordTrace]
  refine ⟨62101112011557348599486707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82801482682076464799315609 62101112011557348599486707)
  ·
    refine ⟨93151668017336022899230061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62101112011557348599486707 93151668017336022899230061)
    ·
      refine ⟨34931875506501008587211273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93151668017336022899230061 34931875506501008587211273)
      ·
        refine ⟨26198906629875756440408455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34931875506501008587211273 26198906629875756440408455)
        ·
          refine ⟨39298359944813634660612683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26198906629875756440408455 39298359944813634660612683)
          ·
            refine ⟨58947539917220451990919025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39298359944813634660612683 58947539917220451990919025)
            ·
              refine ⟨44210654937915338993189269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58947539917220451990919025 44210654937915338993189269)
              ·
                refine ⟨2072374450214781515305747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44210654937915338993189269 2072374450214781515305747)
                ·
                  refine ⟨3108561675322172272958621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2072374450214781515305747 3108561675322172272958621)
                  ·
                    refine ⟨1165710628245814602359483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3108561675322172272958621 1165710628245814602359483)
                    ·
                      rfl

theorem cell22_3405320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_3405320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3405320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3405320 prefixEnd_3405320 := by exact prefixLift 3405320
  have htrace : WordTrace (prefixWord ++ tailWord_3405320) baseStart_3405320 baseEnd_3405320 := by
    simpa [prefixWord, tailWord_3405320, baseEnd_3405320] using wordTrace_append hprefix tailTrace_3405320
  have hstable : (prefixWord ++ tailWord_3405320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405320).length < 2 ^ (prefixWord ++ tailWord_3405320).sum := by decide
  have hdescent : baseEnd_3405320 < baseStart_3405320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405333 : List Nat := [1, 3, 2, 1, 3, 3, 1, 3, 5]
def baseStart_3405333 : Nat := 118140960795 + 3405333 * 2 ^ 59
def prefixEnd_3405333 : Nat := 4983230072969 + 3 ^ 40 * 3405333 * 2
def baseEnd_3405333 : Nat := 388571692803828967261481

theorem tailTrace_3405333 : CollatzResearch.WordTrace tailWord_3405333 prefixEnd_3405333 388571692803828967261481 := by
  unfold tailWord_3405333
  simp only [CollatzResearch.WordTrace]
  refine ⟨124202698172067600419196653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82801798781378400279464435 124202698172067600419196653)
  ·
    refine ⟨46576011814525350157198745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124202698172067600419196653 46576011814525350157198745)
    ·
      refine ⟨34932008860894012617899059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46576011814525350157198745 34932008860894012617899059)
      ·
        refine ⟨52398013291341018926848589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34932008860894012617899059 52398013291341018926848589)
        ·
          refine ⟨19649254984252882097568221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52398013291341018926848589 19649254984252882097568221)
          ·
            refine ⟨7368470619094830786588083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19649254984252882097568221 7368470619094830786588083)
            ·
              refine ⟨11052705928642246179882125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7368470619094830786588083 11052705928642246179882125)
              ·
                refine ⟨4144764723240842317455797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11052705928642246179882125 4144764723240842317455797)
                ·
                  refine ⟨388571692803828967261481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4144764723240842317455797 388571692803828967261481)
                  ·
                    rfl

theorem cell22_3405333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_3405333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3405333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3405333 prefixEnd_3405333 := by exact prefixLift 3405333
  have htrace : WordTrace (prefixWord ++ tailWord_3405333) baseStart_3405333 baseEnd_3405333 := by
    simpa [prefixWord, tailWord_3405333, baseEnd_3405333] using wordTrace_append hprefix tailTrace_3405333
  have hstable : (prefixWord ++ tailWord_3405333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405333).length < 2 ^ (prefixWord ++ tailWord_3405333).sum := by decide
  have hdescent : baseEnd_3405333 < baseStart_3405333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405376 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 5, 5]
def baseStart_3405376 : Nat := 118140960795 + 3405376 * 2 ^ 59
def prefixEnd_3405376 : Nat := 4983230072969 + 3 ^ 40 * 3405376 * 2
def baseEnd_3405376 : Nat := 1165729798190249122959311

theorem tailTrace_3405376 : CollatzResearch.WordTrace tailWord_3405376 prefixEnd_3405376 1165729798190249122959311 := by
  unfold tailWord_3405376
  simp only [CollatzResearch.WordTrace]
  refine ⟨62102133255455909381505991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82802844340607879175341321 62102133255455909381505991)
  ·
    refine ⟨93153199883183864072258987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62102133255455909381505991 93153199883183864072258987)
    ·
      refine ⟨139729799824775796108388481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93153199883183864072258987 139729799824775796108388481)
      ·
        refine ⟨104797349868581847081291361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139729799824775796108388481 104797349868581847081291361)
        ·
          refine ⟨78598012401436385310968521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104797349868581847081291361 78598012401436385310968521)
          ·
            refine ⟨58948509301077288983226391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78598012401436385310968521 58948509301077288983226391)
            ·
              refine ⟨88422763951615933474839587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58948509301077288983226391 88422763951615933474839587)
              ·
                refine ⟨132634145927423900212259381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88422763951615933474839587 132634145927423900212259381)
                ·
                  refine ⟨12434451180695990644899317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132634145927423900212259381 12434451180695990644899317)
                  ·
                    refine ⟨1165729798190249122959311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12434451180695990644899317 1165729798190249122959311)
                    ·
                      rfl

theorem cell22_3405376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_3405376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3405376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3405376 prefixEnd_3405376 := by exact prefixLift 3405376
  have htrace : WordTrace (prefixWord ++ tailWord_3405376) baseStart_3405376 baseEnd_3405376 := by
    simpa [prefixWord, tailWord_3405376, baseEnd_3405376] using wordTrace_append hprefix tailTrace_3405376
  have hstable : (prefixWord ++ tailWord_3405376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405376).length < 2 ^ (prefixWord ++ tailWord_3405376).sum := by decide
  have hdescent : baseEnd_3405376 < baseStart_3405376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405382 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_3405382 : Nat := 118140960795 + 3405382 * 2 ^ 59
def prefixEnd_3405382 : Nat := 4983230072969 + 3 ^ 40 * 3405382 * 2
def baseEnd_3405382 : Nat := 1165731852112867107309293

theorem tailTrace_3405382 : CollatzResearch.WordTrace tailWord_3405382 prefixEnd_3405382 1165731852112867107309293 := by
  unfold tailWord_3405382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3881390167152815055866575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82802990232593387858486933 3881390167152815055866575)
  ·
    refine ⟨5822085250729222583799863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3881390167152815055866575 5822085250729222583799863)
    ·
      refine ⟨8733127876093833875699795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5822085250729222583799863 8733127876093833875699795)
      ·
        refine ⟨13099691814140750813549693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8733127876093833875699795 13099691814140750813549693)
        ·
          refine ⟨4912384430302781555081135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13099691814140750813549693 4912384430302781555081135)
          ·
            refine ⟨7368576645454172332621703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4912384430302781555081135 7368576645454172332621703)
            ·
              refine ⟨11052864968181258498932555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7368576645454172332621703 11052864968181258498932555)
              ·
                refine ⟨16579297452271887748398833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11052864968181258498932555 16579297452271887748398833)
                ·
                  refine ⟨12434473089203915811299125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16579297452271887748398833 12434473089203915811299125)
                  ·
                    refine ⟨1165731852112867107309293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12434473089203915811299125 1165731852112867107309293)
                    ·
                      rfl

theorem cell22_3405382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_3405382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3405382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3405382 prefixEnd_3405382 := by exact prefixLift 3405382
  have htrace : WordTrace (prefixWord ++ tailWord_3405382) baseStart_3405382 baseEnd_3405382 := by
    simpa [prefixWord, tailWord_3405382, baseEnd_3405382] using wordTrace_append hprefix tailTrace_3405382
  have hstable : (prefixWord ++ tailWord_3405382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405382).length < 2 ^ (prefixWord ++ tailWord_3405382).sum := by decide
  have hdescent : baseEnd_3405382 < baseStart_3405382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405391 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 1, 6]
def baseStart_3405391 : Nat := 118140960795 + 3405391 * 2 ^ 59
def prefixEnd_3405391 : Nat := 4983230072969 + 3 ^ 40 * 3405391 * 2
def baseEnd_3405391 : Nat := 1165734932996794083834265

theorem tailTrace_3405391 : CollatzResearch.WordTrace tailWord_3405391 prefixEnd_3405391 1165734932996794083834265 := by
  unfold tailWord_3405391
  simp only [CollatzResearch.WordTrace]
  refine ⟨124204813605857476324808027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82803209070571650883205351 124204813605857476324808027)
  ·
    refine ⟨186307220408786214487212041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124204813605857476324808027 186307220408786214487212041)
    ·
      refine ⟨139730415306589660865409031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186307220408786214487212041 139730415306589660865409031)
      ·
        refine ⟨209595622959884491298113547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139730415306589660865409031 209595622959884491298113547)
        ·
          refine ⟨314393434439826736947170321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209595622959884491298113547 314393434439826736947170321)
          ·
            refine ⟨235795075829870052710377741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314393434439826736947170321 235795075829870052710377741)
            ·
              refine ⟨88423153436201269766391653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235795075829870052710377741 88423153436201269766391653)
              ·
                refine ⟨16579341269287738081198435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88423153436201269766391653 16579341269287738081198435)
                ·
                  refine ⟨24869011903931607121797653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16579341269287738081198435 24869011903931607121797653)
                  ·
                    refine ⟨1165734932996794083834265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24869011903931607121797653 1165734932996794083834265)
                    ·
                      rfl

theorem cell22_3405391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_3405391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3405391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3405391 prefixEnd_3405391 := by exact prefixLift 3405391
  have htrace : WordTrace (prefixWord ++ tailWord_3405391) baseStart_3405391 baseEnd_3405391 := by
    simpa [prefixWord, tailWord_3405391, baseEnd_3405391] using wordTrace_append hprefix tailTrace_3405391
  have hstable : (prefixWord ++ tailWord_3405391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405391).length < 2 ^ (prefixWord ++ tailWord_3405391).sum := by decide
  have hdescent : baseEnd_3405391 < baseStart_3405391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405393 : List Nat := [1, 2, 2, 1, 3, 2, 4, 1, 1, 5]
def baseStart_3405393 : Nat := 118140960795 + 3405393 * 2 ^ 59
def prefixEnd_3405393 : Nat := 4983230072969 + 3 ^ 40 * 3405393 * 2
def baseEnd_3405393 : Nat := 1165735617637666745284259

theorem tailTrace_3405393 : CollatzResearch.WordTrace tailWord_3405393 prefixEnd_3405393 1165735617637666745284259 := by
  unfold tailWord_3405393
  simp only [CollatzResearch.WordTrace]
  refine ⟨124204886551850230666380833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82803257701233487110920555 124204886551850230666380833)
  ·
    refine ⟨93153664913887672999785625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124204886551850230666380833 93153664913887672999785625)
    ·
      refine ⟨69865248685415754749839219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93153664913887672999785625 69865248685415754749839219)
      ·
        refine ⟨104797873028123632124758829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69865248685415754749839219 104797873028123632124758829)
        ·
          refine ⟨39299202385546362046784561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104797873028123632124758829 39299202385546362046784561)
          ·
            refine ⟨29474401789159771535088421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39299202385546362046784561 29474401789159771535088421)
            ·
              refine ⟨5526450335467457162829079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29474401789159771535088421 5526450335467457162829079)
              ·
                refine ⟨8289675503201185744243619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5526450335467457162829079 8289675503201185744243619)
                ·
                  refine ⟨12434513254801778616365429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8289675503201185744243619 12434513254801778616365429)
                  ·
                    refine ⟨1165735617637666745284259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12434513254801778616365429 1165735617637666745284259)
                    ·
                      rfl

theorem cell22_3405393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_3405393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3405393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3405393 prefixEnd_3405393 := by exact prefixLift 3405393
  have htrace : WordTrace (prefixWord ++ tailWord_3405393) baseStart_3405393 baseEnd_3405393 := by
    simpa [prefixWord, tailWord_3405393, baseEnd_3405393] using wordTrace_append hprefix tailTrace_3405393
  have hstable : (prefixWord ++ tailWord_3405393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405393).length < 2 ^ (prefixWord ++ tailWord_3405393).sum := by decide
  have hdescent : baseEnd_3405393 < baseStart_3405393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405444 : List Nat := [2, 3, 2, 1, 4, 1, 3, 1, 2, 3]
def baseStart_3405444 : Nat := 118140960795 + 3405444 * 2 ^ 59
def prefixEnd_3405444 : Nat := 4983230072969 + 3 ^ 40 * 3405444 * 2
def baseEnd_3405444 : Nat := 1165753075979919612259103

theorem tailTrace_3405444 : CollatzResearch.WordTrace tailWord_3405444 prefixEnd_3405444 1165753075979919612259103 := by
  unfold tailWord_3405444
  simp only [CollatzResearch.WordTrace]
  refine ⟨62103373337332733188243693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82804497783110310917658257 62103373337332733188243693)
  ·
    refine ⟨23288765001499774945591385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62103373337332733188243693 23288765001499774945591385)
    ·
      refine ⟨17466573751124831209193539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23288765001499774945591385 17466573751124831209193539)
      ·
        refine ⟨26199860626687246813790309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17466573751124831209193539 26199860626687246813790309)
        ·
          refine ⟨4912473867503858777585683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26199860626687246813790309 4912473867503858777585683)
          ·
            refine ⟨7368710801255788166378525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4912473867503858777585683 7368710801255788166378525)
            ·
              refine ⟨2763266550470920562391947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7368710801255788166378525 2763266550470920562391947)
              ·
                refine ⟨4144899825706380843587921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2763266550470920562391947 4144899825706380843587921)
                ·
                  refine ⟨3108674869279785632690941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4144899825706380843587921 3108674869279785632690941)
                  ·
                    refine ⟨1165753075979919612259103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3108674869279785632690941 1165753075979919612259103)
                    ·
                      rfl

theorem cell22_3405444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_3405444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3405444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3405444 prefixEnd_3405444 := by exact prefixLift 3405444
  have htrace : WordTrace (prefixWord ++ tailWord_3405444) baseStart_3405444 baseEnd_3405444 := by
    simpa [prefixWord, tailWord_3405444, baseEnd_3405444] using wordTrace_append hprefix tailTrace_3405444
  have hstable : (prefixWord ++ tailWord_3405444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405444).length < 2 ^ (prefixWord ++ tailWord_3405444).sum := by decide
  have hdescent : baseEnd_3405444 < baseStart_3405444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405485 : List Nat := [1, 5, 2, 1, 1, 1, 2, 4, 5]
def baseStart_3405485 : Nat := 118140960795 + 3405485 * 2 ^ 59
def prefixEnd_3405485 : Nat := 4983230072969 + 3 ^ 40 * 3405485 * 2
def baseEnd_3405485 : Nat := 388589037039269723994659

theorem tailTrace_3405485 : CollatzResearch.WordTrace tailWord_3405485 prefixEnd_3405485 388589037039269723994659 := by
  unfold tailWord_3405485
  simp only [CollatzResearch.WordTrace]
  refine ⟨124208242067516930378729909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82805494711677953585819939 124208242067516930378729909)
  ·
    refine ⟨11644522693829712223005929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124208242067516930378729909 11644522693829712223005929)
    ·
      refine ⟨8733392020372284167254447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11644522693829712223005929 8733392020372284167254447)
      ·
        refine ⟨13100088030558426250881671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8733392020372284167254447 13100088030558426250881671)
        ·
          refine ⟨19650132045837639376322507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13100088030558426250881671 19650132045837639376322507)
          ·
            refine ⟨29475198068756459064483761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19650132045837639376322507 29475198068756459064483761)
            ·
              refine ⟨22106398551567344298362821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29475198068756459064483761 22106398551567344298362821)
              ·
                refine ⟨4144949728418877055943029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22106398551567344298362821 4144949728418877055943029)
                ·
                  refine ⟨388589037039269723994659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4144949728418877055943029 388589037039269723994659)
                  ·
                    rfl

theorem cell22_3405485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_3405485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3405485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3405485 prefixEnd_3405485 := by exact prefixLift 3405485
  have htrace : WordTrace (prefixWord ++ tailWord_3405485) baseStart_3405485 baseEnd_3405485 := by
    simpa [prefixWord, tailWord_3405485, baseEnd_3405485] using wordTrace_append hprefix tailTrace_3405485
  have hstable : (prefixWord ++ tailWord_3405485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405485).length < 2 ^ (prefixWord ++ tailWord_3405485).sum := by decide
  have hdescent : baseEnd_3405485 < baseStart_3405485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405502 : List Nat := [4, 2, 1, 1, 2, 2, 4, 1, 5]
def baseStart_3405502 : Nat := 118140960795 + 3405502 * 2 ^ 59
def prefixEnd_3405502 : Nat := 4983230072969 + 3 ^ 40 * 3405502 * 2
def baseEnd_3405502 : Nat := 388590976855075598102975

theorem tailTrace_3405502 : CollatzResearch.WordTrace tailWord_3405502 prefixEnd_3405502 388590976855075598102975 := by
  unfold tailWord_3405502
  simp only [CollatzResearch.WordTrace]
  refine ⟨15526107763556917785262345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82805908072303561521399173 15526107763556917785262345)
  ·
    refine ⟨11644580822667688338946759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15526107763556917785262345 11644580822667688338946759)
    ·
      refine ⟨17466871234001532508420139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11644580822667688338946759 17466871234001532508420139)
      ·
        refine ⟨26200306851002298762630209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17466871234001532508420139 26200306851002298762630209)
        ·
          refine ⟨19650230138251724071972657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26200306851002298762630209 19650230138251724071972657)
          ·
            refine ⟨14737672603688793053979493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19650230138251724071972657 14737672603688793053979493)
            ·
              refine ⟨2763313613191648697621155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14737672603688793053979493 2763313613191648697621155)
              ·
                refine ⟨4144970419787473046431733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2763313613191648697621155 4144970419787473046431733)
                ·
                  refine ⟨388590976855075598102975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4144970419787473046431733 388590976855075598102975)
                  ·
                    rfl

theorem cell22_3405502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_3405502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3405502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3405502 prefixEnd_3405502 := by exact prefixLift 3405502
  have htrace : WordTrace (prefixWord ++ tailWord_3405502) baseStart_3405502 baseEnd_3405502 := by
    simpa [prefixWord, tailWord_3405502, baseEnd_3405502] using wordTrace_append hprefix tailTrace_3405502
  have hstable : (prefixWord ++ tailWord_3405502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405502).length < 2 ^ (prefixWord ++ tailWord_3405502).sum := by decide
  have hdescent : baseEnd_3405502 < baseStart_3405502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405547 : List Nat := [1, 1, 1, 1, 2, 4, 6, 2, 4]
def baseStart_3405547 : Nat := 118140960795 + 3405547 * 2 ^ 59
def prefixEnd_3405547 : Nat := 4983230072969 + 3 ^ 40 * 3405547 * 2
def baseEnd_3405547 : Nat := 388596111661620558977929

theorem tailTrace_3405547 : CollatzResearch.WordTrace tailWord_3405547 prefixEnd_3405547 388596111661620558977929 := by
  unfold tailWord_3405547
  simp only [CollatzResearch.WordTrace]
  refine ⟨124210503393292314967486895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82807002262194876644991263 124210503393292314967486895)
  ·
    refine ⟨186315755089938472451230343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124210503393292314967486895 186315755089938472451230343)
    ·
      refine ⟨279473632634907708676845515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186315755089938472451230343 279473632634907708676845515)
      ·
        refine ⟨419210448952361563015268273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279473632634907708676845515 419210448952361563015268273)
        ·
          refine ⟨314407836714271172261451205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419210448952361563015268273 314407836714271172261451205)
          ·
            refine ⟨58951469383925844799022101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 314407836714271172261451205 58951469383925844799022101)
            ·
              refine ⟨2763350127371523974954161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58951469383925844799022101 2763350127371523974954161)
              ·
                refine ⟨2072512595528642981215621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2763350127371523974954161 2072512595528642981215621)
                ·
                  refine ⟨388596111661620558977929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2072512595528642981215621 388596111661620558977929)
                  ·
                    rfl

theorem cell22_3405547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 4].length) (baseStart_3405547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3405547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3405547 prefixEnd_3405547 := by exact prefixLift 3405547
  have htrace : WordTrace (prefixWord ++ tailWord_3405547) baseStart_3405547 baseEnd_3405547 := by
    simpa [prefixWord, tailWord_3405547, baseEnd_3405547] using wordTrace_append hprefix tailTrace_3405547
  have hstable : (prefixWord ++ tailWord_3405547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405547).length < 2 ^ (prefixWord ++ tailWord_3405547).sum := by decide
  have hdescent : baseEnd_3405547 < baseStart_3405547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405680 : List Nat := [2, 1, 1, 1, 4, 1, 1, 5, 1, 5]
def baseStart_3405680 : Nat := 118140960795 + 3405680 * 2 ^ 59
def prefixEnd_3405680 : Nat := 4983230072969 + 3 ^ 40 * 3405680 * 2
def baseEnd_3405680 : Nat := 1165833863602893663358379

theorem tailTrace_3405680 : CollatzResearch.WordTrace tailWord_3405680 prefixEnd_3405680 1165833863602893663358379 := by
  unfold tailWord_3405680
  simp only [CollatzResearch.WordTrace]
  refine ⟨62107677150905239341039247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82810236201206985788052329 62107677150905239341039247)
  ·
    refine ⟨93161515726357859011558871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62107677150905239341039247 93161515726357859011558871)
    ·
      refine ⟨139742273589536788517338307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93161515726357859011558871 139742273589536788517338307)
      ·
        refine ⟨209613410384305182776007461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139742273589536788517338307 209613410384305182776007461)
        ·
          refine ⟨39302514447057221770501399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209613410384305182776007461 39302514447057221770501399)
          ·
            refine ⟨58953771670585832655752099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39302514447057221770501399 58953771670585832655752099)
            ·
              refine ⟨88430657505878748983628149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58953771670585832655752099 88430657505878748983628149)
              ·
                refine ⟨8290374141176132717215139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88430657505878748983628149 8290374141176132717215139)
                ·
                  refine ⟨12435561211764199075822709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8290374141176132717215139 12435561211764199075822709)
                  ·
                    refine ⟨1165833863602893663358379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12435561211764199075822709 1165833863602893663358379)
                    ·
                      rfl

theorem cell22_3405680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 1, 5].length) (baseStart_3405680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3405680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3405680 prefixEnd_3405680 := by exact prefixLift 3405680
  have htrace : WordTrace (prefixWord ++ tailWord_3405680) baseStart_3405680 baseEnd_3405680 := by
    simpa [prefixWord, tailWord_3405680, baseEnd_3405680] using wordTrace_append hprefix tailTrace_3405680
  have hstable : (prefixWord ++ tailWord_3405680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405680).length < 2 ^ (prefixWord ++ tailWord_3405680).sum := by decide
  have hdescent : baseEnd_3405680 < baseStart_3405680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405716 : List Nat := [2, 4, 2, 1, 1, 2, 4, 2, 4]
def baseStart_3405716 : Nat := 118140960795 + 3405716 * 2 ^ 59
def prefixEnd_3405716 : Nat := 4983230072969 + 3 ^ 40 * 3405716 * 2
def baseEnd_3405716 : Nat := 388615395712867189819423

theorem tailTrace_3405716 : CollatzResearch.WordTrace tailWord_3405716 prefixEnd_3405716 388615395712867189819423 := by
  unfold tailWord_3405716
  simp only [CollatzResearch.WordTrace]
  refine ⟨62108333664840028415194501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82811111553120037886926001 62108333664840028415194501)
  ·
    refine ⟨11645312562157505327848969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62108333664840028415194501 11645312562157505327848969)
    ·
      refine ⟨8733984421618128995886727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11645312562157505327848969 8733984421618128995886727)
      ·
        refine ⟨13100976632427193493830091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8733984421618128995886727 13100976632427193493830091)
        ·
          refine ⟨19651464948640790240745137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13100976632427193493830091 19651464948640790240745137)
          ·
            refine ⟨14738598711480592680558853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19651464948640790240745137 14738598711480592680558853)
            ·
              refine ⟨2763487258402611127604785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14738598711480592680558853 2763487258402611127604785)
              ·
                refine ⟨2072615443801958345703589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2763487258402611127604785 2072615443801958345703589)
                ·
                  refine ⟨388615395712867189819423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2072615443801958345703589 388615395712867189819423)
                  ·
                    rfl

theorem cell22_3405716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_3405716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3405716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3405716 prefixEnd_3405716 := by exact prefixLift 3405716
  have htrace : WordTrace (prefixWord ++ tailWord_3405716) baseStart_3405716 baseEnd_3405716 := by
    simpa [prefixWord, tailWord_3405716, baseEnd_3405716] using wordTrace_append hprefix tailTrace_3405716
  have hstable : (prefixWord ++ tailWord_3405716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405716).length < 2 ^ (prefixWord ++ tailWord_3405716).sum := by decide
  have hdescent : baseEnd_3405716 < baseStart_3405716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405772 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 7]
def baseStart_3405772 : Nat := 118140960795 + 3405772 * 2 ^ 59
def prefixEnd_3405772 : Nat := 4983230072969 + 3 ^ 40 * 3405772 * 2
def baseEnd_3405772 : Nat := 388621785694345363352699

theorem tailTrace_3405772 : CollatzResearch.WordTrace tailWord_3405772 prefixEnd_3405772 388621785694345363352699 := by
  unfold tailWord_3405772
  simp only [CollatzResearch.WordTrace]
  refine ⟨62109354908738589197213785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82812473211651452262951713 62109354908738589197213785)
  ·
    refine ⟨46582016181553941897910339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62109354908738589197213785 46582016181553941897910339)
    ·
      refine ⟨69873024272330912846865509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46582016181553941897910339 69873024272330912846865509)
      ·
        refine ⟨13101192051062046158787283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69873024272330912846865509 13101192051062046158787283)
        ·
          refine ⟨19651788076593069238180925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13101192051062046158787283 19651788076593069238180925)
          ·
            refine ⟨7369420528722400964317847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19651788076593069238180925 7369420528722400964317847)
            ·
              refine ⟨11054130793083601446476771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7369420528722400964317847 11054130793083601446476771)
              ·
                refine ⟨16581196189625402169715157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11054130793083601446476771 16581196189625402169715157)
                ·
                  refine ⟨388621785694345363352699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16581196189625402169715157 388621785694345363352699)
                  ·
                    rfl

theorem cell22_3405772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_3405772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3405772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3405772 prefixEnd_3405772 := by exact prefixLift 3405772
  have htrace : WordTrace (prefixWord ++ tailWord_3405772) baseStart_3405772 baseEnd_3405772 := by
    simpa [prefixWord, tailWord_3405772, baseEnd_3405772] using wordTrace_append hprefix tailTrace_3405772
  have hstable : (prefixWord ++ tailWord_3405772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405772).length < 2 ^ (prefixWord ++ tailWord_3405772).sum := by decide
  have hdescent : baseEnd_3405772 < baseStart_3405772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406074 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 1, 7]
def baseStart_3406074 : Nat := 118140960795 + 3406074 * 2 ^ 59
def prefixEnd_3406074 : Nat := 4983230072969 + 3 ^ 40 * 3406074 * 2
def baseEnd_3406074 : Nat := 1165968737854807969007171

theorem tailTrace_3406074 : CollatzResearch.WordTrace tailWord_3406074 prefixEnd_3406074 1165968737854807969007171 := by
  unfold tailWord_3406074
  simp only [CollatzResearch.WordTrace]
  refine ⟨31057431165595770992980319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82819816441588722647947517 31057431165595770992980319)
  ·
    refine ⟨46586146748393656489470479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31057431165595770992980319 46586146748393656489470479)
    ·
      refine ⟨69879220122590484734205719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46586146748393656489470479 69879220122590484734205719)
      ·
        refine ⟨104818830183885727101308579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69879220122590484734205719 104818830183885727101308579)
        ·
          refine ⟨157228245275828590651962869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104818830183885727101308579 157228245275828590651962869)
          ·
            refine ⟨14740147994608930373621519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157228245275828590651962869 14740147994608930373621519)
            ·
              refine ⟨22110221991913395560432279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14740147994608930373621519 22110221991913395560432279)
              ·
                refine ⟨33165332987870093340648419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22110221991913395560432279 33165332987870093340648419)
                ·
                  refine ⟨49747999481805140010972629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33165332987870093340648419 49747999481805140010972629)
                  ·
                    refine ⟨1165968737854807969007171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49747999481805140010972629 1165968737854807969007171)
                    ·
                      rfl

theorem cell22_3406074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_3406074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406074 prefixEnd_3406074 := by exact prefixLift 3406074
  have htrace : WordTrace (prefixWord ++ tailWord_3406074) baseStart_3406074 baseEnd_3406074 := by
    simpa [prefixWord, tailWord_3406074, baseEnd_3406074] using wordTrace_append hprefix tailTrace_3406074
  have hstable : (prefixWord ++ tailWord_3406074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406074).length < 2 ^ (prefixWord ++ tailWord_3406074).sum := by decide
  have hdescent : baseEnd_3406074 < baseStart_3406074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406076 : List Nat := [2, 2, 2, 1, 4, 1, 2, 3, 5]
def baseStart_3406076 : Nat := 118140960795 + 3406076 * 2 ^ 59
def prefixEnd_3406076 : Nat := 4983230072969 + 3 ^ 40 * 3406076 * 2
def baseEnd_3406076 : Nat := 388656474165226876819055

theorem tailTrace_3406076 : CollatzResearch.WordTrace tailWord_3406076 prefixEnd_3406076 388656474165226876819055 := by
  unfold tailWord_3406076
  simp only [CollatzResearch.WordTrace]
  refine ⟨62114898804187919156747041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82819865072250558875662721 62114898804187919156747041)
  ·
    refine ⟨46586174103140939367560281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62114898804187919156747041 46586174103140939367560281)
    ·
      refine ⟨34939630577355704525670211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46586174103140939367560281 34939630577355704525670211)
      ·
        refine ⟨52409445866033556788505317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34939630577355704525670211 52409445866033556788505317)
        ·
          refine ⟨9826771099881291897844747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52409445866033556788505317 9826771099881291897844747)
          ·
            refine ⟨14740156649821937846767121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9826771099881291897844747 14740156649821937846767121)
            ·
              refine ⟨11055117487366453385075341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14740156649821937846767121 11055117487366453385075341)
              ·
                refine ⟨4145669057762420019403253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11055117487366453385075341 4145669057762420019403253)
                ·
                  refine ⟨388656474165226876819055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4145669057762420019403253 388656474165226876819055)
                  ·
                    rfl

theorem cell22_3406076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_3406076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406076 prefixEnd_3406076 := by exact prefixLift 3406076
  have htrace : WordTrace (prefixWord ++ tailWord_3406076) baseStart_3406076 baseEnd_3406076 := by
    simpa [prefixWord, tailWord_3406076, baseEnd_3406076] using wordTrace_append hprefix tailTrace_3406076
  have hstable : (prefixWord ++ tailWord_3406076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406076).length < 2 ^ (prefixWord ++ tailWord_3406076).sum := by decide
  have hdescent : baseEnd_3406076 < baseStart_3406076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406104 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 8]
def baseStart_3406104 : Nat := 118140960795 + 3406104 * 2 ^ 59
def prefixEnd_3406104 : Nat := 4983230072969 + 3 ^ 40 * 3406104 * 2
def baseEnd_3406104 : Nat := 388659669155965963585693

theorem tailTrace_3406104 : CollatzResearch.WordTrace tailWord_3406104 prefixEnd_3406104 388659669155965963585693 := by
  unfold tailWord_3406104
  simp only [CollatzResearch.WordTrace]
  refine ⟨62115409426137199547756683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82820545901516266063675577 62115409426137199547756683)
  ·
    refine ⟨93173114139205799321635025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62115409426137199547756683 93173114139205799321635025)
    ·
      refine ⟨69879835604404349491226269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93173114139205799321635025 69879835604404349491226269)
      ·
        refine ⟨26204938351651631059209851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69879835604404349491226269 26204938351651631059209851)
        ·
          refine ⟨39307407527477446588814777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26204938351651631059209851 39307407527477446588814777)
          ·
            refine ⟨29480555645608084941611083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39307407527477446588814777 29480555645608084941611083)
            ·
              refine ⟨44220833468412127412416625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29480555645608084941611083 44220833468412127412416625)
              ·
                refine ⟨33165625101309095559312469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44220833468412127412416625 33165625101309095559312469)
                ·
                  refine ⟨388659669155965963585693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33165625101309095559312469 388659669155965963585693)
                  ·
                    rfl

theorem cell22_3406104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 8].length) (baseStart_3406104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406104 prefixEnd_3406104 := by exact prefixLift 3406104
  have htrace : WordTrace (prefixWord ++ tailWord_3406104) baseStart_3406104 baseEnd_3406104 := by
    simpa [prefixWord, tailWord_3406104, baseEnd_3406104] using wordTrace_append hprefix tailTrace_3406104
  have hstable : (prefixWord ++ tailWord_3406104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406104).length < 2 ^ (prefixWord ++ tailWord_3406104).sum := by decide
  have hdescent : baseEnd_3406104 < baseStart_3406104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406110 : List Nat := [4, 3, 2, 1, 1, 1, 3, 2, 5]
def baseStart_3406110 : Nat := 118140960795 + 3406110 * 2 ^ 59
def prefixEnd_3406110 : Nat := 4983230072969 + 3 ^ 40 * 3406110 * 2
def baseEnd_3406110 : Nat := 388660353796838625035687

theorem tailTrace_3406110 : CollatzResearch.WordTrace tailWord_3406110 prefixEnd_3406110 388660353796838625035687 := by
  unfold tailWord_3406110
  simp only [CollatzResearch.WordTrace]
  refine ⟨15528879711281582765028973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82820691793501774746821189 15528879711281582765028973)
  ·
    refine ⟨5823329891730593536885865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15528879711281582765028973 5823329891730593536885865)
    ·
      refine ⟨4367497418797945152664399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5823329891730593536885865 4367497418797945152664399)
      ·
        refine ⟨6551246128196917728996599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4367497418797945152664399 6551246128196917728996599)
        ·
          refine ⟨9826869192295376593494899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6551246128196917728996599 9826869192295376593494899)
          ·
            refine ⟨14740303788443064890242349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9826869192295376593494899 14740303788443064890242349)
            ·
              refine ⟨5527613920666149333840881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14740303788443064890242349 5527613920666149333840881)
              ·
                refine ⟨4145710440499612000380661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5527613920666149333840881 4145710440499612000380661)
                ·
                  refine ⟨388660353796838625035687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4145710440499612000380661 388660353796838625035687)
                  ·
                    rfl

theorem cell22_3406110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_3406110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406110 prefixEnd_3406110 := by exact prefixLift 3406110
  have htrace : WordTrace (prefixWord ++ tailWord_3406110) baseStart_3406110 baseEnd_3406110 := by
    simpa [prefixWord, tailWord_3406110, baseEnd_3406110] using wordTrace_append hprefix tailTrace_3406110
  have hstable : (prefixWord ++ tailWord_3406110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406110).length < 2 ^ (prefixWord ++ tailWord_3406110).sum := by decide
  have hdescent : baseEnd_3406110 < baseStart_3406110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406136 : List Nat := [2, 1, 2, 1, 3, 1, 5, 1, 1, 5]
def baseStart_3406136 : Nat := 118140960795 + 3406136 * 2 ^ 59
def prefixEnd_3406136 : Nat := 4983230072969 + 3 ^ 40 * 3406136 * 2
def baseEnd_3406136 : Nat := 1165989961721860473956981

theorem tailTrace_3406136 : CollatzResearch.WordTrace tailWord_3406136 prefixEnd_3406136 1165989961721860473956981 := by
  unfold tailWord_3406136
  simp only [CollatzResearch.WordTrace]
  refine ⟨62115992994079234280339131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82821323992105645707118841 62115992994079234280339131)
  ·
    refine ⟨93173989491118851420508697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62115992994079234280339131 93173989491118851420508697)
    ·
      refine ⟨69880492118339138565381523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93173989491118851420508697 69880492118339138565381523)
      ·
        refine ⟨104820738177508707848072285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69880492118339138565381523 104820738177508707848072285)
        ·
          refine ⟨39307776816565765443027107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104820738177508707848072285 39307776816565765443027107)
          ·
            refine ⟨58961665224848648164540661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39307776816565765443027107 58961665224848648164540661)
            ·
              refine ⟨5527656114829560765425687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58961665224848648164540661 5527656114829560765425687)
              ·
                refine ⟨8291484172244341148138531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5527656114829560765425687 8291484172244341148138531)
                ·
                  refine ⟨12437226258366511722207797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8291484172244341148138531 12437226258366511722207797)
                  ·
                    refine ⟨1165989961721860473956981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12437226258366511722207797 1165989961721860473956981)
                    ·
                      rfl

theorem cell22_3406136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_3406136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406136 prefixEnd_3406136 := by exact prefixLift 3406136
  have htrace : WordTrace (prefixWord ++ tailWord_3406136) baseStart_3406136 baseEnd_3406136 := by
    simpa [prefixWord, tailWord_3406136, baseEnd_3406136] using wordTrace_append hprefix tailTrace_3406136
  have hstable : (prefixWord ++ tailWord_3406136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406136).length < 2 ^ (prefixWord ++ tailWord_3406136).sum := by decide
  have hdescent : baseEnd_3406136 < baseStart_3406136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406151 : List Nat := [1, 1, 4, 1, 2, 2, 2, 3, 2, 4]
def baseStart_3406151 : Nat := 118140960795 + 3406151 * 2 ^ 59
def prefixEnd_3406151 : Nat := 4983230072969 + 3 ^ 40 * 3406151 * 2
def baseEnd_3406151 : Nat := 1165995096528405434831935

theorem tailTrace_3406151 : CollatzResearch.WordTrace tailWord_3406151 prefixEnd_3406151 1165995096528405434831935 := by
  unfold tailWord_3406151
  simp only [CollatzResearch.WordTrace]
  refine ⟨124232533083104126122474307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82821688722069417414982871 124232533083104126122474307)
  ·
    refine ⟨186348799624656189183711461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124232533083104126122474307 186348799624656189183711461)
    ·
      refine ⟨34940399929623035471945899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186348799624656189183711461 34940399929623035471945899)
      ·
        refine ⟨52410599894434553207918849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34940399929623035471945899 52410599894434553207918849)
        ·
          refine ⟨39307949920825914905939137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52410599894434553207918849 39307949920825914905939137)
          ·
            refine ⟨29480962440619436179454353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39307949920825914905939137 29480962440619436179454353)
            ·
              refine ⟨22110721830464577134590765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29480962440619436179454353 22110721830464577134590765)
              ·
                refine ⟨8291520686424216425471537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22110721830464577134590765 8291520686424216425471537)
                ·
                  refine ⟨6218640514818162319103653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8291520686424216425471537 6218640514818162319103653)
                  ·
                    refine ⟨1165995096528405434831935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6218640514818162319103653 1165995096528405434831935)
                    ·
                      rfl

theorem cell22_3406151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_3406151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406151 prefixEnd_3406151 := by exact prefixLift 3406151
  have htrace : WordTrace (prefixWord ++ tailWord_3406151) baseStart_3406151 baseEnd_3406151 := by
    simpa [prefixWord, tailWord_3406151, baseEnd_3406151] using wordTrace_append hprefix tailTrace_3406151
  have hstable : (prefixWord ++ tailWord_3406151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406151).length < 2 ^ (prefixWord ++ tailWord_3406151).sum := by decide
  have hdescent : baseEnd_3406151 < baseStart_3406151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406172 : List Nat := [2, 2, 4, 3, 2, 1, 1, 1, 6]
def baseStart_3406172 : Nat := 118140960795 + 3406172 * 2 ^ 59
def prefixEnd_3406172 : Nat := 4983230072969 + 3 ^ 40 * 3406172 * 2
def baseEnd_3406172 : Nat := 388667428419189460018957

theorem tailTrace_3406172 : CollatzResearch.WordTrace tailWord_3406172 prefixEnd_3406172 388667428419189460018957 := by
  unfold tailWord_3406172
  simp only [CollatzResearch.WordTrace]
  refine ⟨62116649508014023354494385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82822199344018697805992513 62116649508014023354494385)
  ·
    refine ⟨46587487131010517515870789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62116649508014023354494385 46587487131010517515870789)
    ·
      refine ⟨8735153837064472034225773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46587487131010517515870789 8735153837064472034225773)
      ·
        refine ⟨3275682688899177012834665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8735153837064472034225773 3275682688899177012834665)
        ·
          refine ⟨2456762016674382759625999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3275682688899177012834665 2456762016674382759625999)
          ·
            refine ⟨3685143025011574139438999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2456762016674382759625999 3685143025011574139438999)
            ·
              refine ⟨5527714537517361209158499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3685143025011574139438999 5527714537517361209158499)
              ·
                refine ⟨8291571806276041813737749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5527714537517361209158499 8291571806276041813737749)
                ·
                  refine ⟨388667428419189460018957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8291571806276041813737749 388667428419189460018957)
                  ·
                    rfl

theorem cell22_3406172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 6].length) (baseStart_3406172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406172 prefixEnd_3406172 := by exact prefixLift 3406172
  have htrace : WordTrace (prefixWord ++ tailWord_3406172) baseStart_3406172 baseEnd_3406172 := by
    simpa [prefixWord, tailWord_3406172, baseEnd_3406172] using wordTrace_append hprefix tailTrace_3406172
  have hstable : (prefixWord ++ tailWord_3406172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406172).length < 2 ^ (prefixWord ++ tailWord_3406172).sum := by decide
  have hdescent : baseEnd_3406172 < baseStart_3406172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406215 : List Nat := [1, 1, 4, 2, 2, 1, 2, 5, 1, 3]
def baseStart_3406215 : Nat := 118140960795 + 3406215 * 2 ^ 59
def prefixEnd_3406215 : Nat := 4983230072969 + 3 ^ 40 * 3406215 * 2
def baseEnd_3406215 : Nat := 1166017005036330601231739

theorem tailTrace_3406215 : CollatzResearch.WordTrace tailWord_3406215 prefixEnd_3406215 1166017005036330601231739 := by
  unfold tailWord_3406215
  simp only [CollatzResearch.WordTrace]
  refine ⟨124234867354872265052804099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82823244903248176701869399 124234867354872265052804099)
  ·
    refine ⟨186352301032308397579206149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124234867354872265052804099 186352301032308397579206149)
    ·
      refine ⟨34941056443557824546101153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186352301032308397579206149 34941056443557824546101153)
      ·
        refine ⟨26205792332668368409575865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34941056443557824546101153 26205792332668368409575865)
        ·
          refine ⟨19654344249501276307181899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26205792332668368409575865 19654344249501276307181899)
          ·
            refine ⟨29481516374251914460772849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19654344249501276307181899 29481516374251914460772849)
            ·
              refine ⟨22111137280688935845579637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29481516374251914460772849 22111137280688935845579637)
              ·
                refine ⟨2072919120064587735523091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22111137280688935845579637 2072919120064587735523091)
                ·
                  refine ⟨3109378680096881603284637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2072919120064587735523091 3109378680096881603284637)
                  ·
                    refine ⟨1166017005036330601231739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3109378680096881603284637 1166017005036330601231739)
                    ·
                      rfl

theorem cell22_3406215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_3406215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406215 prefixEnd_3406215 := by exact prefixLift 3406215
  have htrace : WordTrace (prefixWord ++ tailWord_3406215) baseStart_3406215 baseEnd_3406215 := by
    simpa [prefixWord, tailWord_3406215, baseEnd_3406215] using wordTrace_append hprefix tailTrace_3406215
  have hstable : (prefixWord ++ tailWord_3406215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406215).length < 2 ^ (prefixWord ++ tailWord_3406215).sum := by decide
  have hdescent : baseEnd_3406215 < baseStart_3406215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406232 : List Nat := [2, 1, 2, 5, 1, 2, 1, 4, 1, 3]
def baseStart_3406232 : Nat := 118140960795 + 3406232 * 2 ^ 59
def prefixEnd_3406232 : Nat := 4983230072969 + 3 ^ 40 * 3406232 * 2
def baseEnd_3406232 : Nat := 1166022824483748223556687

theorem tailTrace_3406232 : CollatzResearch.WordTrace tailWord_3406232 prefixEnd_3406232 1166022824483748223556687 := by
  unfold tailWord_3406232
  simp only [CollatzResearch.WordTrace]
  refine ⟨62117743697905338478086475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82823658263873784637448633 62117743697905338478086475)
  ·
    refine ⟨93176615546858007717129713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62117743697905338478086475 93176615546858007717129713)
    ·
      refine ⟨69882461660143505787847285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93176615546858007717129713 69882461660143505787847285)
      ·
        refine ⟨6551480780638453667610683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69882461660143505787847285 6551480780638453667610683)
        ·
          refine ⟨9827221170957680501416025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6551480780638453667610683 9827221170957680501416025)
          ·
            refine ⟨7370415878218260376062019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9827221170957680501416025 7370415878218260376062019)
            ·
              refine ⟨11055623817327390564093029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7370415878218260376062019 11055623817327390564093029)
              ·
                refine ⟨2072929465748885730767443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11055623817327390564093029 2072929465748885730767443)
                ·
                  refine ⟨3109394198623328596151165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2072929465748885730767443 3109394198623328596151165)
                  ·
                    refine ⟨1166022824483748223556687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3109394198623328596151165 1166022824483748223556687)
                    ·
                      rfl

theorem cell22_3406232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 1, 3].length) (baseStart_3406232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406232 prefixEnd_3406232 := by exact prefixLift 3406232
  have htrace : WordTrace (prefixWord ++ tailWord_3406232) baseStart_3406232 baseEnd_3406232 := by
    simpa [prefixWord, tailWord_3406232, baseEnd_3406232] using wordTrace_append hprefix tailTrace_3406232
  have hstable : (prefixWord ++ tailWord_3406232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406232).length < 2 ^ (prefixWord ++ tailWord_3406232).sum := by decide
  have hdescent : baseEnd_3406232 < baseStart_3406232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406258 : List Nat := [3, 2, 1, 1, 1, 1, 4, 4, 1, 4]
def baseStart_3406258 : Nat := 118140960795 + 3406258 * 2 ^ 59
def prefixEnd_3406258 : Nat := 4983230072969 + 3 ^ 40 * 3406258 * 2
def baseEnd_3406258 : Nat := 1166031724815092822406607

theorem tailTrace_3406258 : CollatzResearch.WordTrace tailWord_3406258 prefixEnd_3406258 1166031724815092822406607 := by
  unfold tailWord_3406258
  simp only [CollatzResearch.WordTrace]
  refine ⟨31059108923429120849154857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82824290462477655597746285 31059108923429120849154857)
  ·
    refine ⟨23294331692571840636866143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31059108923429120849154857 23294331692571840636866143)
    ·
      refine ⟨34941497538857760955299215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23294331692571840636866143 34941497538857760955299215)
      ·
        refine ⟨52412246308286641432948823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34941497538857760955299215 52412246308286641432948823)
        ·
          refine ⟨78618369462429962149423235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52412246308286641432948823 78618369462429962149423235)
          ·
            refine ⟨117927554193644943224134853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78618369462429962149423235 117927554193644943224134853)
            ·
              refine ⟨22111416411308426854525285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117927554193644943224134853 22111416411308426854525285)
              ·
                refine ⟨4145890577120330035223491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22111416411308426854525285 4145890577120330035223491)
                ·
                  refine ⟨6218835865680495052835237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4145890577120330035223491 6218835865680495052835237)
                  ·
                    refine ⟨1166031724815092822406607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6218835865680495052835237 1166031724815092822406607)
                    ·
                      rfl

theorem cell22_3406258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_3406258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406258 prefixEnd_3406258 := by exact prefixLift 3406258
  have htrace : WordTrace (prefixWord ++ tailWord_3406258) baseStart_3406258 baseEnd_3406258 := by
    simpa [prefixWord, tailWord_3406258, baseEnd_3406258] using wordTrace_append hprefix tailTrace_3406258
  have hstable : (prefixWord ++ tailWord_3406258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406258).length < 2 ^ (prefixWord ++ tailWord_3406258).sum := by decide
  have hdescent : baseEnd_3406258 < baseStart_3406258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406316 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 2, 7]
def baseStart_3406316 : Nat := 118140960795 + 3406316 * 2 ^ 59
def prefixEnd_3406316 : Nat := 4983230072969 + 3 ^ 40 * 3406316 * 2
def baseEnd_3406316 : Nat := 1166051579400400004456429

theorem tailTrace_3406316 : CollatzResearch.WordTrace tailWord_3406316 prefixEnd_3406316 1166051579400400004456429 := by
  unfold tailWord_3406316
  simp only [CollatzResearch.WordTrace]
  refine ⟨62119275563753179651115401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82825700751670906201487201 62119275563753179651115401)
  ·
    refine ⟨46589456672814884738336551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62119275563753179651115401 46589456672814884738336551)
    ·
      refine ⟨69884185009222327107504827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46589456672814884738336551 69884185009222327107504827)
      ·
        refine ⟨104826277513833490661257241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69884185009222327107504827 104826277513833490661257241)
        ·
          refine ⟨78619708135375117995942931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104826277513833490661257241 78619708135375117995942931)
          ·
            refine ⟨117929562203062676993914397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78619708135375117995942931 117929562203062676993914397)
            ·
              refine ⟨44223585826148503872717899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117929562203062676993914397 44223585826148503872717899)
              ·
                refine ⟨66335378739222755809076849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44223585826148503872717899 66335378739222755809076849)
                ·
                  refine ⟨49751534054417066856807637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66335378739222755809076849 49751534054417066856807637)
                  ·
                    refine ⟨1166051579400400004456429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49751534054417066856807637 1166051579400400004456429)
                    ·
                      rfl

theorem cell22_3406316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_3406316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406316 prefixEnd_3406316 := by exact prefixLift 3406316
  have htrace : WordTrace (prefixWord ++ tailWord_3406316) baseStart_3406316 baseEnd_3406316 := by
    simpa [prefixWord, tailWord_3406316, baseEnd_3406316] using wordTrace_append hprefix tailTrace_3406316
  have hstable : (prefixWord ++ tailWord_3406316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406316).length < 2 ^ (prefixWord ++ tailWord_3406316).sum := by decide
  have hdescent : baseEnd_3406316 < baseStart_3406316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406318 : List Nat := [4, 1, 2, 1, 2, 3, 1, 8]
def baseStart_3406318 : Nat := 118140960795 + 3406318 * 2 ^ 59
def prefixEnd_3406318 : Nat := 4983230072969 + 3 ^ 40 * 3406318 * 2
def baseEnd_3406318 : Nat := 129561362671252518434047

theorem tailTrace_3406318 : CollatzResearch.WordTrace tailWord_3406318 prefixEnd_3406318 129561362671252518434047 := by
  unfold tailWord_3406318
  simp only [CollatzResearch.WordTrace]
  refine ⟨15529828009187389205475451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82825749382332742429202405 15529828009187389205475451)
  ·
    refine ⟨23294742013781083808213177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15529828009187389205475451 23294742013781083808213177)
    ·
      refine ⟨17471056510335812856159883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23294742013781083808213177 17471056510335812856159883)
      ·
        refine ⟨26206584765503719284239825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17471056510335812856159883 26206584765503719284239825)
        ·
          refine ⟨19654938574127789463179869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26206584765503719284239825 19654938574127789463179869)
          ·
            refine ⟨7370601965297921048692451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19654938574127789463179869 7370601965297921048692451)
            ·
              refine ⟨11055902947946881573038677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7370601965297921048692451 11055902947946881573038677)
              ·
                refine ⟨129561362671252518434047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11055902947946881573038677 129561362671252518434047)
                ·
                  rfl

theorem cell22_3406318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_3406318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406318 prefixEnd_3406318 := by exact prefixLift 3406318
  have htrace : WordTrace (prefixWord ++ tailWord_3406318) baseStart_3406318 baseEnd_3406318 := by
    simpa [prefixWord, tailWord_3406318, baseEnd_3406318] using wordTrace_append hprefix tailTrace_3406318
  have hstable : (prefixWord ++ tailWord_3406318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406318).length < 2 ^ (prefixWord ++ tailWord_3406318).sum := by decide
  have hdescent : baseEnd_3406318 < baseStart_3406318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406356 : List Nat := [2, 4, 3, 1, 1, 3, 2, 1, 2, 3]
def baseStart_3406356 : Nat := 118140960795 + 3406356 * 2 ^ 59
def prefixEnd_3406356 : Nat := 4983230072969 + 3 ^ 40 * 3406356 * 2
def baseEnd_3406356 : Nat := 1166065272217853233456307

theorem tailTrace_3406356 : CollatzResearch.WordTrace tailWord_3406356 prefixEnd_3406356 1166065272217853233456307 := by
  unfold tailWord_3406356
  simp only [CollatzResearch.WordTrace]
  refine ⟨62120005023680723066843461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82826673364907630755791281 62120005023680723066843461)
  ·
    refine ⟨11647500941940135575033149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62120005023680723066843461 11647500941940135575033149)
    ·
      refine ⟨4367812853227550840637431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11647500941940135575033149 4367812853227550840637431)
      ·
        refine ⟨6551719279841326260956147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4367812853227550840637431 6551719279841326260956147)
        ·
          refine ⟨9827578919761989391434221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6551719279841326260956147 9827578919761989391434221)
          ·
            refine ⟨3685342094910746021787833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9827578919761989391434221 3685342094910746021787833)
            ·
              refine ⟨2764006571183059516340875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3685342094910746021787833 2764006571183059516340875)
              ·
                refine ⟨4146009856774589274511313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2764006571183059516340875 4146009856774589274511313)
                ·
                  refine ⟨3109507392580941955883485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4146009856774589274511313 3109507392580941955883485)
                  ·
                    refine ⟨1166065272217853233456307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3109507392580941955883485 1166065272217853233456307)
                    ·
                      rfl

theorem cell22_3406356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_3406356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406356 prefixEnd_3406356 := by exact prefixLift 3406356
  have htrace : WordTrace (prefixWord ++ tailWord_3406356) baseStart_3406356 baseEnd_3406356 := by
    simpa [prefixWord, tailWord_3406356, baseEnd_3406356] using wordTrace_append hprefix tailTrace_3406356
  have hstable : (prefixWord ++ tailWord_3406356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406356).length < 2 ^ (prefixWord ++ tailWord_3406356).sum := by decide
  have hdescent : baseEnd_3406356 < baseStart_3406356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406401 : List Nat := [1, 2, 5, 1, 1, 4, 2, 2, 1, 3]
def baseStart_3406401 : Nat := 118140960795 + 3406401 * 2 ^ 59
def prefixEnd_3406401 : Nat := 4983230072969 + 3 ^ 40 * 3406401 * 2
def baseEnd_3406401 : Nat := 1166080676637488116081169

theorem tailTrace_3406401 : CollatzResearch.WordTrace tailWord_3406401 prefixEnd_3406401 1166080676637488116081169 := by
  unfold tailWord_3406401
  simp only [CollatzResearch.WordTrace]
  refine ⟨124241651332198418819075057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82827767554798945879383371 124241651332198418819075057)
  ·
    refine ⟨93181238499148814114306293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124241651332198418819075057 93181238499148814114306293)
    ·
      refine ⟨8735741109295201323216215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93181238499148814114306293 8735741109295201323216215)
      ·
        refine ⟨13103611663942801984824323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8735741109295201323216215 13103611663942801984824323)
        ·
          refine ⟨19655417495914202977236485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13103611663942801984824323 19655417495914202977236485)
          ·
            refine ⟨3685390780483913058231841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19655417495914202977236485 3685390780483913058231841)
            ·
              refine ⟨2764043085362934793673881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3685390780483913058231841 2764043085362934793673881)
              ·
                refine ⟨2073032314022201095255411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2764043085362934793673881 2073032314022201095255411)
                ·
                  refine ⟨3109548471033301642883117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2073032314022201095255411 3109548471033301642883117)
                  ·
                    refine ⟨1166080676637488116081169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3109548471033301642883117 1166080676637488116081169)
                    ·
                      rfl

theorem cell22_3406401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_3406401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406401 prefixEnd_3406401 := by exact prefixLift 3406401
  have htrace : WordTrace (prefixWord ++ tailWord_3406401) baseStart_3406401 baseEnd_3406401 := by
    simpa [prefixWord, tailWord_3406401, baseEnd_3406401] using wordTrace_append hprefix tailTrace_3406401
  have hstable : (prefixWord ++ tailWord_3406401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406401).length < 2 ^ (prefixWord ++ tailWord_3406401).sum := by decide
  have hdescent : baseEnd_3406401 < baseStart_3406401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406442 : List Nat := [3, 1, 3, 2, 1, 1, 4, 3, 4]
def baseStart_3406442 : Nat := 118140960795 + 3406442 * 2 ^ 59
def prefixEnd_3406442 : Nat := 4983230072969 + 3 ^ 40 * 3406442 * 2
def baseEnd_3406442 : Nat := 388698237258459225268681

theorem tailTrace_3406442 : CollatzResearch.WordTrace tailWord_3406442 prefixEnd_3406442 388698237258459225268681 := by
  unfold tailWord_3406442
  simp only [CollatzResearch.WordTrace]
  refine ⟨31060786681262470705329395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82828764483366588547545053 31060786681262470705329395)
  ·
    refine ⟨46591180021893706057994093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31060786681262470705329395 46591180021893706057994093)
    ·
      refine ⟨17471692508210139771747785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46591180021893706057994093 17471692508210139771747785)
      ·
        refine ⟨13103769381157604828810839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17471692508210139771747785 13103769381157604828810839)
        ·
          refine ⟨19655654071736407243216259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13103769381157604828810839 19655654071736407243216259)
          ·
            refine ⟨29483481107604610864824389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19655654071736407243216259 29483481107604610864824389)
            ·
              refine ⟨5528152707675864537154573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29483481107604610864824389 5528152707675864537154573)
              ·
                refine ⟨2073057265378449201432965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5528152707675864537154573 2073057265378449201432965)
                ·
                  refine ⟨388698237258459225268681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2073057265378449201432965 388698237258459225268681)
                  ·
                    rfl

theorem cell22_3406442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 4].length) (baseStart_3406442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406442 prefixEnd_3406442 := by exact prefixLift 3406442
  have htrace : WordTrace (prefixWord ++ tailWord_3406442) baseStart_3406442 baseEnd_3406442 := by
    simpa [prefixWord, tailWord_3406442, baseEnd_3406442] using wordTrace_append hprefix tailTrace_3406442
  have hstable : (prefixWord ++ tailWord_3406442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406442).length < 2 ^ (prefixWord ++ tailWord_3406442).sum := by decide
  have hdescent : baseEnd_3406442 < baseStart_3406442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406457 : List Nat := [1, 2, 1, 3, 3, 2, 3, 2, 2, 3]
def baseStart_3406457 : Nat := 118140960795 + 3406457 * 2 ^ 59
def prefixEnd_3406457 : Nat := 4983230072969 + 3 ^ 40 * 3406457 * 2
def baseEnd_3406457 : Nat := 1166099846581922636680997

theorem tailTrace_3406457 : CollatzResearch.WordTrace tailWord_3406457 prefixEnd_3406457 1166099846581922636680997 := by
  unfold tailWord_3406457
  simp only [CollatzResearch.WordTrace]
  refine ⟨124243693819995540383113625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82829129213330360255409083 124243693819995540383113625)
  ·
    refine ⟨93182770364996655287335219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124243693819995540383113625 93182770364996655287335219)
    ·
      refine ⟨139774155547494982931002829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93182770364996655287335219 139774155547494982931002829)
      ·
        refine ⟨52415308330310618599126061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139774155547494982931002829 52415308330310618599126061)
        ·
          refine ⟨19655740623866481974672273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52415308330310618599126061 19655740623866481974672273)
          ·
            refine ⟨14741805467899861481004205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19655740623866481974672273 14741805467899861481004205)
            ·
              refine ⟨5528177050462448055376577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14741805467899861481004205 5528177050462448055376577)
              ·
                refine ⟨4146132787846836041532433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5528177050462448055376577 4146132787846836041532433)
                ·
                  refine ⟨3109599590885127031149325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4146132787846836041532433 3109599590885127031149325)
                  ·
                    refine ⟨1166099846581922636680997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3109599590885127031149325 1166099846581922636680997)
                    ·
                      rfl

theorem cell22_3406457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 3].length) (baseStart_3406457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406457 prefixEnd_3406457 := by exact prefixLift 3406457
  have htrace : WordTrace (prefixWord ++ tailWord_3406457) baseStart_3406457 baseEnd_3406457 := by
    simpa [prefixWord, tailWord_3406457, baseEnd_3406457] using wordTrace_append hprefix tailTrace_3406457
  have hstable : (prefixWord ++ tailWord_3406457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406457).length < 2 ^ (prefixWord ++ tailWord_3406457).sum := by decide
  have hdescent : baseEnd_3406457 < baseStart_3406457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406474 : List Nat := [3, 1, 2, 3, 4, 1, 1, 1, 1, 5]
def baseStart_3406474 : Nat := 118140960795 + 3406474 * 2 ^ 59
def prefixEnd_3406474 : Nat := 4983230072969 + 3 ^ 40 * 3406474 * 2
def baseEnd_3406474 : Nat := 1166105666029340259005945

theorem tailTrace_3406474 : CollatzResearch.WordTrace tailWord_3406474 prefixEnd_3406474 1166105666029340259005945 := by
  unfold tailWord_3406474
  simp only [CollatzResearch.WordTrace]
  refine ⟨31061078465233488071620619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82829542573955968190988317 31061078465233488071620619)
  ·
    refine ⟨46591617697850232107430929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31061078465233488071620619 46591617697850232107430929)
    ·
      refine ⟨34943713273387674080573197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46591617697850232107430929 34943713273387674080573197)
      ·
        refine ⟨13103892477520377780214949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34943713273387674080573197 13103892477520377780214949)
        ·
          refine ⟨2456979839535070833790303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13103892477520377780214949 2456979839535070833790303)
          ·
            refine ⟨3685469759302606250685455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2456979839535070833790303 3685469759302606250685455)
            ·
              refine ⟨5528204638953909376028183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3685469759302606250685455 5528204638953909376028183)
              ·
                refine ⟨8292306958430864064042275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5528204638953909376028183 8292306958430864064042275)
                ·
                  refine ⟨12438460437646296096063413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8292306958430864064042275 12438460437646296096063413)
                  ·
                    refine ⟨1166105666029340259005945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12438460437646296096063413 1166105666029340259005945)
                    ·
                      rfl

theorem cell22_3406474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_3406474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406474 prefixEnd_3406474 := by exact prefixLift 3406474
  have htrace : WordTrace (prefixWord ++ tailWord_3406474) baseStart_3406474 baseEnd_3406474 := by
    simpa [prefixWord, tailWord_3406474, baseEnd_3406474] using wordTrace_append hprefix tailTrace_3406474
  have hstable : (prefixWord ++ tailWord_3406474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406474).length < 2 ^ (prefixWord ++ tailWord_3406474).sum := by decide
  have hdescent : baseEnd_3406474 < baseStart_3406474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406519 : List Nat := [1, 1, 3, 1, 6, 2, 1, 1, 3, 3]
def baseStart_3406519 : Nat := 118140960795 + 3406519 * 2 ^ 59
def prefixEnd_3406519 : Nat := 4983230072969 + 3 ^ 40 * 3406519 * 2
def baseEnd_3406519 : Nat := 1166121070448975141630807

theorem tailTrace_3406519 : CollatzResearch.WordTrace tailWord_3406519 prefixEnd_3406519 1166121070448975141630807 := by
  unfold tailWord_3406519
  simp only [CollatzResearch.WordTrace]
  refine ⟨124245955145770924971870611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82830636763847283314580407 124245955145770924971870611)
  ·
    refine ⟨186368932718656387457805917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124245955145770924971870611 186368932718656387457805917)
    ·
      refine ⟨69888349769496145296677219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186368932718656387457805917 69888349769496145296677219)
      ·
        refine ⟨104832524654244217945015829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69888349769496145296677219 104832524654244217945015829)
        ·
          refine ⟨4914024593167697716172617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104832524654244217945015829 4914024593167697716172617)
          ·
            refine ⟨3685518444875773287129463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4914024593167697716172617 3685518444875773287129463)
            ·
              refine ⟨5528277667313659930694195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3685518444875773287129463 5528277667313659930694195)
              ·
                refine ⟨8292416500970489896041293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5528277667313659930694195 8292416500970489896041293)
                ·
                  refine ⟨3109656187863933711015485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8292416500970489896041293 3109656187863933711015485)
                  ·
                    refine ⟨1166121070448975141630807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3109656187863933711015485 1166121070448975141630807)
                    ·
                      rfl

theorem cell22_3406519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_3406519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406519 prefixEnd_3406519 := by exact prefixLift 3406519
  have htrace : WordTrace (prefixWord ++ tailWord_3406519) baseStart_3406519 baseEnd_3406519 := by
    simpa [prefixWord, tailWord_3406519, baseEnd_3406519] using wordTrace_append hprefix tailTrace_3406519
  have hstable : (prefixWord ++ tailWord_3406519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406519).length < 2 ^ (prefixWord ++ tailWord_3406519).sum := by decide
  have hdescent : baseEnd_3406519 < baseStart_3406519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406532 : List Nat := [2, 3, 3, 1, 1, 3, 1, 3, 5]
def baseStart_3406532 : Nat := 118140960795 + 3406532 * 2 ^ 59
def prefixEnd_3406532 : Nat := 4983230072969 + 3 ^ 40 * 3406532 * 2
def baseEnd_3406532 : Nat := 388708506871549147018589

theorem tailTrace_3406532 : CollatzResearch.WordTrace tailWord_3406532 prefixEnd_3406532 388708506871549147018589 := by
  unfold tailWord_3406532
  simp only [CollatzResearch.WordTrace]
  refine ⟨62123214647361914096046925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82830952863149218794729233 62123214647361914096046925)
  ·
    refine ⟨23296205492760717786017597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62123214647361914096046925 23296205492760717786017597)
    ·
      refine ⟨8736077059785269169756599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23296205492760717786017597 8736077059785269169756599)
      ·
        refine ⟨13104115589677903754634899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8736077059785269169756599 13104115589677903754634899)
        ·
          refine ⟨19656173384516855631952349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13104115589677903754634899 19656173384516855631952349)
          ·
            refine ⟨7371065019193820861982131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19656173384516855631952349 7371065019193820861982131)
            ·
              refine ⟨11056597528790731292973197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7371065019193820861982131 11056597528790731292973197)
              ·
                refine ⟨4146224073296524234864949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11056597528790731292973197 4146224073296524234864949)
                ·
                  refine ⟨388708506871549147018589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4146224073296524234864949 388708506871549147018589)
                  ·
                    rfl

theorem cell22_3406532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_3406532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406532 prefixEnd_3406532 := by exact prefixLift 3406532
  have htrace : WordTrace (prefixWord ++ tailWord_3406532) baseStart_3406532 baseEnd_3406532 := by
    simpa [prefixWord, tailWord_3406532, baseEnd_3406532] using wordTrace_append hprefix tailTrace_3406532
  have hstable : (prefixWord ++ tailWord_3406532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406532).length < 2 ^ (prefixWord ++ tailWord_3406532).sum := by decide
  have hdescent : baseEnd_3406532 < baseStart_3406532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406545 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 3, 4]
def baseStart_3406545 : Nat := 118140960795 + 3406545 * 2 ^ 59
def prefixEnd_3406545 : Nat := 4983230072969 + 3 ^ 40 * 3406545 * 2
def baseEnd_3406545 : Nat := 1166129970780319740480727

theorem tailTrace_3406545 : CollatzResearch.WordTrace tailWord_3406545 prefixEnd_3406545 1166129970780319740480727 := by
  unfold tailWord_3406545
  simp only [CollatzResearch.WordTrace]
  refine ⟨124246903443676731412317089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82831268962451154274878059 124246903443676731412317089)
  ·
    refine ⟨93185177582757548559237817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124246903443676731412317089 93185177582757548559237817)
    ·
      refine ⟨69888883187068161419428363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93185177582757548559237817 69888883187068161419428363)
      ·
        refine ⟨104833324780602242129142545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69888883187068161419428363 104833324780602242129142545)
        ·
          refine ⟨78624993585451681596856909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104833324780602242129142545 78624993585451681596856909)
          ·
            refine ⟨29484372594544380598821341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78624993585451681596856909 29484372594544380598821341)
            ·
              refine ⟨11056639722954142724558003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29484372594544380598821341 11056639722954142724558003)
              ·
                refine ⟨16584959584431214086837005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11056639722954142724558003 16584959584431214086837005)
                ·
                  refine ⟨6219359844161705282563877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16584959584431214086837005 6219359844161705282563877)
                  ·
                    refine ⟨1166129970780319740480727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6219359844161705282563877 1166129970780319740480727)
                    ·
                      rfl

theorem cell22_3406545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_3406545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406545 prefixEnd_3406545 := by exact prefixLift 3406545
  have htrace : WordTrace (prefixWord ++ tailWord_3406545) baseStart_3406545 baseEnd_3406545 := by
    simpa [prefixWord, tailWord_3406545, baseEnd_3406545] using wordTrace_append hprefix tailTrace_3406545
  have hstable : (prefixWord ++ tailWord_3406545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406545).length < 2 ^ (prefixWord ++ tailWord_3406545).sum := by decide
  have hdescent : baseEnd_3406545 < baseStart_3406545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406577 : List Nat := [1, 2, 2, 2, 2, 2, 3, 4, 4]
def baseStart_3406577 : Nat := 118140960795 + 3406577 * 2 ^ 59
def prefixEnd_3406577 : Nat := 4983230072969 + 3 ^ 40 * 3406577 * 2
def baseEnd_3406577 : Nat := 388713641678094107893543

theorem tailTrace_3406577 : CollatzResearch.WordTrace tailWord_3406577 prefixEnd_3406577 388713641678094107893543 := by
  unfold tailWord_3406577
  simp only [CollatzResearch.WordTrace]
  refine ⟨124248070579560800877481985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82832047053040533918321323 124248070579560800877481985)
  ·
    refine ⟨93186052934670600658111489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124248070579560800877481985 93186052934670600658111489)
    ·
      refine ⟨69889539701002950493583617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93186052934670600658111489 69889539701002950493583617)
      ·
        refine ⟨52417154775752212870187713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69889539701002950493583617 52417154775752212870187713)
        ·
          refine ⟨39312866081814159652640785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52417154775752212870187713 39312866081814159652640785)
          ·
            refine ⟨29484649561360619739480589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39312866081814159652640785 29484649561360619739480589)
            ·
              refine ⟨11056743585510232402305221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29484649561360619739480589 11056743585510232402305221)
              ·
                refine ⟨2073139422283168575432229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11056743585510232402305221 2073139422283168575432229)
                ·
                  refine ⟨388713641678094107893543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2073139422283168575432229 388713641678094107893543)
                  ·
                    rfl

theorem cell22_3406577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 4].length) (baseStart_3406577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406577 prefixEnd_3406577 := by exact prefixLift 3406577
  have htrace : WordTrace (prefixWord ++ tailWord_3406577) baseStart_3406577 baseEnd_3406577 := by
    simpa [prefixWord, tailWord_3406577, baseEnd_3406577] using wordTrace_append hprefix tailTrace_3406577
  have hstable : (prefixWord ++ tailWord_3406577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406577).length < 2 ^ (prefixWord ++ tailWord_3406577).sum := by decide
  have hdescent : baseEnd_3406577 < baseStart_3406577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406581 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 2, 5]
def baseStart_3406581 : Nat := 118140960795 + 3406581 * 2 ^ 59
def prefixEnd_3406581 : Nat := 4983230072969 + 3 ^ 40 * 3406581 * 2
def baseEnd_3406581 : Nat := 1166142294316027646580617

theorem tailTrace_3406581 : CollatzResearch.WordTrace tailWord_3406581 prefixEnd_3406581 1166142294316027646580617 := by
  unfold tailWord_3406581
  simp only [CollatzResearch.WordTrace]
  refine ⟨124248216471546309560627597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82832144314364206373751731 124248216471546309560627597)
  ·
    refine ⟨46593081176829866085235349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124248216471546309560627597 46593081176829866085235349)
    ·
      refine ⟨2184050680163899972745407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46593081176829866085235349 2184050680163899972745407)
      ·
        refine ⟨3276076020245849959118111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2184050680163899972745407 3276076020245849959118111)
        ·
          refine ⟨4914114030368774938677167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3276076020245849959118111 4914114030368774938677167)
          ·
            refine ⟨7371171045553162408015751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4914114030368774938677167 7371171045553162408015751)
            ·
              refine ⟨11056756568329743612023627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7371171045553162408015751 11056756568329743612023627)
              ·
                refine ⟨16585134852494615418035441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11056756568329743612023627 16585134852494615418035441)
                ·
                  refine ⟨12438851139370961563526581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16585134852494615418035441 12438851139370961563526581)
                  ·
                    refine ⟨1166142294316027646580617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12438851139370961563526581 1166142294316027646580617)
                    ·
                      rfl

theorem cell22_3406581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_3406581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406581 prefixEnd_3406581 := by exact prefixLift 3406581
  have htrace : WordTrace (prefixWord ++ tailWord_3406581) baseStart_3406581 baseEnd_3406581 := by
    simpa [prefixWord, tailWord_3406581, baseEnd_3406581] using wordTrace_append hprefix tailTrace_3406581
  have hstable : (prefixWord ++ tailWord_3406581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406581).length < 2 ^ (prefixWord ++ tailWord_3406581).sum := by decide
  have hdescent : baseEnd_3406581 < baseStart_3406581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406626 : List Nat := [3, 3, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_3406626 : Nat := 118140960795 + 3406626 * 2 ^ 59
def prefixEnd_3406626 : Nat := 4983230072969 + 3 ^ 40 * 3406626 * 2
def baseEnd_3406626 : Nat := 1166157698735662529205479

theorem tailTrace_3406626 : CollatzResearch.WordTrace tailWord_3406626 prefixEnd_3406626 1166157698735662529205479 := by
  unfold tailWord_3406626
  simp only [CollatzResearch.WordTrace]
  refine ⟨31062464439095820561503933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82833238504255521497343821 31062464439095820561503933)
  ·
    refine ⟨11648424164660932710563975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31062464439095820561503933 11648424164660932710563975)
    ·
      refine ⟨17472636246991399065845963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11648424164660932710563975 17472636246991399065845963)
      ·
        refine ⟨26208954370487098598768945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17472636246991399065845963 26208954370487098598768945)
        ·
          refine ⟨19656715777865323949076709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26208954370487098598768945 19656715777865323949076709)
          ·
            refine ⟨3685634208349748240451883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19656715777865323949076709 3685634208349748240451883)
            ·
              refine ⟨5528451312524622360677825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3685634208349748240451883 5528451312524622360677825)
              ·
                refine ⟨4146338484393466770508369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5528451312524622360677825 4146338484393466770508369)
                ·
                  refine ⟨3109753863295100077881277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4146338484393466770508369 3109753863295100077881277)
                  ·
                    refine ⟨1166157698735662529205479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3109753863295100077881277 1166157698735662529205479)
                    ·
                      rfl

theorem cell22_3406626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_3406626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406626 prefixEnd_3406626 := by exact prefixLift 3406626
  have htrace : WordTrace (prefixWord ++ tailWord_3406626) baseStart_3406626 baseEnd_3406626 := by
    simpa [prefixWord, tailWord_3406626, baseEnd_3406626] using wordTrace_append hprefix tailTrace_3406626
  have hstable : (prefixWord ++ tailWord_3406626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406626).length < 2 ^ (prefixWord ++ tailWord_3406626).sum := by decide
  have hdescent : baseEnd_3406626 < baseStart_3406626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406727 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 3, 5]
def baseStart_3406727 : Nat := 118140960795 + 3406727 * 2 ^ 59
def prefixEnd_3406727 : Nat := 4983230072969 + 3 ^ 40 * 3406727 * 2
def baseEnd_3406727 : Nat := 1166192273099731932430169

theorem tailTrace_3406727 : CollatzResearch.WordTrace tailWord_3406727 prefixEnd_3406727 1166192273099731932430169 := by
  unfold tailWord_3406727
  simp only [CollatzResearch.WordTrace]
  refine ⟨124253541529017376495442435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82835694352678250996961623 124253541529017376495442435)
  ·
    refine ⟨186380312293526064743163653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124253541529017376495442435 186380312293526064743163653)
    ·
      refine ⟨34946308555036137139343185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186380312293526064743163653 34946308555036137139343185)
      ·
        refine ⟨26209731416277102854507389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34946308555036137139343185 26209731416277102854507389)
        ·
          refine ⟨9828649281103913570440271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26209731416277102854507389 9828649281103913570440271)
          ·
            refine ⟨14742973921655870355660407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9828649281103913570440271 14742973921655870355660407)
            ·
              refine ⟨22114460882483805533490611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14742973921655870355660407 22114460882483805533490611)
              ·
                refine ⟨33171691323725708300235917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22114460882483805533490611 33171691323725708300235917)
                ·
                  refine ⟨12439384246397140612588469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33171691323725708300235917 12439384246397140612588469)
                  ·
                    refine ⟨1166192273099731932430169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12439384246397140612588469 1166192273099731932430169)
                    ·
                      rfl

theorem cell22_3406727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_3406727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406727 prefixEnd_3406727 := by exact prefixLift 3406727
  have htrace : WordTrace (prefixWord ++ tailWord_3406727) baseStart_3406727 baseEnd_3406727 := by
    simpa [prefixWord, tailWord_3406727, baseEnd_3406727] using wordTrace_append hprefix tailTrace_3406727
  have hstable : (prefixWord ++ tailWord_3406727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406727).length < 2 ^ (prefixWord ++ tailWord_3406727).sum := by decide
  have hdescent : baseEnd_3406727 < baseStart_3406727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406746 : List Nat := [3, 1, 1, 4, 3, 1, 1, 4, 4]
def baseStart_3406746 : Nat := 118140960795 + 3406746 * 2 ^ 59
def prefixEnd_3406746 : Nat := 4983230072969 + 3 ^ 40 * 3406746 * 2
def baseEnd_3406746 : Nat := 388732925729340738735037

theorem tailTrace_3406746 : CollatzResearch.WordTrace tailWord_3406746 prefixEnd_3406746 388732925729340738735037 := by
  unfold tailWord_3406746
  simp only [CollatzResearch.WordTrace]
  refine ⟨31063558628987135685096023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82836156343965695160256061 31063558628987135685096023)
  ·
    refine ⟨46595337943480703527644035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31063558628987135685096023 46595337943480703527644035)
    ·
      refine ⟨69893006915221055291466053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46595337943480703527644035 69893006915221055291466053)
      ·
        refine ⟨13104938796603947867149885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69893006915221055291466053 13104938796603947867149885)
        ·
          refine ⟨4914352048726480450181207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13104938796603947867149885 4914352048726480450181207)
          ·
            refine ⟨7371528073089720675271811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4914352048726480450181207 7371528073089720675271811)
            ·
              refine ⟨11057292109634581012907717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7371528073089720675271811 11057292109634581012907717)
              ·
                refine ⟨2073242270556483939920197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11057292109634581012907717 2073242270556483939920197)
                ·
                  refine ⟨388732925729340738735037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2073242270556483939920197 388732925729340738735037)
                  ·
                    rfl

theorem cell22_3406746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 4].length) (baseStart_3406746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406746 prefixEnd_3406746 := by exact prefixLift 3406746
  have htrace : WordTrace (prefixWord ++ tailWord_3406746) baseStart_3406746 baseEnd_3406746 := by
    simpa [prefixWord, tailWord_3406746, baseEnd_3406746] using wordTrace_append hprefix tailTrace_3406746
  have hstable : (prefixWord ++ tailWord_3406746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406746).length < 2 ^ (prefixWord ++ tailWord_3406746).sum := by decide
  have hdescent : baseEnd_3406746 < baseStart_3406746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406892 : List Nat := [2, 2, 1, 1, 1, 2, 3, 10]
def baseStart_3406892 : Nat := 118140960795 + 3406892 * 2 ^ 59
def prefixEnd_3406892 : Nat := 4983230072969 + 3 ^ 40 * 3406892 * 2
def baseEnd_3406892 : Nat := 129583195107969611339407

theorem tailTrace_3406892 : CollatzResearch.WordTrace tailWord_3406892 prefixEnd_3406892 129583195107969611339407 := by
  unfold tailWord_3406892
  simp only [CollatzResearch.WordTrace]
  refine ⟨62129779786709804837599465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82839706382279739783465953 62129779786709804837599465)
  ·
    refine ⟨46597334840032353628199599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62129779786709804837599465 46597334840032353628199599)
    ·
      refine ⟨69896002260048530442299399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46597334840032353628199599 69896002260048530442299399)
      ·
        refine ⟨104844003390072795663449099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69896002260048530442299399 104844003390072795663449099)
        ·
          refine ⟨157266005085109193495173649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104844003390072795663449099 157266005085109193495173649)
          ·
            refine ⟨117949503813831895121380237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157266005085109193495173649 117949503813831895121380237)
            ·
              refine ⟨44231063930186960670517589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117949503813831895121380237 44231063930186960670517589)
              ·
                refine ⟨129583195107969611339407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44231063930186960670517589 129583195107969611339407)
                ·
                  rfl

theorem cell22_3406892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 10].length) (baseStart_3406892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406892 prefixEnd_3406892 := by exact prefixLift 3406892
  have htrace : WordTrace (prefixWord ++ tailWord_3406892) baseStart_3406892 baseEnd_3406892 := by
    simpa [prefixWord, tailWord_3406892, baseEnd_3406892] using wordTrace_append hprefix tailTrace_3406892
  have hstable : (prefixWord ++ tailWord_3406892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406892).length < 2 ^ (prefixWord ++ tailWord_3406892).sum := by decide
  have hdescent : baseEnd_3406892 < baseStart_3406892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406900 : List Nat := [2, 5, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_3406900 : Nat := 118140960795 + 3406900 * 2 ^ 59
def prefixEnd_3406900 : Nat := 4983230072969 + 3 ^ 40 * 3406900 * 2
def baseEnd_3406900 : Nat := 1166251494535217147854639

theorem tailTrace_3406900 : CollatzResearch.WordTrace tailWord_3406900 prefixEnd_3406900 1166251494535217147854639 := by
  unfold tailWord_3406900
  simp only [CollatzResearch.WordTrace]
  refine ⟨62129925678695313520745077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82839900904927084694326769 62129925678695313520745077)
  ·
    refine ⟨5824680532377685642569851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62129925678695313520745077 5824680532377685642569851)
    ·
      refine ⟨8737020798566528463854777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5824680532377685642569851 8737020798566528463854777)
      ·
        refine ⟨6552765598924896347891083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8737020798566528463854777 6552765598924896347891083)
        ·
          refine ⟨9829148398387344521836625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6552765598924896347891083 9829148398387344521836625)
          ·
            refine ⟨7371861298790508391377469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9829148398387344521836625 7371861298790508391377469)
            ·
              refine ⟨2764447987046440646766551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7371861298790508391377469 2764447987046440646766551)
              ·
                refine ⟨4146671980569660970149827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2764447987046440646766551 4146671980569660970149827)
                ·
                  refine ⟨6220007970854491455224741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4146671980569660970149827 6220007970854491455224741)
                  ·
                    refine ⟨1166251494535217147854639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6220007970854491455224741 1166251494535217147854639)
                    ·
                      rfl

theorem cell22_3406900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_3406900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3406900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3406900 prefixEnd_3406900 := by exact prefixLift 3406900
  have htrace : WordTrace (prefixWord ++ tailWord_3406900) baseStart_3406900 baseEnd_3406900 := by
    simpa [prefixWord, tailWord_3406900, baseEnd_3406900] using wordTrace_append hprefix tailTrace_3406900
  have hstable : (prefixWord ++ tailWord_3406900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406900).length < 2 ^ (prefixWord ++ tailWord_3406900).sum := by decide
  have hdescent : baseEnd_3406900 < baseStart_3406900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
