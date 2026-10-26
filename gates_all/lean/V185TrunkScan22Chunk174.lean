import V185TrunkScan22Chunk173

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1553675 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 4, 4]
def baseStart_1553675 : Nat := 118140960795 + 1553675 * 2 ^ 59
def prefixEnd_1553675 : Nat := 4983230072969 + 3 ^ 40 * 1553675 * 2
def baseEnd_1553675 : Nat := 531854703916209315411523

theorem tailTrace_1553675 : CollatzResearch.WordTrace tailWord_1553675 prefixEnd_1553675 531854703916209315411523 := by
  unfold tailWord_1553675
  simp only [CollatzResearch.WordTrace]
  refine ⟨56667182646308296409790479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37778121764205530939860319 56667182646308296409790479)
  ·
    refine ⟨85000773969462444614685719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56667182646308296409790479 85000773969462444614685719)
    ·
      refine ⟨127501160954193666922028579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85000773969462444614685719 127501160954193666922028579)
      ·
        refine ⟨191251741431290500383042869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127501160954193666922028579 191251741431290500383042869)
        ·
          refine ⟨17929850759183484410910269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191251741431290500383042869 17929850759183484410910269)
          ·
            refine ⟨6723694034693806654091351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17929850759183484410910269 6723694034693806654091351)
            ·
              refine ⟨10085541052040709981137027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6723694034693806654091351 10085541052040709981137027)
              ·
                refine ⟨15128311578061064971705541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10085541052040709981137027 15128311578061064971705541)
                ·
                  refine ⟨2836558420886449682194789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15128311578061064971705541 2836558420886449682194789)
                  ·
                    refine ⟨531854703916209315411523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2836558420886449682194789 531854703916209315411523)
                    ·
                      rfl

theorem cell22_1553675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 4].length) (baseStart_1553675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553675 prefixEnd_1553675 := by exact prefixLift 1553675
  have htrace : WordTrace (prefixWord ++ tailWord_1553675) baseStart_1553675 baseEnd_1553675 := by
    simpa [prefixWord, tailWord_1553675, baseEnd_1553675] using wordTrace_append hprefix tailTrace_1553675
  have hstable : (prefixWord ++ tailWord_1553675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553675).length < 2 ^ (prefixWord ++ tailWord_1553675).sum := by decide
  have hdescent : baseEnd_1553675 < baseStart_1553675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553690 : List Nat := [3, 1, 1, 3, 3, 1, 1, 9]
def baseStart_1553690 : Nat := 118140960795 + 1553690 * 2 ^ 59
def prefixEnd_1553690 : Nat := 4983230072969 + 3 ^ 40 * 1553690 * 2
def baseEnd_1553690 : Nat := 59095537635861586254053

theorem tailTrace_1553690 : CollatzResearch.WordTrace tailWord_1553690 prefixEnd_1553690 59095537635861586254053 := by
  unfold tailWord_1553690
  simp only [CollatzResearch.WordTrace]
  refine ⟨14166932435313488492896631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37778486494169302647724349 14166932435313488492896631)
  ·
    refine ⟨21250398652970232739344947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14166932435313488492896631 21250398652970232739344947)
    ·
      refine ⟨31875597979455349109017421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21250398652970232739344947 31875597979455349109017421)
      ·
        refine ⟨11953349242295755915881533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31875597979455349109017421 11953349242295755915881533)
        ·
          refine ⟨4482505965860908468455575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11953349242295755915881533 4482505965860908468455575)
          ·
            refine ⟨6723758948791362702683363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4482505965860908468455575 6723758948791362702683363)
            ·
              refine ⟨10085638423187044054025045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6723758948791362702683363 10085638423187044054025045)
              ·
                refine ⟨59095537635861586254053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10085638423187044054025045 59095537635861586254053)
                ·
                  rfl

theorem cell22_1553690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 9].length) (baseStart_1553690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553690 prefixEnd_1553690 := by exact prefixLift 1553690
  have htrace : WordTrace (prefixWord ++ tailWord_1553690) baseStart_1553690 baseEnd_1553690 := by
    simpa [prefixWord, tailWord_1553690, baseEnd_1553690] using wordTrace_append hprefix tailTrace_1553690
  have hstable : (prefixWord ++ tailWord_1553690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553690).length < 2 ^ (prefixWord ++ tailWord_1553690).sum := by decide
  have hdescent : baseEnd_1553690 < baseStart_1553690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553709 : List Nat := [1, 5, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_1553709 : Nat := 118140960795 + 1553709 * 2 ^ 59
def prefixEnd_1553709 : Nat := 4983230072969 + 3 ^ 40 * 1553709 * 2
def baseEnd_1553709 : Nat := 531866342811044560061419

theorem tailTrace_1553709 : CollatzResearch.WordTrace tailWord_1553709 prefixEnd_1553709 531866342811044560061419 := by
  unfold tailWord_1553709
  simp only [CollatzResearch.WordTrace]
  refine ⟨56668422728185120216528181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37778948485456746811018787 56668422728185120216528181)
  ·
    refine ⟨5312664630767355020299517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56668422728185120216528181 5312664630767355020299517)
    ·
      refine ⟨1992249236537758132612319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5312664630767355020299517 1992249236537758132612319)
      ·
        refine ⟨2988373854806637198918479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1992249236537758132612319 2988373854806637198918479)
        ·
          refine ⟨4482560782209955798377719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2988373854806637198918479 4482560782209955798377719)
          ·
            refine ⟨6723841173314933697566579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4482560782209955798377719 6723841173314933697566579)
            ·
              refine ⟨10085761759972400546349869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6723841173314933697566579 10085761759972400546349869)
              ·
                refine ⟨3782160659989650204881201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10085761759972400546349869 3782160659989650204881201)
                ·
                  refine ⟨2836620494992237653660901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3782160659989650204881201 2836620494992237653660901)
                  ·
                    refine ⟨531866342811044560061419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2836620494992237653660901 531866342811044560061419)
                    ·
                      rfl

theorem cell22_1553709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_1553709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553709 prefixEnd_1553709 := by exact prefixLift 1553709
  have htrace : WordTrace (prefixWord ++ tailWord_1553709) baseStart_1553709 baseEnd_1553709 := by
    simpa [prefixWord, tailWord_1553709, baseEnd_1553709] using wordTrace_append hprefix tailTrace_1553709
  have hstable : (prefixWord ++ tailWord_1553709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553709).length < 2 ^ (prefixWord ++ tailWord_1553709).sum := by decide
  have hdescent : baseEnd_1553709 < baseStart_1553709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553741 : List Nat := [1, 6, 1, 3, 1, 2, 1, 7]
def baseStart_1553741 : Nat := 118140960795 + 1553741 * 2 ^ 59
def prefixEnd_1553741 : Nat := 4983230072969 + 3 ^ 40 * 1553741 * 2
def baseEnd_1553741 : Nat := 59097477451667460362369

theorem tailTrace_1553741 : CollatzResearch.WordTrace tailWord_1553741 prefixEnd_1553741 59097477451667460362369 := by
  unfold tailWord_1553741
  simp only [CollatzResearch.WordTrace]
  refine ⟨56669589864069189681693077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37779726576046126454462051 56669589864069189681693077)
  ·
    refine ⟨2656387024878243266329363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56669589864069189681693077 2656387024878243266329363)
    ·
      refine ⟨3984580537317364899494045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2656387024878243266329363 3984580537317364899494045)
      ·
        refine ⟨1494217701494011837310267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3984580537317364899494045 1494217701494011837310267)
        ·
          refine ⟨2241326552241017755965401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1494217701494011837310267 2241326552241017755965401)
          ·
            refine ⟨1680994914180763316974051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2241326552241017755965401 1680994914180763316974051)
            ·
              refine ⟨2521492371271144975461077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1680994914180763316974051 2521492371271144975461077)
              ·
                refine ⟨59097477451667460362369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2521492371271144975461077 59097477451667460362369)
                ·
                  rfl

theorem cell22_1553741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 7].length) (baseStart_1553741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553741 prefixEnd_1553741 := by exact prefixLift 1553741
  have htrace : WordTrace (prefixWord ++ tailWord_1553741) baseStart_1553741 baseEnd_1553741 := by
    simpa [prefixWord, tailWord_1553741, baseEnd_1553741] using wordTrace_append hprefix tailTrace_1553741
  have hstable : (prefixWord ++ tailWord_1553741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553741).length < 2 ^ (prefixWord ++ tailWord_1553741).sum := by decide
  have hdescent : baseEnd_1553741 < baseStart_1553741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553816 : List Nat := [2, 1, 2, 5, 2, 1, 2, 2, 1, 4]
def baseStart_1553816 : Nat := 118140960795 + 1553816 * 2 ^ 59
def prefixEnd_1553816 : Nat := 4983230072969 + 3 ^ 40 * 1553816 * 2
def baseEnd_1553816 : Nat := 531902971097731947636091

theorem tailTrace_1553816 : CollatzResearch.WordTrace tailWord_1553816 prefixEnd_1553816 531902971097731947636091 := by
  unfold tailWord_1553816
  simp only [CollatzResearch.WordTrace]
  refine ⟨28336162669398738745336651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37781550225864984993782201 28336162669398738745336651)
  ·
    refine ⟨42504244004098108118004977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28336162669398738745336651 42504244004098108118004977)
    ·
      refine ⟨31878183003073581088503733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42504244004098108118004977 31878183003073581088503733)
      ·
        refine ⟨2988579656538148227047225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31878183003073581088503733 2988579656538148227047225)
        ·
          refine ⟨2241434742403611170285419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2988579656538148227047225 2241434742403611170285419)
          ·
            refine ⟨3362152113605416755428129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2241434742403611170285419 3362152113605416755428129)
            ·
              refine ⟨2521614085204062566571097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3362152113605416755428129 2521614085204062566571097)
              ·
                refine ⟨1891210563903046924928323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2521614085204062566571097 1891210563903046924928323)
                ·
                  refine ⟨2836815845854570387392485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1891210563903046924928323 2836815845854570387392485)
                  ·
                    refine ⟨531902971097731947636091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2836815845854570387392485 531902971097731947636091)
                    ·
                      rfl

theorem cell22_1553816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_1553816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553816 prefixEnd_1553816 := by exact prefixLift 1553816
  have htrace : WordTrace (prefixWord ++ tailWord_1553816) baseStart_1553816 baseEnd_1553816 := by
    simpa [prefixWord, tailWord_1553816, baseEnd_1553816] using wordTrace_append hprefix tailTrace_1553816
  have hstable : (prefixWord ++ tailWord_1553816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553816).length < 2 ^ (prefixWord ++ tailWord_1553816).sum := by decide
  have hdescent : baseEnd_1553816 < baseStart_1553816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553827 : List Nat := [1, 1, 1, 4, 1, 3, 2, 3, 2, 4]
def baseStart_1553827 : Nat := 118140960795 + 1553827 * 2 ^ 59
def prefixEnd_1553827 : Nat := 4983230072969 + 3 ^ 40 * 1553827 * 2
def baseEnd_1553827 : Nat := 531906736622531585611057

theorem tailTrace_1553827 : CollatzResearch.WordTrace tailWord_1553827 prefixEnd_1553827 531906736622531585611057 := by
  unfold tailWord_1553827
  simp only [CollatzResearch.WordTrace]
  refine ⟨56672726541757626369323735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37781817694505084246215823 56672726541757626369323735)
  ·
    refine ⟨85009089812636439553985603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56672726541757626369323735 85009089812636439553985603)
    ·
      refine ⟨127513634718954659330978405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85009089812636439553985603 127513634718954659330978405)
      ·
        refine ⟨23908806509803998624558451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127513634718954659330978405 23908806509803998624558451)
        ·
          refine ⟨35863209764705997936837677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23908806509803998624558451 35863209764705997936837677)
          ·
            refine ⟨13448703661764749226314129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35863209764705997936837677 13448703661764749226314129)
            ·
              refine ⟨10086527746323561919735597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13448703661764749226314129 10086527746323561919735597)
              ·
                refine ⟨3782447904871335719900849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10086527746323561919735597 3782447904871335719900849)
                ·
                  refine ⟨2836835928653501789925637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3782447904871335719900849 2836835928653501789925637)
                  ·
                    refine ⟨531906736622531585611057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2836835928653501789925637 531906736622531585611057)
                    ·
                      rfl

theorem cell22_1553827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 4].length) (baseStart_1553827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553827 prefixEnd_1553827 := by exact prefixLift 1553827
  have htrace : WordTrace (prefixWord ++ tailWord_1553827) baseStart_1553827 baseEnd_1553827 := by
    simpa [prefixWord, tailWord_1553827, baseEnd_1553827] using wordTrace_append hprefix tailTrace_1553827
  have hstable : (prefixWord ++ tailWord_1553827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553827).length < 2 ^ (prefixWord ++ tailWord_1553827).sum := by decide
  have hdescent : baseEnd_1553827 < baseStart_1553827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553904 : List Nat := [2, 1, 1, 1, 3, 5, 2, 2, 5]
def baseStart_1553904 : Nat := 118140960795 + 1553904 * 2 ^ 59
def prefixEnd_1553904 : Nat := 4983230072969 + 3 ^ 40 * 1553904 * 2
def baseEnd_1553904 : Nat := 177311031765376350478607

theorem tailTrace_1553904 : CollatzResearch.WordTrace tailWord_1553904 prefixEnd_1553904 177311031765376350478607 := by
  unfold tailWord_1553904
  simp only [CollatzResearch.WordTrace]
  refine ⟨28337767481239334259938383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37783689974985779013251177 28337767481239334259938383)
  ·
    refine ⟨42506651221859001389907575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28337767481239334259938383 42506651221859001389907575)
    ·
      refine ⟨63759976832788502084861363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42506651221859001389907575 63759976832788502084861363)
      ·
        refine ⟨95639965249182753127292045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63759976832788502084861363 95639965249182753127292045)
        ·
          refine ⟨35864986968443532422734517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95639965249182753127292045 35864986968443532422734517)
          ·
            refine ⟨3362342528291581164631361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35864986968443532422734517 3362342528291581164631361)
            ·
              refine ⟨2521756896218685873473521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3362342528291581164631361 2521756896218685873473521)
              ·
                refine ⟨1891317672164014405105141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2521756896218685873473521 1891317672164014405105141)
                ·
                  refine ⟨177311031765376350478607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1891317672164014405105141 177311031765376350478607)
                  ·
                    rfl

theorem cell22_1553904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 5].length) (baseStart_1553904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553904 prefixEnd_1553904 := by exact prefixLift 1553904
  have htrace : WordTrace (prefixWord ++ tailWord_1553904) baseStart_1553904 baseEnd_1553904 := by
    simpa [prefixWord, tailWord_1553904, baseEnd_1553904] using wordTrace_append hprefix tailTrace_1553904
  have hstable : (prefixWord ++ tailWord_1553904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553904).length < 2 ^ (prefixWord ++ tailWord_1553904).sum := by decide
  have hdescent : baseEnd_1553904 < baseStart_1553904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553951 : List Nat := [1, 1, 2, 4, 1, 1, 6, 1, 1, 4]
def baseStart_1553951 : Nat := 118140960795 + 1553951 * 2 ^ 59
def prefixEnd_1553951 : Nat := 4983230072969 + 3 ^ 40 * 1553951 * 2
def baseEnd_1553951 : Nat := 531949184356636595510677

theorem tailTrace_1553951 : CollatzResearch.WordTrace tailWord_1553951 prefixEnd_1553951 531949184356636595510677 := by
  unfold tailWord_1553951
  simp only [CollatzResearch.WordTrace]
  refine ⟨56677249193308395546837707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37784832795538930364558471 56677249193308395546837707)
  ·
    refine ⟨85015873789962593320256561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56677249193308395546837707 85015873789962593320256561)
    ·
      refine ⟨63761905342471944990192421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85015873789962593320256561 63761905342471944990192421)
      ·
        refine ⟨11955357251713489685661079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63761905342471944990192421 11955357251713489685661079)
        ·
          refine ⟨17933035877570234528491619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11955357251713489685661079 17933035877570234528491619)
          ·
            refine ⟨26899553816355351792737429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17933035877570234528491619 26899553816355351792737429)
            ·
              refine ⟨1260916585141657115284567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26899553816355351792737429 1260916585141657115284567)
              ·
                refine ⟨1891374877712485672926851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1260916585141657115284567 1891374877712485672926851)
                ·
                  refine ⟨2837062316568728509390277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1891374877712485672926851 2837062316568728509390277)
                  ·
                    refine ⟨531949184356636595510677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2837062316568728509390277 531949184356636595510677)
                    ·
                      rfl

theorem cell22_1553951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 1, 4].length) (baseStart_1553951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553951 prefixEnd_1553951 := by exact prefixLift 1553951
  have htrace : WordTrace (prefixWord ++ tailWord_1553951) baseStart_1553951 baseEnd_1553951 := by
    simpa [prefixWord, tailWord_1553951, baseEnd_1553951] using wordTrace_append hprefix tailTrace_1553951
  have hstable : (prefixWord ++ tailWord_1553951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553951).length < 2 ^ (prefixWord ++ tailWord_1553951).sum := by decide
  have hdescent : baseEnd_1553951 < baseStart_1553951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553966 : List Nat := [4, 1, 3, 1, 2, 2, 2, 1, 6]
def baseStart_1553966 : Nat := 118140960795 + 1553966 * 2 ^ 59
def prefixEnd_1553966 : Nat := 4983230072969 + 3 ^ 40 * 1553966 * 2
def baseEnd_1553966 : Nat := 177318106387727185461877

theorem tailTrace_1553966 : CollatzResearch.WordTrace tailWord_1553966 prefixEnd_1553966 177318106387727185461877 := by
  unfold tailWord_1553966
  simp only [CollatzResearch.WordTrace]
  refine ⟨7084724536031756638579219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37785197525502702072422501 7084724536031756638579219)
  ·
    refine ⟨10627086804047634957868829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7084724536031756638579219 10627086804047634957868829)
    ·
      refine ⟨3985157551517863109200811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10627086804047634957868829 3985157551517863109200811)
      ·
        refine ⟨5977736327276794663801217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3985157551517863109200811 5977736327276794663801217)
        ·
          refine ⟨4483302245457595997850913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5977736327276794663801217 4483302245457595997850913)
          ·
            refine ⟨3362476684093196998388185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4483302245457595997850913 3362476684093196998388185)
            ·
              refine ⟨2521857513069897748791139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3362476684093196998388185 2521857513069897748791139)
              ·
                refine ⟨3782786269604846623186709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2521857513069897748791139 3782786269604846623186709)
                ·
                  refine ⟨177318106387727185461877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3782786269604846623186709 177318106387727185461877)
                  ·
                    rfl

theorem cell22_1553966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_1553966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553966 prefixEnd_1553966 := by exact prefixLift 1553966
  have htrace : WordTrace (prefixWord ++ tailWord_1553966) baseStart_1553966 baseEnd_1553966 := by
    simpa [prefixWord, tailWord_1553966, baseEnd_1553966] using wordTrace_append hprefix tailTrace_1553966
  have hstable : (prefixWord ++ tailWord_1553966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553966).length < 2 ^ (prefixWord ++ tailWord_1553966).sum := by decide
  have hdescent : baseEnd_1553966 < baseStart_1553966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554009 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 5, 3]
def baseStart_1554009 : Nat := 118140960795 + 1554009 * 2 ^ 59
def prefixEnd_1554009 : Nat := 4983230072969 + 3 ^ 40 * 1554009 * 2
def baseEnd_1554009 : Nat := 531969038941943777560499

theorem tailTrace_1554009 : CollatzResearch.WordTrace tailWord_1554009 prefixEnd_1554009 531969038941943777560499 := by
  unfold tailWord_1554009
  simp only [CollatzResearch.WordTrace]
  refine ⟨56679364627098271452449081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37786243084732180968299387 56679364627098271452449081)
  ·
    refine ⟨42509523470323703589336811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56679364627098271452449081 42509523470323703589336811)
    ·
      refine ⟨63764285205485555384005217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42509523470323703589336811 63764285205485555384005217)
      ·
        refine ⟨47823213904114166538003913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63764285205485555384005217 47823213904114166538003913)
        ·
          refine ⟨35867410428085624903502935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47823213904114166538003913 35867410428085624903502935)
          ·
            refine ⟨53801115642128437355254403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35867410428085624903502935 53801115642128437355254403)
            ·
              refine ⟨80701673463192656032881605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53801115642128437355254403 80701673463192656032881605)
              ·
                refine ⟨15131563774348623006165301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80701673463192656032881605 15131563774348623006165301)
                ·
                  refine ⟨1418584103845183406827997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15131563774348623006165301 1418584103845183406827997)
                  ·
                    refine ⟨531969038941943777560499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1418584103845183406827997 531969038941943777560499)
                    ·
                      rfl

theorem cell22_1554009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 3].length) (baseStart_1554009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554009 prefixEnd_1554009 := by exact prefixLift 1554009
  have htrace : WordTrace (prefixWord ++ tailWord_1554009) baseStart_1554009 baseEnd_1554009 := by
    simpa [prefixWord, tailWord_1554009, baseEnd_1554009] using wordTrace_append hprefix tailTrace_1554009
  have hstable : (prefixWord ++ tailWord_1554009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554009).length < 2 ^ (prefixWord ++ tailWord_1554009).sum := by decide
  have hdescent : baseEnd_1554009 < baseStart_1554009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554116 : List Nat := [2, 3, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_1554116 : Nat := 118140960795 + 1554116 * 2 ^ 59
def prefixEnd_1554116 : Nat := 4983230072969 + 3 ^ 40 * 1554116 * 2
def baseEnd_1554116 : Nat := 532005667228631165135171

theorem tailTrace_1554116 : CollatzResearch.WordTrace tailWord_1554116 prefixEnd_1554116 532005667228631165135171 := by
  unfold tailWord_1554116
  simp only [CollatzResearch.WordTrace]
  refine ⟨28341633618855314363297101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37788844825140419151062801 28341633618855314363297101)
  ·
    refine ⟨10628112607070742886236413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28341633618855314363297101 10628112607070742886236413)
    ·
      refine ⟨3985542227651528582338655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10628112607070742886236413 3985542227651528582338655)
      ·
        refine ⟨5978313341477292873507983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3985542227651528582338655 5978313341477292873507983)
        ·
          refine ⟨8967470012215939310261975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5978313341477292873507983 8967470012215939310261975)
          ·
            refine ⟨13451205018323908965392963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8967470012215939310261975 13451205018323908965392963)
            ·
              refine ⟨20176807527485863448089445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13451205018323908965392963 20176807527485863448089445)
              ·
                refine ⟨3783151411403599396516771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20176807527485863448089445 3783151411403599396516771)
                ·
                  refine ⟨5674727117105399094775157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3783151411403599396516771 5674727117105399094775157)
                  ·
                    refine ⟨532005667228631165135171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5674727117105399094775157 532005667228631165135171)
                    ·
                      rfl

theorem cell22_1554116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_1554116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554116 prefixEnd_1554116 := by exact prefixLift 1554116
  have htrace : WordTrace (prefixWord ++ tailWord_1554116) baseStart_1554116 baseEnd_1554116 := by
    simpa [prefixWord, tailWord_1554116, baseEnd_1554116] using wordTrace_append hprefix tailTrace_1554116
  have hstable : (prefixWord ++ tailWord_1554116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554116).length < 2 ^ (prefixWord ++ tailWord_1554116).sum := by decide
  have hdescent : baseEnd_1554116 < baseStart_1554116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554129 : List Nat := [1, 2, 2, 1, 2, 5, 9]
def baseStart_1554129 : Nat := 118140960795 + 1554129 * 2 ^ 59
def prefixEnd_1554129 : Nat := 4983230072969 + 3 ^ 40 * 1554129 * 2
def baseEnd_1554129 : Nat := 19704078422011239428153

theorem tailTrace_1554129 : CollatzResearch.WordTrace tailWord_1554129 prefixEnd_1554129 19704078422011239428153 := by
  unfold tailWord_1554129
  simp only [CollatzResearch.WordTrace]
  refine ⟨56683741386663531946817441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37789160924442354631211627 56683741386663531946817441)
  ·
    refine ⟨42512806039997648960113081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56683741386663531946817441 42512806039997648960113081)
    ·
      refine ⟨31884604529998236720084811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42512806039997648960113081 31884604529998236720084811)
      ·
        refine ⟨47826906794997355080127217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31884604529998236720084811 47826906794997355080127217)
        ·
          refine ⟨35870180096248016310095413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47826906794997355080127217 35870180096248016310095413)
          ·
            refine ⟨3362829384023251529071445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35870180096248016310095413 3362829384023251529071445)
            ·
              refine ⟨19704078422011239428153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3362829384023251529071445 19704078422011239428153)
              ·
                rfl

theorem cell22_1554129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 9].length) (baseStart_1554129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554129 prefixEnd_1554129 := by exact prefixLift 1554129
  have htrace : WordTrace (prefixWord ++ tailWord_1554129) baseStart_1554129 baseEnd_1554129 := by
    simpa [prefixWord, tailWord_1554129, baseEnd_1554129] using wordTrace_append hprefix tailTrace_1554129
  have hstable : (prefixWord ++ tailWord_1554129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554129).length < 2 ^ (prefixWord ++ tailWord_1554129).sum := by decide
  have hdescent : baseEnd_1554129 < baseStart_1554129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554246 : List Nat := [6, 1, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_1554246 : Nat := 118140960795 + 1554246 * 2 ^ 59
def prefixEnd_1554246 : Nat := 4983230072969 + 3 ^ 40 * 1554246 * 2
def baseEnd_1554246 : Nat := 532050168885354159384773

theorem tailTrace_1554246 : CollatzResearch.WordTrace tailWord_1554246 prefixEnd_1554246 532050168885354159384773 := by
  unfold tailWord_1554246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1771500272726239404025831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37792005818159773952551061 1771500272726239404025831)
  ·
    refine ⟨2657250409089359106038747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1771500272726239404025831 2657250409089359106038747)
    ·
      refine ⟨3985875613634038659058121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2657250409089359106038747 3985875613634038659058121)
      ·
        refine ⟨2989406710225528994293591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3985875613634038659058121 2989406710225528994293591)
        ·
          refine ⟨4484110065338293491440387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2989406710225528994293591 4484110065338293491440387)
          ·
            refine ⟨6726165098007440237160581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4484110065338293491440387 6726165098007440237160581)
            ·
              refine ⟨1261155955876395044467609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6726165098007440237160581 1261155955876395044467609)
              ·
                refine ⟨945866966907296283350707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1261155955876395044467609 945866966907296283350707)
                ·
                  refine ⟨1418800450360944425026061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 945866966907296283350707 1418800450360944425026061)
                  ·
                    refine ⟨532050168885354159384773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1418800450360944425026061 532050168885354159384773)
                    ·
                      rfl

theorem cell22_1554246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_1554246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554246 prefixEnd_1554246 := by exact prefixLift 1554246
  have htrace : WordTrace (prefixWord ++ tailWord_1554246) baseStart_1554246 baseEnd_1554246 := by
    simpa [prefixWord, tailWord_1554246, baseEnd_1554246] using wordTrace_append hprefix tailTrace_1554246
  have hstable : (prefixWord ++ tailWord_1554246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554246).length < 2 ^ (prefixWord ++ tailWord_1554246).sum := by decide
  have hdescent : baseEnd_1554246 < baseStart_1554246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554266 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 1, 6]
def baseStart_1554266 : Nat := 118140960795 + 1554266 * 2 ^ 59
def prefixEnd_1554266 : Nat := 4983230072969 + 3 ^ 40 * 1554266 * 2
def baseEnd_1554266 : Nat := 532057015294080773884711

theorem tailTrace_1554266 : CollatzResearch.WordTrace tailWord_1554266 prefixEnd_1554266 532057015294080773884711 := by
  unfold tailWord_1554266
  simp only [CollatzResearch.WordTrace]
  refine ⟨14172184546791801086138663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37792492124778136229703101 14172184546791801086138663)
  ·
    refine ⟨21258276820187701629207995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14172184546791801086138663 21258276820187701629207995)
    ·
      refine ⟨31887415230281552443811993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21258276820187701629207995 31887415230281552443811993)
      ·
        refine ⟨23915561422711164332858995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31887415230281552443811993 23915561422711164332858995)
        ·
          refine ⟨35873342134066746499288493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23915561422711164332858995 35873342134066746499288493)
          ·
            refine ⟨13452503300275029937233185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35873342134066746499288493 13452503300275029937233185)
            ·
              refine ⟨10089377475206272452924889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13452503300275029937233185 10089377475206272452924889)
              ·
                refine ⟨7567033106404704339693667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10089377475206272452924889 7567033106404704339693667)
                ·
                  refine ⟨11350549659607056509540501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7567033106404704339693667 11350549659607056509540501)
                  ·
                    refine ⟨532057015294080773884711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11350549659607056509540501 532057015294080773884711)
                    ·
                      rfl

theorem cell22_1554266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_1554266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554266 prefixEnd_1554266 := by exact prefixLift 1554266
  have htrace : WordTrace (prefixWord ++ tailWord_1554266) baseStart_1554266 baseEnd_1554266 := by
    simpa [prefixWord, tailWord_1554266, baseEnd_1554266] using wordTrace_append hprefix tailTrace_1554266
  have hstable : (prefixWord ++ tailWord_1554266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554266).length < 2 ^ (prefixWord ++ tailWord_1554266).sum := by decide
  have hdescent : baseEnd_1554266 < baseStart_1554266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554302 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_1554302 : Nat := 118140960795 + 1554302 * 2 ^ 59
def prefixEnd_1554302 : Nat := 4983230072969 + 3 ^ 40 * 1554302 * 2
def baseEnd_1554302 : Nat := 532069338829788679984601

theorem tailTrace_1554302 : CollatzResearch.WordTrace tailWord_1554302 prefixEnd_1554302 532069338829788679984601 := by
  unfold tailWord_1554302
  simp only [CollatzResearch.WordTrace]
  refine ⟨7086256401879597811608145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37793367476691188328576773 7086256401879597811608145)
  ·
    refine ⟨5314692301409698358706109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7086256401879597811608145 5314692301409698358706109)
    ·
      refine ⟨1993009613028636884514791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5314692301409698358706109 1993009613028636884514791)
      ·
        refine ⟨2989514419542955326772187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1993009613028636884514791 2989514419542955326772187)
        ·
          refine ⟨4484271629314432990158281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2989514419542955326772187 4484271629314432990158281)
          ·
            refine ⟨3363203721985824742618711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4484271629314432990158281 3363203721985824742618711)
            ·
              refine ⟨5044805582978737113928067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3363203721985824742618711 5044805582978737113928067)
              ·
                refine ⟨7567208374468105670892101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5044805582978737113928067 7567208374468105670892101)
                ·
                  refine ⟨1418851570212769813292269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7567208374468105670892101 1418851570212769813292269)
                  ·
                    refine ⟨532069338829788679984601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1418851570212769813292269 532069338829788679984601)
                    ·
                      rfl

theorem cell22_1554302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_1554302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554302 prefixEnd_1554302 := by exact prefixLift 1554302
  have htrace : WordTrace (prefixWord ++ tailWord_1554302) baseStart_1554302 baseEnd_1554302 := by
    simpa [prefixWord, tailWord_1554302, baseEnd_1554302] using wordTrace_append hprefix tailTrace_1554302
  have hstable : (prefixWord ++ tailWord_1554302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554302).length < 2 ^ (prefixWord ++ tailWord_1554302).sum := by decide
  have hdescent : baseEnd_1554302 < baseStart_1554302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554330 : List Nat := [3, 1, 1, 4, 2, 1, 2, 2, 3, 3]
def baseStart_1554330 : Nat := 118140960795 + 1554330 * 2 ^ 59
def prefixEnd_1554330 : Nat := 4983230072969 + 3 ^ 40 * 1554330 * 2
def baseEnd_1554330 : Nat := 532078923802005940284515

theorem tailTrace_1554330 : CollatzResearch.WordTrace tailWord_1554330 prefixEnd_1554330 532078923802005940284515 := by
  unfold tailWord_1554330
  simp only [CollatzResearch.WordTrace]
  refine ⟨14172768114733835818721111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37794048305956895516589629 14172768114733835818721111)
  ·
    refine ⟨21259152172100753728081667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14172768114733835818721111 21259152172100753728081667)
    ·
      refine ⟨31888728258151130592122501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21259152172100753728081667 31888728258151130592122501)
      ·
        refine ⟨5979136548403336986022969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31888728258151130592122501 5979136548403336986022969)
        ·
          refine ⟨4484352411302502739517227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5979136548403336986022969 4484352411302502739517227)
          ·
            refine ⟨6726528616953754109275841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4484352411302502739517227 6726528616953754109275841)
            ·
              refine ⟨5044896462715315581956881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6726528616953754109275841 5044896462715315581956881)
              ·
                refine ⟨3783672347036486686467661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5044896462715315581956881 3783672347036486686467661)
                ·
                  refine ⟨1418877130138682507425373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3783672347036486686467661 1418877130138682507425373)
                  ·
                    refine ⟨532078923802005940284515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1418877130138682507425373 532078923802005940284515)
                    ·
                      rfl

theorem cell22_1554330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_1554330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554330 prefixEnd_1554330 := by exact prefixLift 1554330
  have htrace : WordTrace (prefixWord ++ tailWord_1554330) baseStart_1554330 baseEnd_1554330 := by
    simpa [prefixWord, tailWord_1554330, baseEnd_1554330] using wordTrace_append hprefix tailTrace_1554330
  have hstable : (prefixWord ++ tailWord_1554330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554330).length < 2 ^ (prefixWord ++ tailWord_1554330).sum := by decide
  have hdescent : baseEnd_1554330 < baseStart_1554330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554341 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 1, 7]
def baseStart_1554341 : Nat := 118140960795 + 1554341 * 2 ^ 59
def prefixEnd_1554341 : Nat := 4983230072969 + 3 ^ 40 * 1554341 * 2
def baseEnd_1554341 : Nat := 532082689326805578259481

theorem tailTrace_1554341 : CollatzResearch.WordTrace tailWord_1554341 prefixEnd_1554341 532082689326805578259481 := by
  unfold tailWord_1554341
  simp only [CollatzResearch.WordTrace]
  refine ⟨56691473661895492153534877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37794315774596994769023251 56691473661895492153534877)
  ·
    refine ⟨21259302623210809557575579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56691473661895492153534877 21259302623210809557575579)
    ·
      refine ⟨31888953934816214336363369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21259302623210809557575579 31888953934816214336363369)
      ·
        refine ⟨23916715451112160752272527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31888953934816214336363369 23916715451112160752272527)
        ·
          refine ⟨35875073176668241128408791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23916715451112160752272527 35875073176668241128408791)
          ·
            refine ⟨53812609765002361692613187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35875073176668241128408791 53812609765002361692613187)
            ·
              refine ⟨80718914647503542538919781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53812609765002361692613187 80718914647503542538919781)
              ·
                refine ⟨15134796496406914226047459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80718914647503542538919781 15134796496406914226047459)
                ·
                  refine ⟨22702194744610371339071189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15134796496406914226047459 22702194744610371339071189)
                  ·
                    refine ⟨532082689326805578259481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22702194744610371339071189 532082689326805578259481)
                    ·
                      rfl

theorem cell22_1554341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_1554341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554341 prefixEnd_1554341 := by exact prefixLift 1554341
  have htrace : WordTrace (prefixWord ++ tailWord_1554341) baseStart_1554341 baseEnd_1554341 := by
    simpa [prefixWord, tailWord_1554341, baseEnd_1554341] using wordTrace_append hprefix tailTrace_1554341
  have hstable : (prefixWord ++ tailWord_1554341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554341).length < 2 ^ (prefixWord ++ tailWord_1554341).sum := by decide
  have hdescent : baseEnd_1554341 < baseStart_1554341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554343 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 7]
def baseStart_1554343 : Nat := 118140960795 + 1554343 * 2 ^ 59
def prefixEnd_1554343 : Nat := 4983230072969 + 3 ^ 40 * 1554343 * 2
def baseEnd_1554343 : Nat := 177361124655892746569825

theorem tailTrace_1554343 : CollatzResearch.WordTrace tailWord_1554343 prefixEnd_1554343 177361124655892746569825 := by
  unfold tailWord_1554343
  simp only [CollatzResearch.WordTrace]
  refine ⟨56691546607888246495107683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37794364405258830996738455 56691546607888246495107683)
  ·
    refine ⟨85037319911832369742661525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56691546607888246495107683 85037319911832369742661525)
    ·
      refine ⟨3986124370867142331687259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85037319911832369742661525 3986124370867142331687259)
      ·
        refine ⟨5979186556300713497530889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3986124370867142331687259 5979186556300713497530889)
        ·
          refine ⟨4484389917225535123148167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5979186556300713497530889 4484389917225535123148167)
          ·
            refine ⟨6726584875838302684722251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4484389917225535123148167 6726584875838302684722251)
            ·
              refine ⟨10089877313757454027083377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6726584875838302684722251 10089877313757454027083377)
              ·
                refine ⟨7567407985318090520312533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10089877313757454027083377 7567407985318090520312533)
                ·
                  refine ⟨177361124655892746569825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7567407985318090520312533 177361124655892746569825)
                  ·
                    rfl

theorem cell22_1554343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 7].length) (baseStart_1554343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554343 prefixEnd_1554343 := by exact prefixLift 1554343
  have htrace : WordTrace (prefixWord ++ tailWord_1554343) baseStart_1554343 baseEnd_1554343 := by
    simpa [prefixWord, tailWord_1554343, baseEnd_1554343] using wordTrace_append hprefix tailTrace_1554343
  have hstable : (prefixWord ++ tailWord_1554343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554343).length < 2 ^ (prefixWord ++ tailWord_1554343).sum := by decide
  have hdescent : baseEnd_1554343 < baseStart_1554343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554364 : List Nat := [2, 2, 2, 5, 1, 2, 1, 1, 3, 3]
def baseStart_1554364 : Nat := 118140960795 + 1554364 * 2 ^ 59
def prefixEnd_1554364 : Nat := 4983230072969 + 3 ^ 40 * 1554364 * 2
def baseEnd_1554364 : Nat := 532090562696841184934411

theorem tailTrace_1554364 : CollatzResearch.WordTrace tailWord_1554364 prefixEnd_1554364 532090562696841184934411 := by
  unfold tailWord_1554364
  simp only [CollatzResearch.WordTrace]
  refine ⟨28346156270406083540811073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37794875027208111387748097 28346156270406083540811073)
  ·
    refine ⟨21259617202804562655608305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28346156270406083540811073 21259617202804562655608305)
    ·
      refine ⟨15944712902103421991706229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21259617202804562655608305 15944712902103421991706229)
      ·
        refine ⟨1494816834572195811722459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15944712902103421991706229 1494816834572195811722459)
        ·
          refine ⟨2242225251858293717583689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1494816834572195811722459 2242225251858293717583689)
          ·
            refine ⟨1681668938893720288187767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2242225251858293717583689 1681668938893720288187767)
            ·
              refine ⟨2522503408340580432281651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1681668938893720288187767 2522503408340580432281651)
              ·
                refine ⟨3783755112510870648422477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2522503408340580432281651 3783755112510870648422477)
                ·
                  refine ⟨1418908167191576493158429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3783755112510870648422477 1418908167191576493158429)
                  ·
                    refine ⟨532090562696841184934411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1418908167191576493158429 532090562696841184934411)
                    ·
                      rfl

theorem cell22_1554364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_1554364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554364 prefixEnd_1554364 := by exact prefixLift 1554364
  have htrace : WordTrace (prefixWord ++ tailWord_1554364) baseStart_1554364 baseEnd_1554364 := by
    simpa [prefixWord, tailWord_1554364, baseEnd_1554364] using wordTrace_append hprefix tailTrace_1554364
  have hstable : (prefixWord ++ tailWord_1554364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554364).length < 2 ^ (prefixWord ++ tailWord_1554364).sum := by decide
  have hdescent : baseEnd_1554364 < baseStart_1554364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554388 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 8]
def baseStart_1554388 : Nat := 118140960795 + 1554388 * 2 ^ 59
def prefixEnd_1554388 : Nat := 4983230072969 + 3 ^ 40 * 1554388 * 2
def baseEnd_1554388 : Nat := 177366259462437707444779

theorem tailTrace_1554388 : CollatzResearch.WordTrace tailWord_1554388 prefixEnd_1554388 177366259462437707444779 := by
  unfold tailWord_1554388
  simp only [CollatzResearch.WordTrace]
  refine ⟨28346593946362609590247909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37795458595150146120330545 28346593946362609590247909)
  ·
    refine ⟨5314986364942989298171483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28346593946362609590247909 5314986364942989298171483)
    ·
      refine ⟨7972479547414483947257225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5314986364942989298171483 7972479547414483947257225)
      ·
        refine ⟨5979359660560862960442919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7972479547414483947257225 5979359660560862960442919)
        ·
          refine ⟨8969039490841294440664379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5979359660560862960442919 8969039490841294440664379)
          ·
            refine ⟨13453559236261941660996569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8969039490841294440664379 13453559236261941660996569)
            ·
              refine ⟨10090169427196456245747427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13453559236261941660996569 10090169427196456245747427)
              ·
                refine ⟨15135254140794684368621141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10090169427196456245747427 15135254140794684368621141)
                ·
                  refine ⟨177366259462437707444779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15135254140794684368621141 177366259462437707444779)
                  ·
                    rfl

theorem cell22_1554388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_1554388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554388 prefixEnd_1554388 := by exact prefixLift 1554388
  have htrace : WordTrace (prefixWord ++ tailWord_1554388) baseStart_1554388 baseEnd_1554388 := by
    simpa [prefixWord, tailWord_1554388, baseEnd_1554388] using wordTrace_append hprefix tailTrace_1554388
  have hstable : (prefixWord ++ tailWord_1554388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554388).length < 2 ^ (prefixWord ++ tailWord_1554388).sum := by decide
  have hdescent : baseEnd_1554388 < baseStart_1554388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554403 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 3, 5]
def baseStart_1554403 : Nat := 118140960795 + 1554403 * 2 ^ 59
def prefixEnd_1554403 : Nat := 4983230072969 + 3 ^ 40 * 1554403 * 2
def baseEnd_1554403 : Nat := 532103913193858083209291

theorem tailTrace_1554403 : CollatzResearch.WordTrace tailWord_1554403 prefixEnd_1554403 532103913193858083209291 := by
  unfold tailWord_1554403
  simp only [CollatzResearch.WordTrace]
  refine ⟨56693734987670876742291863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37795823325113917828194575 56693734987670876742291863)
  ·
    refine ⟨85040602481506315113437795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56693734987670876742291863 85040602481506315113437795)
    ·
      refine ⟨127560903722259472670156693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85040602481506315113437795 127560903722259472670156693)
      ·
        refine ⟨5979417361980912781413595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127560903722259472670156693 5979417361980912781413595)
        ·
          refine ⟨8969126042971369172120393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5979417361980912781413595 8969126042971369172120393)
          ·
            refine ⟨6726844532228526879090295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8969126042971369172120393 6726844532228526879090295)
            ·
              refine ⟨10090266798342790318635443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6726844532228526879090295 10090266798342790318635443)
              ·
                refine ⟨15135400197514185477953165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10090266798342790318635443 15135400197514185477953165)
                ·
                  refine ⟨5675775074067819554232437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15135400197514185477953165 5675775074067819554232437)
                  ·
                    refine ⟨532103913193858083209291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5675775074067819554232437 532103913193858083209291)
                    ·
                      rfl

theorem cell22_1554403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 5].length) (baseStart_1554403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554403 prefixEnd_1554403 := by exact prefixLift 1554403
  have htrace : WordTrace (prefixWord ++ tailWord_1554403) baseStart_1554403 baseEnd_1554403 := by
    simpa [prefixWord, tailWord_1554403, baseEnd_1554403] using wordTrace_append hprefix tailTrace_1554403
  have hstable : (prefixWord ++ tailWord_1554403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554403).length < 2 ^ (prefixWord ++ tailWord_1554403).sum := by decide
  have hdescent : baseEnd_1554403 < baseStart_1554403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554471 : List Nat := [1, 1, 7, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1554471 : Nat := 118140960795 + 1554471 * 2 ^ 59
def prefixEnd_1554471 : Nat := 4983230072969 + 3 ^ 40 * 1554471 * 2
def baseEnd_1554471 : Nat := 532127190983528572509083

theorem tailTrace_1554471 : CollatzResearch.WordTrace tailWord_1554471 prefixEnd_1554471 532127190983528572509083 := by
  unfold tailWord_1554471
  simp only [CollatzResearch.WordTrace]
  refine ⟨56696215151424524355767267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37797476767616349570511511 56696215151424524355767267)
  ·
    refine ⟨85044322727136786533650901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56696215151424524355767267 85044322727136786533650901)
    ·
      refine ⟨1993226313917268434382443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 85044322727136786533650901 1993226313917268434382443)
      ·
        refine ⟨2989839470875902651573665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1993226313917268434382443 2989839470875902651573665)
        ·
          refine ⟨2242379603156926988680249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2989839470875902651573665 2242379603156926988680249)
          ·
            refine ⟨1681784702367695241510187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2242379603156926988680249 1681784702367695241510187)
            ·
              refine ⟨2522677053551542862265281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1681784702367695241510187 2522677053551542862265281)
              ·
                refine ⟨1892007790163657146698961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2522677053551542862265281 1892007790163657146698961)
                ·
                  refine ⟨1419005842622742860024221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1892007790163657146698961 1419005842622742860024221)
                  ·
                    refine ⟨532127190983528572509083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1419005842622742860024221 532127190983528572509083)
                    ·
                      rfl

theorem cell22_1554471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1554471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554471 prefixEnd_1554471 := by exact prefixLift 1554471
  have htrace : WordTrace (prefixWord ++ tailWord_1554471) baseStart_1554471 baseEnd_1554471 := by
    simpa [prefixWord, tailWord_1554471, baseEnd_1554471] using wordTrace_append hprefix tailTrace_1554471
  have hstable : (prefixWord ++ tailWord_1554471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554471).length < 2 ^ (prefixWord ++ tailWord_1554471).sum := by decide
  have hdescent : baseEnd_1554471 < baseStart_1554471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554482 : List Nat := [3, 2, 1, 1, 2, 4, 2, 1, 3, 3]
def baseStart_1554482 : Nat := 118140960795 + 1554482 * 2 ^ 59
def prefixEnd_1554482 : Nat := 4983230072969 + 3 ^ 40 * 1554482 * 2
def baseEnd_1554482 : Nat := 532130956508328210484049

theorem tailTrace_1554482 : CollatzResearch.WordTrace tailWord_1554482 prefixEnd_1554482 532130956508328210484049 := by
  unfold tailWord_1554482
  simp only [CollatzResearch.WordTrace]
  refine ⟨14174154088596168308604425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37797744236256448822945133 14174154088596168308604425)
  ·
    refine ⟨10630615566447126231453319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14174154088596168308604425 10630615566447126231453319)
    ·
      refine ⟨15945923349670689347179979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10630615566447126231453319 15945923349670689347179979)
      ·
        refine ⟨23918885024506034020769969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15945923349670689347179979 23918885024506034020769969)
        ·
          refine ⟨17939163768379525515577477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23918885024506034020769969 17939163768379525515577477)
          ·
            refine ⟨3363593206571161034170777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17939163768379525515577477 3363593206571161034170777)
            ·
              refine ⟨2522694904928370775628083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3363593206571161034170777 2522694904928370775628083)
              ·
                refine ⟨3784042357392556163442125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2522694904928370775628083 3784042357392556163442125)
                ·
                  refine ⟨1419015884022208561290797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3784042357392556163442125 1419015884022208561290797)
                  ·
                    refine ⟨532130956508328210484049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1419015884022208561290797 532130956508328210484049)
                    ·
                      rfl

theorem cell22_1554482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_1554482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554482 prefixEnd_1554482 := by exact prefixLift 1554482
  have htrace : WordTrace (prefixWord ++ tailWord_1554482) baseStart_1554482 baseEnd_1554482 := by
    simpa [prefixWord, tailWord_1554482, baseEnd_1554482] using wordTrace_append hprefix tailTrace_1554482
  have hstable : (prefixWord ++ tailWord_1554482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554482).length < 2 ^ (prefixWord ++ tailWord_1554482).sum := by decide
  have hdescent : baseEnd_1554482 < baseStart_1554482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554540 : List Nat := [2, 2, 1, 1, 3, 3, 3, 1, 6]
def baseStart_1554540 : Nat := 118140960795 + 1554540 * 2 ^ 59
def prefixEnd_1554540 : Nat := 4983230072969 + 3 ^ 40 * 1554540 * 2
def baseEnd_1554540 : Nat := 177383603697878464177957

theorem tailTrace_1554540 : CollatzResearch.WordTrace tailWord_1554540 prefixEnd_1554540 177383603697878464177957 := by
  unfold tailWord_1554540
  simp only [CollatzResearch.WordTrace]
  refine ⟨28349365894087274570014537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37799154525449699426686049 28349365894087274570014537)
  ·
    refine ⟨21262024420565455927510903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28349365894087274570014537 21262024420565455927510903)
    ·
      refine ⟨31893036630848183891266355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21262024420565455927510903 31893036630848183891266355)
      ·
        refine ⟨47839554946272275836899533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31893036630848183891266355 47839554946272275836899533)
        ·
          refine ⟨17939833104852103438837325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47839554946272275836899533 17939833104852103438837325)
          ·
            refine ⟨6727437414319538789563997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17939833104852103438837325 6727437414319538789563997)
            ·
              refine ⟨2522789030369827046086499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6727437414319538789563997 2522789030369827046086499)
              ·
                refine ⟨3784183545554740569129749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2522789030369827046086499 3784183545554740569129749)
                ·
                  refine ⟨177383603697878464177957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3784183545554740569129749 177383603697878464177957)
                  ·
                    rfl

theorem cell22_1554540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_1554540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554540 prefixEnd_1554540 := by exact prefixLift 1554540
  have htrace : WordTrace (prefixWord ++ tailWord_1554540) baseStart_1554540 baseEnd_1554540 := by
    simpa [prefixWord, tailWord_1554540, baseEnd_1554540] using wordTrace_append hprefix tailTrace_1554540
  have hstable : (prefixWord ++ tailWord_1554540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554540).length < 2 ^ (prefixWord ++ tailWord_1554540).sum := by decide
  have hdescent : baseEnd_1554540 < baseStart_1554540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554589 : List Nat := [1, 4, 2, 1, 1, 4, 2, 2, 2, 3]
def baseStart_1554589 : Nat := 118140960795 + 1554589 * 2 ^ 59
def prefixEnd_1554589 : Nat := 4983230072969 + 3 ^ 40 * 1554589 * 2
def baseEnd_1554589 : Nat := 532167584795015598058721

theorem tailTrace_1554589 : CollatzResearch.WordTrace tailWord_1554589 prefixEnd_1554589 532167584795015598058721 := by
  unfold tailWord_1554589
  simp only [CollatzResearch.WordTrace]
  refine ⟨56700518964997030508562821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37800345976664687005708547 56700518964997030508562821)
  ·
    refine ⟨10631347305936943220355529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56700518964997030508562821 10631347305936943220355529)
    ·
      refine ⟨7973510479452707415266647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10631347305936943220355529 7973510479452707415266647)
      ·
        refine ⟨11960265719179061122899971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7973510479452707415266647 11960265719179061122899971)
        ·
          refine ⟨17940398578768591684349957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11960265719179061122899971 17940398578768591684349957)
          ·
            refine ⟨3363824733519110940815617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17940398578768591684349957 3363824733519110940815617)
            ·
              refine ⟨2522868550139333205611713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3363824733519110940815617 2522868550139333205611713)
              ·
                refine ⟨1892151412604499904208785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2522868550139333205611713 1892151412604499904208785)
                ·
                  refine ⟨1419113559453374928156589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1892151412604499904208785 1419113559453374928156589)
                  ·
                    refine ⟨532167584795015598058721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1419113559453374928156589 532167584795015598058721)
                    ·
                      rfl

theorem cell22_1554589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_1554589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554589 prefixEnd_1554589 := by exact prefixLift 1554589
  have htrace : WordTrace (prefixWord ++ tailWord_1554589) baseStart_1554589 baseEnd_1554589 := by
    simpa [prefixWord, tailWord_1554589, baseEnd_1554589] using wordTrace_append hprefix tailTrace_1554589
  have hstable : (prefixWord ++ tailWord_1554589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554589).length < 2 ^ (prefixWord ++ tailWord_1554589).sum := by decide
  have hdescent : baseEnd_1554589 < baseStart_1554589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554591 : List Nat := [1, 1, 2, 6, 1, 3, 2, 2, 4]
def baseStart_1554591 : Nat := 118140960795 + 1554591 * 2 ^ 59
def prefixEnd_1554591 : Nat := 4983230072969 + 3 ^ 40 * 1554591 * 2
def baseEnd_1554591 : Nat := 177389423145296086502905

theorem tailTrace_1554591 : CollatzResearch.WordTrace tailWord_1554591 prefixEnd_1554591 177389423145296086502905 := by
  unfold tailWord_1554591
  simp only [CollatzResearch.WordTrace]
  refine ⟨56700591910989784850135627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37800394607326523233423751 56700591910989784850135627)
  ·
    refine ⟨85050887866484677275203441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56700591910989784850135627 85050887866484677275203441)
    ·
      refine ⟨63788165899863507956402581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85050887866484677275203441 63788165899863507956402581)
      ·
        refine ⟨2990070276556101935456371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63788165899863507956402581 2990070276556101935456371)
        ·
          refine ⟨4485105414834152903184557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2990070276556101935456371 4485105414834152903184557)
          ·
            refine ⟨1681914530562807338694209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4485105414834152903184557 1681914530562807338694209)
            ·
              refine ⟨1261435897922105504020657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1681914530562807338694209 1261435897922105504020657)
              ·
                refine ⟨946076923441579128015493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1261435897922105504020657 946076923441579128015493)
                ·
                  refine ⟨177389423145296086502905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 946076923441579128015493 177389423145296086502905)
                  ·
                    rfl

theorem cell22_1554591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 4].length) (baseStart_1554591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554591 prefixEnd_1554591 := by exact prefixLift 1554591
  have htrace : WordTrace (prefixWord ++ tailWord_1554591) baseStart_1554591 baseEnd_1554591 := by
    simpa [prefixWord, tailWord_1554591, baseEnd_1554591] using wordTrace_append hprefix tailTrace_1554591
  have hstable : (prefixWord ++ tailWord_1554591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554591).length < 2 ^ (prefixWord ++ tailWord_1554591).sum := by decide
  have hdescent : baseEnd_1554591 < baseStart_1554591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554606 : List Nat := [4, 1, 4, 2, 1, 1, 2, 1, 1, 5]
def baseStart_1554606 : Nat := 118140960795 + 1554606 * 2 ^ 59
def prefixEnd_1554606 : Nat := 4983230072969 + 3 ^ 40 * 1554606 * 2
def baseEnd_1554606 : Nat := 532173404242433220383669

theorem tailTrace_1554606 : CollatzResearch.WordTrace tailWord_1554606 prefixEnd_1554606 532173404242433220383669 := by
  unfold tailWord_1554606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7087642375741930301491459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37800759337290294941287781 7087642375741930301491459)
  ·
    refine ⟨10631463563612895452237189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7087642375741930301491459 10631463563612895452237189)
    ·
      refine ⟨1993399418177417897294473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10631463563612895452237189 1993399418177417897294473)
      ·
        refine ⟨1495049563633063422970855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1993399418177417897294473 1495049563633063422970855)
        ·
          refine ⟨2242574345449595134456283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1495049563633063422970855 2242574345449595134456283)
          ·
            refine ⟨3363861518174392701684425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2242574345449595134456283 3363861518174392701684425)
            ·
              refine ⟨2522896138630794526263319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3363861518174392701684425 2522896138630794526263319)
              ·
                refine ⟨3784344207946191789394979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2522896138630794526263319 3784344207946191789394979)
                ·
                  refine ⟨5676516311919287684092469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3784344207946191789394979 5676516311919287684092469)
                  ·
                    refine ⟨532173404242433220383669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5676516311919287684092469 532173404242433220383669)
                    ·
                      rfl

theorem cell22_1554606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_1554606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554606 prefixEnd_1554606 := by exact prefixLift 1554606
  have htrace : WordTrace (prefixWord ++ tailWord_1554606) baseStart_1554606 baseEnd_1554606 := by
    simpa [prefixWord, tailWord_1554606, baseEnd_1554606] using wordTrace_append hprefix tailTrace_1554606
  have hstable : (prefixWord ++ tailWord_1554606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554606).length < 2 ^ (prefixWord ++ tailWord_1554606).sum := by decide
  have hdescent : baseEnd_1554606 < baseStart_1554606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554617 : List Nat := [1, 2, 1, 4, 1, 2, 3, 2, 3, 3]
def baseStart_1554617 : Nat := 118140960795 + 1554617 * 2 ^ 59
def prefixEnd_1554617 : Nat := 4983230072969 + 3 ^ 40 * 1554617 * 2
def baseEnd_1554617 : Nat := 532177169767232858358635

theorem tailTrace_1554617 : CollatzResearch.WordTrace tailWord_1554617 prefixEnd_1554617 532177169767232858358635 := by
  unfold tailWord_1554617
  simp only [CollatzResearch.WordTrace]
  refine ⟨56701540208895591290582105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37801026805930394193721403 56701540208895591290582105)
  ·
    refine ⟨42526155156671693467936579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56701540208895591290582105 42526155156671693467936579)
    ·
      refine ⟨63789232735007540201904869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42526155156671693467936579 63789232735007540201904869)
      ·
        refine ⟨11960481137813913787857163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63789232735007540201904869 11960481137813913787857163)
        ·
          refine ⟨17940721706720870681785745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11960481137813913787857163 17940721706720870681785745)
          ·
            refine ⟨13455541280040653011339309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17940721706720870681785745 13455541280040653011339309)
            ·
              refine ⟨5045827980015244879252241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13455541280040653011339309 5045827980015244879252241)
              ·
                refine ⟨3784370985011433659439181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5045827980015244879252241 3784370985011433659439181)
                ·
                  refine ⟨1419139119379287622289693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3784370985011433659439181 1419139119379287622289693)
                  ·
                    refine ⟨532177169767232858358635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1419139119379287622289693 532177169767232858358635)
                    ·
                      rfl

theorem cell22_1554617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 3].length) (baseStart_1554617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554617 prefixEnd_1554617 := by exact prefixLift 1554617
  have htrace : WordTrace (prefixWord ++ tailWord_1554617) baseStart_1554617 baseEnd_1554617 := by
    simpa [prefixWord, tailWord_1554617, baseEnd_1554617] using wordTrace_append hprefix tailTrace_1554617
  have hstable : (prefixWord ++ tailWord_1554617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554617).length < 2 ^ (prefixWord ++ tailWord_1554617).sum := by decide
  have hdescent : baseEnd_1554617 < baseStart_1554617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554664 : List Nat := [2, 1, 4, 1, 2, 3, 3, 1, 5]
def baseStart_1554664 : Nat := 118140960795 + 1554664 * 2 ^ 59
def prefixEnd_1554664 : Nat := 4983230072969 + 3 ^ 40 * 1554664 * 2
def baseEnd_1554664 : Nat := 177397752942580134144497

theorem tailTrace_1554664 : CollatzResearch.WordTrace tailWord_1554664 prefixEnd_1554664 177397752942580134144497 := by
  unfold tailWord_1554664
  simp only [CollatzResearch.WordTrace]
  refine ⟨28351627219862659158771523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37802169626483545545028697 28351627219862659158771523)
  ·
    refine ⟨42527440829793988738157285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28351627219862659158771523 42527440829793988738157285)
    ·
      refine ⟨7973895155586372888404491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42527440829793988738157285 7973895155586372888404491)
      ·
        refine ⟨11960842733379559332606737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7973895155586372888404491 11960842733379559332606737)
        ·
          refine ⟨8970632050034669499455053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11960842733379559332606737 8970632050034669499455053)
          ·
            refine ⟨3363987018763001062295645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8970632050034669499455053 3363987018763001062295645)
            ·
              refine ⟨1261495132036125398360867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3363987018763001062295645 1261495132036125398360867)
              ·
                refine ⟨1892242698054188097541301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1261495132036125398360867 1892242698054188097541301)
                ·
                  refine ⟨177397752942580134144497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1892242698054188097541301 177397752942580134144497)
                  ·
                    rfl

theorem cell22_1554664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 5].length) (baseStart_1554664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554664 prefixEnd_1554664 := by exact prefixLift 1554664
  have htrace : WordTrace (prefixWord ++ tailWord_1554664) baseStart_1554664 baseEnd_1554664 := by
    simpa [prefixWord, tailWord_1554664, baseEnd_1554664] using wordTrace_append hprefix tailTrace_1554664
  have hstable : (prefixWord ++ tailWord_1554664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554664).length < 2 ^ (prefixWord ++ tailWord_1554664).sum := by decide
  have hdescent : baseEnd_1554664 < baseStart_1554664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554675 : List Nat := [1, 1, 1, 2, 2, 4, 1, 4, 6]
def baseStart_1554675 : Nat := 118140960795 + 1554675 * 2 ^ 59
def prefixEnd_1554675 : Nat := 4983230072969 + 3 ^ 40 * 1554675 * 2
def baseEnd_1554675 : Nat := 177399008117513346802819

theorem tailTrace_1554675 : CollatzResearch.WordTrace tailWord_1554675 prefixEnd_1554675 177399008117513346802819 := by
  unfold tailWord_1554675
  simp only [CollatzResearch.WordTrace]
  refine ⟨56703655642685467196193479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37802437095123644797462319 56703655642685467196193479)
  ·
    refine ⟨85055483464028200794290219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56703655642685467196193479 85055483464028200794290219)
    ·
      refine ⟨127583225196042301191435329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85055483464028200794290219 127583225196042301191435329)
      ·
        refine ⟨95687418897031725893576497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127583225196042301191435329 95687418897031725893576497)
        ·
          refine ⟨71765564172773794420182373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95687418897031725893576497 71765564172773794420182373)
          ·
            refine ⟨13456043282395086453784195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71765564172773794420182373 13456043282395086453784195)
            ·
              refine ⟨20184064923592629680676293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13456043282395086453784195 20184064923592629680676293)
              ·
                refine ⟨3784512173173618065126805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20184064923592629680676293 3784512173173618065126805)
                ·
                  refine ⟨177399008117513346802819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3784512173173618065126805 177399008117513346802819)
                  ·
                    rfl

theorem cell22_1554675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 6].length) (baseStart_1554675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554675 prefixEnd_1554675 := by exact prefixLift 1554675
  have htrace : WordTrace (prefixWord ++ tailWord_1554675) baseStart_1554675 baseEnd_1554675 := by
    simpa [prefixWord, tailWord_1554675, baseEnd_1554675] using wordTrace_append hprefix tailTrace_1554675
  have hstable : (prefixWord ++ tailWord_1554675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554675).length < 2 ^ (prefixWord ++ tailWord_1554675).sum := by decide
  have hdescent : baseEnd_1554675 < baseStart_1554675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554728 : List Nat := [2, 1, 5, 1, 4, 1, 1, 2, 1, 4]
def baseStart_1554728 : Nat := 118140960795 + 1554728 * 2 ^ 59
def prefixEnd_1554728 : Nat := 4983230072969 + 3 ^ 40 * 1554728 * 2
def baseEnd_1554728 : Nat := 532215167335665568833295

theorem tailTrace_1554728 : CollatzResearch.WordTrace tailWord_1554728 prefixEnd_1554728 532215167335665568833295 := by
  unfold tailWord_1554728
  simp only [CollatzResearch.WordTrace]
  refine ⟨28352794355746728623936419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37803725807662304831915225 28352794355746728623936419)
  ·
    refine ⟨42529191533620092935904629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28352794355746728623936419 42529191533620092935904629)
    ·
      refine ⟨3987111706276883712741059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42529191533620092935904629 3987111706276883712741059)
      ·
        refine ⟨5980667559415325569111589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3987111706276883712741059 5980667559415325569111589)
        ·
          refine ⟨1121375167390373544208423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5980667559415325569111589 1121375167390373544208423)
          ·
            refine ⟨1682062751085560316312635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1121375167390373544208423 1682062751085560316312635)
            ·
              refine ⟨2523094126628340474468953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1682062751085560316312635 2523094126628340474468953)
              ·
                refine ⟨1892320594971255355851715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2523094126628340474468953 1892320594971255355851715)
                ·
                  refine ⟨2838480892456883033777573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1892320594971255355851715 2838480892456883033777573)
                  ·
                    refine ⟨532215167335665568833295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2838480892456883033777573 532215167335665568833295)
                    ·
                      rfl

theorem cell22_1554728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_1554728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554728 prefixEnd_1554728 := by exact prefixLift 1554728
  have htrace : WordTrace (prefixWord ++ tailWord_1554728) baseStart_1554728 baseEnd_1554728 := by
    simpa [prefixWord, tailWord_1554728, baseEnd_1554728] using wordTrace_append hprefix tailTrace_1554728
  have hstable : (prefixWord ++ tailWord_1554728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554728).length < 2 ^ (prefixWord ++ tailWord_1554728).sum := by decide
  have hdescent : baseEnd_1554728 < baseStart_1554728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554735 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 2, 7]
def baseStart_1554735 : Nat := 118140960795 + 1554735 * 2 ^ 59
def prefixEnd_1554735 : Nat := 4983230072969 + 3 ^ 40 * 1554735 * 2
def baseEnd_1554735 : Nat := 532217563578719883908273

theorem tailTrace_1554735 : CollatzResearch.WordTrace tailWord_1554735 prefixEnd_1554735 532217563578719883908273 := by
  unfold tailWord_1554735
  simp only [CollatzResearch.WordTrace]
  refine ⟨56705844022468097443377659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37803896014978731628918439 56705844022468097443377659)
  ·
    refine ⟨85058766033702146165066489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56705844022468097443377659 85058766033702146165066489)
    ·
      refine ⟨63794074525276609623799867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85058766033702146165066489 63794074525276609623799867)
      ·
        refine ⟨95691111787914914435699801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63794074525276609623799867 95691111787914914435699801)
        ·
          refine ⟨71768333840936185826774851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95691111787914914435699801 71768333840936185826774851)
          ·
            refine ⟨107652500761404278740162277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71768333840936185826774851 107652500761404278740162277)
            ·
              refine ⟨20184843892763302263780427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107652500761404278740162277 20184843892763302263780427)
              ·
                refine ⟨30277265839144953395670641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20184843892763302263780427 30277265839144953395670641)
                ·
                  refine ⟨22707949379358715046752981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30277265839144953395670641 22707949379358715046752981)
                  ·
                    refine ⟨532217563578719883908273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22707949379358715046752981 532217563578719883908273)
                    ·
                      rfl

theorem cell22_1554735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_1554735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554735 prefixEnd_1554735 := by exact prefixLift 1554735
  have htrace : WordTrace (prefixWord ++ tailWord_1554735) baseStart_1554735 baseEnd_1554735 := by
    simpa [prefixWord, tailWord_1554735, baseEnd_1554735] using wordTrace_append hprefix tailTrace_1554735
  have hstable : (prefixWord ++ tailWord_1554735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554735).length < 2 ^ (prefixWord ++ tailWord_1554735).sum := by decide
  have hdescent : baseEnd_1554735 < baseStart_1554735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554752 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 7, 3]
def baseStart_1554752 : Nat := 118140960795 + 1554752 * 2 ^ 59
def prefixEnd_1554752 : Nat := 4983230072969 + 3 ^ 40 * 1554752 * 2
def baseEnd_1554752 : Nat := 532223383026137506233221

theorem tailTrace_1554752 : CollatzResearch.WordTrace tailWord_1554752 prefixEnd_1554752 532223383026137506233221 := by
  unfold tailWord_1554752
  simp only [CollatzResearch.WordTrace]
  refine ⟨28353232031703254673373255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37804309375604339564497673 28353232031703254673373255)
  ·
    refine ⟨42529848047554882010059883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28353232031703254673373255 42529848047554882010059883)
    ·
      refine ⟨63794772071332323015089825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42529848047554882010059883 63794772071332323015089825)
      ·
        refine ⟨47846079053499242261317369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63794772071332323015089825 47846079053499242261317369)
        ·
          refine ⟨35884559290124431695988027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47846079053499242261317369 35884559290124431695988027)
          ·
            refine ⟨53826838935186647543982041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35884559290124431695988027 53826838935186647543982041)
            ·
              refine ⟨40370129201389985657986531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53826838935186647543982041 40370129201389985657986531)
              ·
                refine ⟨60555193802084978486979797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40370129201389985657986531 60555193802084978486979797)
                ·
                  refine ⟨1419262354736366683288589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 60555193802084978486979797 1419262354736366683288589)
                  ·
                    refine ⟨532223383026137506233221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1419262354736366683288589 532223383026137506233221)
                    ·
                      rfl

theorem cell22_1554752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 7, 3].length) (baseStart_1554752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554752 prefixEnd_1554752 := by exact prefixLift 1554752
  have htrace : WordTrace (prefixWord ++ tailWord_1554752) baseStart_1554752 baseEnd_1554752 := by
    simpa [prefixWord, tailWord_1554752, baseEnd_1554752] using wordTrace_append hprefix tailTrace_1554752
  have hstable : (prefixWord ++ tailWord_1554752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554752).length < 2 ^ (prefixWord ++ tailWord_1554752).sum := by decide
  have hdescent : baseEnd_1554752 < baseStart_1554752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554786 : List Nat := [3, 3, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_1554786 : Nat := 118140960795 + 1554786 * 2 ^ 59
def prefixEnd_1554786 : Nat := 4983230072969 + 3 ^ 40 * 1554786 * 2
def baseEnd_1554786 : Nat := 532235021920972750883117

theorem tailTrace_1554786 : CollatzResearch.WordTrace tailWord_1554786 prefixEnd_1554786 532235021920972750883117 := by
  unfold tailWord_1554786
  simp only [CollatzResearch.WordTrace]
  refine ⟨14176926036320833288371053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37805136096855555435656141 14176926036320833288371053)
  ·
    refine ⟨5316347263620312483139145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14176926036320833288371053 5316347263620312483139145)
    ·
      refine ⟨3987260447715234362354359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5316347263620312483139145 3987260447715234362354359)
      ·
        refine ⟨5980890671572851543531539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3987260447715234362354359 5980890671572851543531539)
        ·
          refine ⟨8971336007359277315297309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5980890671572851543531539 8971336007359277315297309)
          ·
            refine ⟨3364251002759728993236491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8971336007359277315297309 3364251002759728993236491)
            ·
              refine ⟨5046376504139593489854737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3364251002759728993236491 5046376504139593489854737)
              ·
                refine ⟨3784782378104695117391053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5046376504139593489854737 3784782378104695117391053)
                ·
                  refine ⟨1419293391789260669021645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3784782378104695117391053 1419293391789260669021645)
                  ·
                    refine ⟨532235021920972750883117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1419293391789260669021645 532235021920972750883117)
                    ·
                      rfl

theorem cell22_1554786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_1554786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554786 prefixEnd_1554786 := by exact prefixLift 1554786
  have htrace : WordTrace (prefixWord ++ tailWord_1554786) baseStart_1554786 baseEnd_1554786 := by
    simpa [prefixWord, tailWord_1554786, baseEnd_1554786] using wordTrace_append hprefix tailTrace_1554786
  have hstable : (prefixWord ++ tailWord_1554786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554786).length < 2 ^ (prefixWord ++ tailWord_1554786).sum := by decide
  have hdescent : baseEnd_1554786 < baseStart_1554786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554797 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_1554797 : Nat := 118140960795 + 1554797 * 2 ^ 59
def prefixEnd_1554797 : Nat := 4983230072969 + 3 ^ 40 * 1554797 * 2
def baseEnd_1554797 : Nat := 532238787445772388858083

theorem tailTrace_1554797 : CollatzResearch.WordTrace tailWord_1554797 prefixEnd_1554797 532238787445772388858083 := by
  unfold tailWord_1554797
  simp only [CollatzResearch.WordTrace]
  refine ⟨56708105348243482032134645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37805403565495654688089763 56708105348243482032134645)
  ·
    refine ⟨5316384876397826440512623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56708105348243482032134645 5316384876397826440512623)
    ·
      refine ⟨7974577314596739660768935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5316384876397826440512623 7974577314596739660768935)
      ·
        refine ⟨11961865971895109491153403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7974577314596739660768935 11961865971895109491153403)
        ·
          refine ⟨17942798957842664236730105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11961865971895109491153403 17942798957842664236730105)
          ·
            refine ⟨13457099218381998177547579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17942798957842664236730105 13457099218381998177547579)
            ·
              refine ⟨20185648827572997266321369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13457099218381998177547579 20185648827572997266321369)
              ·
                refine ⟨15139236620679747949741027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20185648827572997266321369 15139236620679747949741027)
                ·
                  refine ⟨22708854931019621924611541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15139236620679747949741027 22708854931019621924611541)
                  ·
                    refine ⟨532238787445772388858083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22708854931019621924611541 532238787445772388858083)
                    ·
                      rfl

theorem cell22_1554797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_1554797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554797 prefixEnd_1554797 := by exact prefixLift 1554797
  have htrace : WordTrace (prefixWord ++ tailWord_1554797) baseStart_1554797 baseEnd_1554797 := by
    simpa [prefixWord, tailWord_1554797, baseEnd_1554797] using wordTrace_append hprefix tailTrace_1554797
  have hstable : (prefixWord ++ tailWord_1554797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554797).length < 2 ^ (prefixWord ++ tailWord_1554797).sum := by decide
  have hdescent : baseEnd_1554797 < baseStart_1554797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554812 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 5, 4]
def baseStart_1554812 : Nat := 118140960795 + 1554812 * 2 ^ 59
def prefixEnd_1554812 : Nat := 4983230072969 + 3 ^ 40 * 1554812 * 2
def baseEnd_1554812 : Nat := 532243922252317349733037

theorem tailTrace_1554812 : CollatzResearch.WordTrace tailWord_1554812 prefixEnd_1554812 532243922252317349733037 := by
  unfold tailWord_1554812
  simp only [CollatzResearch.WordTrace]
  refine ⟨28354326221594569796965345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37805768295459426395953793 28354326221594569796965345)
  ·
    refine ⟨21265744666195927347724009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28354326221594569796965345 21265744666195927347724009)
    ·
      refine ⟨15949308499646945510793007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21265744666195927347724009 15949308499646945510793007)
      ·
        refine ⟨23923962749470418266189511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15949308499646945510793007 23923962749470418266189511)
        ·
          refine ⟨35885944124205627399284267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23923962749470418266189511 35885944124205627399284267)
          ·
            refine ⟨53828916186308441098926401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35885944124205627399284267 53828916186308441098926401)
            ·
              refine ⟨40371687139731330824194801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53828916186308441098926401 40371687139731330824194801)
              ·
                refine ⟨30278765354798498118146101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40371687139731330824194801 30278765354798498118146101)
                ·
                  refine ⟨2838634252012359198576197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30278765354798498118146101 2838634252012359198576197)
                  ·
                    refine ⟨532243922252317349733037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2838634252012359198576197 532243922252317349733037)
                    ·
                      rfl

theorem cell22_1554812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_1554812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554812 prefixEnd_1554812 := by exact prefixLift 1554812
  have htrace : WordTrace (prefixWord ++ tailWord_1554812) baseStart_1554812 baseEnd_1554812 := by
    simpa [prefixWord, tailWord_1554812, baseEnd_1554812] using wordTrace_append hprefix tailTrace_1554812
  have hstable : (prefixWord ++ tailWord_1554812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554812).length < 2 ^ (prefixWord ++ tailWord_1554812).sum := by decide
  have hdescent : baseEnd_1554812 < baseStart_1554812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554827 : List Nat := [1, 1, 1, 1, 4, 4, 1, 3, 6]
def baseStart_1554827 : Nat := 118140960795 + 1554827 * 2 ^ 59
def prefixEnd_1554827 : Nat := 4983230072969 + 3 ^ 40 * 1554827 * 2
def baseEnd_1554827 : Nat := 177416352352954103535997

theorem tailTrace_1554827 : CollatzResearch.WordTrace tailWord_1554827 prefixEnd_1554827 177416352352954103535997 := by
  unfold tailWord_1554827
  simp only [CollatzResearch.WordTrace]
  refine ⟨56709199538134797155726735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37806133025423198103817823 56709199538134797155726735)
  ·
    refine ⟨85063799307202195733590103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56709199538134797155726735 85063799307202195733590103)
    ·
      refine ⟨127595698960803293600385155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85063799307202195733590103 127595698960803293600385155)
      ·
        refine ⟨191393548441204940400577733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127595698960803293600385155 191393548441204940400577733)
        ·
          refine ⟨35886290332725926325108325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191393548441204940400577733 35886290332725926325108325)
          ·
            refine ⟨6728679437386111185957811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35886290332725926325108325 6728679437386111185957811)
            ·
              refine ⟨10093019156079166778936717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6728679437386111185957811 10093019156079166778936717)
              ·
                refine ⟨3784882183529687542101269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10093019156079166778936717 3784882183529687542101269)
                ·
                  refine ⟨177416352352954103535997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3784882183529687542101269 177416352352954103535997)
                  ·
                    rfl

theorem cell22_1554827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 6].length) (baseStart_1554827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554827 prefixEnd_1554827 := by exact prefixLift 1554827
  have htrace : WordTrace (prefixWord ++ tailWord_1554827) baseStart_1554827 baseEnd_1554827 := by
    simpa [prefixWord, tailWord_1554827, baseEnd_1554827] using wordTrace_append hprefix tailTrace_1554827
  have hstable : (prefixWord ++ tailWord_1554827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554827).length < 2 ^ (prefixWord ++ tailWord_1554827).sum := by decide
  have hdescent : baseEnd_1554827 < baseStart_1554827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554857 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 6, 4]
def baseStart_1554857 : Nat := 118140960795 + 1554857 * 2 ^ 59
def prefixEnd_1554857 : Nat := 4983230072969 + 3 ^ 40 * 1554857 * 2
def baseEnd_1554857 : Nat := 532259326671952232357899

theorem tailTrace_1554857 : CollatzResearch.WordTrace tailWord_1554857 prefixEnd_1554857 532259326671952232357899 := by
  unfold tailWord_1554857
  simp only [CollatzResearch.WordTrace]
  refine ⟨56710293728026112279318825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37806862485350741519545883 56710293728026112279318825)
  ·
    refine ⟨42532720296019584209489119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56710293728026112279318825 42532720296019584209489119)
    ·
      refine ⟨63799080444029376314233679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42532720296019584209489119 63799080444029376314233679)
      ·
        refine ⟨95698620666044064471350519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63799080444029376314233679 95698620666044064471350519)
        ·
          refine ⟨143547930999066096707025779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95698620666044064471350519 143547930999066096707025779)
          ·
            refine ⟨215321896498599145060538669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143547930999066096707025779 215321896498599145060538669)
            ·
              refine ⟨80745711186974679397702001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215321896498599145060538669 80745711186974679397702001)
              ·
                refine ⟨60559283390231009548276501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80745711186974679397702001 60559283390231009548276501)
                ·
                  refine ⟨2838716408917078572575461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60559283390231009548276501 2838716408917078572575461)
                  ·
                    refine ⟨532259326671952232357899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2838716408917078572575461 532259326671952232357899)
                    ·
                      rfl

theorem cell22_1554857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 4].length) (baseStart_1554857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554857 prefixEnd_1554857 := by exact prefixLift 1554857
  have htrace : WordTrace (prefixWord ++ tailWord_1554857) baseStart_1554857 baseEnd_1554857 := by
    simpa [prefixWord, tailWord_1554857, baseEnd_1554857] using wordTrace_append hprefix tailTrace_1554857
  have hstable : (prefixWord ++ tailWord_1554857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554857).length < 2 ^ (prefixWord ++ tailWord_1554857).sum := by decide
  have hdescent : baseEnd_1554857 < baseStart_1554857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554876 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 4, 3]
def baseStart_1554876 : Nat := 118140960795 + 1554876 * 2 ^ 59
def prefixEnd_1554876 : Nat := 4983230072969 + 3 ^ 40 * 1554876 * 2
def baseEnd_1554876 : Nat := 532265830760242516132841

theorem tailTrace_1554876 : CollatzResearch.WordTrace tailWord_1554876 prefixEnd_1554876 532265830760242516132841 := by
  unfold tailWord_1554876
  simp only [CollatzResearch.WordTrace]
  refine ⟨28355493357478639262130241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37807324476638185682840321 28355493357478639262130241)
  ·
    refine ⟨21266620018108979446597681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28355493357478639262130241 21266620018108979446597681)
    ·
      refine ⟨15949965013581734584948261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21266620018108979446597681 15949965013581734584948261)
      ·
        refine ⟨2990618440046575234677799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15949965013581734584948261 2990618440046575234677799)
        ·
          refine ⟨4485927660069862852016699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2990618440046575234677799 4485927660069862852016699)
          ·
            refine ⟨6728891490104794278025049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4485927660069862852016699 6728891490104794278025049)
            ·
              refine ⟨5046668617578595708518787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6728891490104794278025049 5046668617578595708518787)
              ·
                refine ⟨7570002926367893562778181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5046668617578595708518787 7570002926367893562778181)
                ·
                  refine ⟨1419375548693980043020909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7570002926367893562778181 1419375548693980043020909)
                  ·
                    refine ⟨532265830760242516132841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1419375548693980043020909 532265830760242516132841)
                    ·
                      rfl

theorem cell22_1554876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_1554876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554876 prefixEnd_1554876 := by exact prefixLift 1554876
  have htrace : WordTrace (prefixWord ++ tailWord_1554876) baseStart_1554876 baseEnd_1554876 := by
    simpa [prefixWord, tailWord_1554876, baseEnd_1554876] using wordTrace_append hprefix tailTrace_1554876
  have hstable : (prefixWord ++ tailWord_1554876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554876).length < 2 ^ (prefixWord ++ tailWord_1554876).sum := by decide
  have hdescent : baseEnd_1554876 < baseStart_1554876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554904 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 5, 3]
def baseStart_1554904 : Nat := 118140960795 + 1554904 * 2 ^ 59
def prefixEnd_1554904 : Nat := 4983230072969 + 3 ^ 40 * 1554904 * 2
def baseEnd_1554904 : Nat := 532275415732459776432755

theorem tailTrace_1554904 : CollatzResearch.WordTrace tailWord_1554904 prefixEnd_1554904 532275415732459776432755 := by
  unfold tailWord_1554904
  simp only [CollatzResearch.WordTrace]
  refine ⟨28356003979427919653139883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37808005305903892870853177 28356003979427919653139883)
  ·
    refine ⟨42534005969141879479709825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28356003979427919653139883 42534005969141879479709825)
    ·
      refine ⟨31900504476856409609782369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42534005969141879479709825 31900504476856409609782369)
      ·
        refine ⟨23925378357642307207336777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31900504476856409609782369 23925378357642307207336777)
        ·
          refine ⟨17944033768231730405502583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23925378357642307207336777 17944033768231730405502583)
          ·
            refine ⟨26916050652347595608253875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17944033768231730405502583 26916050652347595608253875)
            ·
              refine ⟨40374075978521393412380813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26916050652347595608253875 40374075978521393412380813)
              ·
                refine ⟨15140278491945522529642805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40374075978521393412380813 15140278491945522529642805)
                ·
                  refine ⟨1419401108619892737154013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15140278491945522529642805 1419401108619892737154013)
                  ·
                    refine ⟨532275415732459776432755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1419401108619892737154013 532275415732459776432755)
                    ·
                      rfl

theorem cell22_1554904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_1554904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554904 prefixEnd_1554904 := by exact prefixLift 1554904
  have htrace : WordTrace (prefixWord ++ tailWord_1554904) baseStart_1554904 baseEnd_1554904 := by
    simpa [prefixWord, tailWord_1554904, baseEnd_1554904] using wordTrace_append hprefix tailTrace_1554904
  have hstable : (prefixWord ++ tailWord_1554904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554904).length < 2 ^ (prefixWord ++ tailWord_1554904).sum := by decide
  have hdescent : baseEnd_1554904 < baseStart_1554904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554994 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_1554994 : Nat := 118140960795 + 1554994 * 2 ^ 59
def prefixEnd_1554994 : Nat := 4983230072969 + 3 ^ 40 * 1554994 * 2
def baseEnd_1554994 : Nat := 532306224571729541682479

theorem tailTrace_1554994 : CollatzResearch.WordTrace tailWord_1554994 prefixEnd_1554994 532306224571729541682479 := by
  unfold tailWord_1554994
  simp only [CollatzResearch.WordTrace]
  refine ⟨14178822632132446169264009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37810193685686523118037357 14178822632132446169264009)
  ·
    refine ⟨10634116974099334626948007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14178822632132446169264009 10634116974099334626948007)
    ·
      refine ⟨15951175461149001940422011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10634116974099334626948007 15951175461149001940422011)
      ·
        refine ⟨23926763191723502910633017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15951175461149001940422011 23926763191723502910633017)
        ·
          refine ⟨17945072393792627182974763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23926763191723502910633017 17945072393792627182974763)
          ·
            refine ⟨26917608590688940774462145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17945072393792627182974763 26917608590688940774462145)
            ·
              refine ⟨20188206443016705580846609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26917608590688940774462145 20188206443016705580846609)
              ·
                refine ⟨15141154832262529185634957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20188206443016705580846609 15141154832262529185634957)
                ·
                  refine ⟨5677933062098448444613109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15141154832262529185634957 5677933062098448444613109)
                  ·
                    refine ⟨532306224571729541682479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5677933062098448444613109 532306224571729541682479)
                    ·
                      rfl

theorem cell22_1554994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_1554994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1554994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1554994 prefixEnd_1554994 := by exact prefixLift 1554994
  have htrace : WordTrace (prefixWord ++ tailWord_1554994) baseStart_1554994 baseEnd_1554994 := by
    simpa [prefixWord, tailWord_1554994, baseEnd_1554994] using wordTrace_append hprefix tailTrace_1554994
  have hstable : (prefixWord ++ tailWord_1554994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554994).length < 2 ^ (prefixWord ++ tailWord_1554994).sum := by decide
  have hdescent : baseEnd_1554994 < baseStart_1554994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555011 : List Nat := [1, 1, 1, 3, 1, 2, 1, 7, 2, 3]
def baseStart_1555011 : Nat := 118140960795 + 1555011 * 2 ^ 59
def prefixEnd_1555011 : Nat := 4983230072969 + 3 ^ 40 * 1555011 * 2
def baseEnd_1555011 : Nat := 532312044019147164007427

theorem tailTrace_1555011 : CollatzResearch.WordTrace tailWord_1555011 prefixEnd_1555011 532312044019147164007427 := by
  unfold tailWord_1555011
  simp only [CollatzResearch.WordTrace]
  refine ⟨56715910569468196580424887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37810607046312131053616591 56715910569468196580424887)
  ·
    refine ⟨85073865854202294870637331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56715910569468196580424887 85073865854202294870637331)
    ·
      refine ⟨127610798781303442305955997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85073865854202294870637331 127610798781303442305955997)
      ·
        refine ⟨47854049542988790864733499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127610798781303442305955997 47854049542988790864733499)
        ·
          refine ⟨71781074314483186297100249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47854049542988790864733499 71781074314483186297100249)
          ·
            refine ⟨53835805735862389722825187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71781074314483186297100249 53835805735862389722825187)
            ·
              refine ⟨80753708603793584584237781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53835805735862389722825187 80753708603793584584237781)
              ·
                refine ⟨1892665045401412138693073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 80753708603793584584237781 1892665045401412138693073)
                ·
                  refine ⟨1419498784051059104019805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1892665045401412138693073 1419498784051059104019805)
                  ·
                    refine ⟨532312044019147164007427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1419498784051059104019805 532312044019147164007427)
                    ·
                      rfl

theorem cell22_1555011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 3].length) (baseStart_1555011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555011 prefixEnd_1555011 := by exact prefixLift 1555011
  have htrace : WordTrace (prefixWord ++ tailWord_1555011) baseStart_1555011 baseEnd_1555011 := by
    simpa [prefixWord, tailWord_1555011, baseEnd_1555011] using wordTrace_append hprefix tailTrace_1555011
  have hstable : (prefixWord ++ tailWord_1555011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555011).length < 2 ^ (prefixWord ++ tailWord_1555011).sum := by decide
  have hdescent : baseEnd_1555011 < baseStart_1555011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555026 : List Nat := [3, 2, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_1555026 : Nat := 118140960795 + 1555026 * 2 ^ 59
def prefixEnd_1555026 : Nat := 4983230072969 + 3 ^ 40 * 1555026 * 2
def baseEnd_1555026 : Nat := 532317178825692124882381

theorem tailTrace_1555026 : CollatzResearch.WordTrace tailWord_1555026 prefixEnd_1555026 532317178825692124882381 := by
  unfold tailWord_1555026
  simp only [CollatzResearch.WordTrace]
  refine ⟨14179114416103463535555233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37810971776275902761480621 14179114416103463535555233)
  ·
    refine ⟨10634335812077597651666425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14179114416103463535555233 10634335812077597651666425)
    ·
      refine ⟨7975751859058198238749819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10634335812077597651666425 7975751859058198238749819)
      ·
        refine ⟨11963627788587297358124729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7975751859058198238749819 11963627788587297358124729)
        ·
          refine ⟨8972720841440473018593547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11963627788587297358124729 8972720841440473018593547)
          ·
            refine ⟨13459081262160709527890321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8972720841440473018593547 13459081262160709527890321)
            ·
              refine ⟨10094310946620532145917741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13459081262160709527890321 10094310946620532145917741)
              ·
                refine ⟨3785366604982699554719153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10094310946620532145917741 3785366604982699554719153)
                ·
                  refine ⟨2839024953737024666039365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3785366604982699554719153 2839024953737024666039365)
                  ·
                    refine ⟨532317178825692124882381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2839024953737024666039365 532317178825692124882381)
                    ·
                      rfl

theorem cell22_1555026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_1555026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555026 prefixEnd_1555026 := by exact prefixLift 1555026
  have htrace : WordTrace (prefixWord ++ tailWord_1555026) baseStart_1555026 baseEnd_1555026 := by
    simpa [prefixWord, tailWord_1555026, baseEnd_1555026] using wordTrace_append hprefix tailTrace_1555026
  have hstable : (prefixWord ++ tailWord_1555026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555026).length < 2 ^ (prefixWord ++ tailWord_1555026).sum := by decide
  have hdescent : baseEnd_1555026 < baseStart_1555026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555084 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 3, 7]
def baseStart_1555084 : Nat := 118140960795 + 1555084 * 2 ^ 59
def prefixEnd_1555084 : Nat := 4983230072969 + 3 ^ 40 * 1555084 * 2
def baseEnd_1555084 : Nat := 532337033410999306932203

theorem tailTrace_1555084 : CollatzResearch.WordTrace tailWord_1555084 prefixEnd_1555084 532337033410999306932203 := by
  unfold tailWord_1555084
  simp only [CollatzResearch.WordTrace]
  refine ⟨28359286549101865023916153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37812382065469153365221537 28359286549101865023916153)
  ·
    refine ⟨21269464911826398767937115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28359286549101865023916153 21269464911826398767937115)
    ·
      refine ⟨31904197367739598151905673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21269464911826398767937115 31904197367739598151905673)
      ·
        refine ⟨23928148025804698613929255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31904197367739598151905673 23928148025804698613929255)
        ·
          refine ⟨35892222038707047920893883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23928148025804698613929255 35892222038707047920893883)
          ·
            refine ⟨53838333058060571881340825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35892222038707047920893883 53838333058060571881340825)
            ·
              refine ⟨40378749793545428911005619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53838333058060571881340825 40378749793545428911005619)
              ·
                refine ⟨60568124690318143366508429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40378749793545428911005619 60568124690318143366508429)
                ·
                  refine ⟨22713046758869303762440661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60568124690318143366508429 22713046758869303762440661)
                  ·
                    refine ⟨532337033410999306932203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22713046758869303762440661 532337033410999306932203)
                    ·
                      rfl

theorem cell22_1555084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_1555084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555084 prefixEnd_1555084 := by exact prefixLift 1555084
  have htrace : WordTrace (prefixWord ++ tailWord_1555084) baseStart_1555084 baseEnd_1555084 := by
    simpa [prefixWord, tailWord_1555084, baseEnd_1555084] using wordTrace_append hprefix tailTrace_1555084
  have hstable : (prefixWord ++ tailWord_1555084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555084).length < 2 ^ (prefixWord ++ tailWord_1555084).sum := by decide
  have hdescent : baseEnd_1555084 < baseStart_1555084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555118 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1555118 : Nat := 118140960795 + 1555118 * 2 ^ 59
def prefixEnd_1555118 : Nat := 4983230072969 + 3 ^ 40 * 1555118 * 2
def baseEnd_1555118 : Nat := 532348672305834551582099

theorem tailTrace_1555118 : CollatzResearch.WordTrace tailWord_1555118 prefixEnd_1555118 532348672305834551582099 := by
  unfold tailWord_1555118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7089976647510069231821251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37813208786720369236380005 7089976647510069231821251)
  ·
    refine ⟨10634964971265103847731877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7089976647510069231821251 10634964971265103847731877)
    ·
      refine ⟨1994055932112206971449727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10634964971265103847731877 1994055932112206971449727)
      ·
        refine ⟨2991083898168310457174591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1994055932112206971449727 2991083898168310457174591)
        ·
          refine ⟨4486625847252465685761887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2991083898168310457174591 4486625847252465685761887)
          ·
            refine ⟨6729938770878698528642831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4486625847252465685761887 6729938770878698528642831)
            ·
              refine ⟨10094908156318047792964247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6729938770878698528642831 10094908156318047792964247)
              ·
                refine ⟨15142362234477071689446371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10094908156318047792964247 15142362234477071689446371)
                ·
                  refine ⟨22713543351715607534169557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15142362234477071689446371 22713543351715607534169557)
                  ·
                    refine ⟨532348672305834551582099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22713543351715607534169557 532348672305834551582099)
                    ·
                      rfl

theorem cell22_1555118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1555118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555118 prefixEnd_1555118 := by exact prefixLift 1555118
  have htrace : WordTrace (prefixWord ++ tailWord_1555118) baseStart_1555118 baseEnd_1555118 := by
    simpa [prefixWord, tailWord_1555118, baseEnd_1555118] using wordTrace_append hprefix tailTrace_1555118
  have hstable : (prefixWord ++ tailWord_1555118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555118).length < 2 ^ (prefixWord ++ tailWord_1555118).sum := by decide
  have hdescent : baseEnd_1555118 < baseStart_1555118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555150 : List Nat := [4, 1, 1, 1, 3, 2, 4, 1, 1, 4]
def baseStart_1555150 : Nat := 118140960795 + 1555150 * 2 ^ 59
def prefixEnd_1555150 : Nat := 4983230072969 + 3 ^ 40 * 1555150 * 2
def baseEnd_1555150 : Nat := 532359626559797134782001

theorem tailTrace_1555150 : CollatzResearch.WordTrace tailWord_1555150 prefixEnd_1555150 532359626559797134782001 := by
  unfold tailWord_1555150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7090122539495577914966863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37813986877309748879823269 7090122539495577914966863)
  ·
    refine ⟨10635183809243366872450295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7090122539495577914966863 10635183809243366872450295)
    ·
      refine ⟨15952775713865050308675443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10635183809243366872450295 15952775713865050308675443)
      ·
        refine ⟨23929163570797575463013165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15952775713865050308675443 23929163570797575463013165)
        ·
          refine ⟨8973436339049090798629937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23929163570797575463013165 8973436339049090798629937)
          ·
            refine ⟨6730077254286818098972453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8973436339049090798629937 6730077254286818098972453)
            ·
              refine ⟨1261889485178778393557335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6730077254286818098972453 1261889485178778393557335)
              ·
                refine ⟨1892834227768167590336003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1261889485178778393557335 1892834227768167590336003)
                ·
                  refine ⟨2839251341652251385504005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1892834227768167590336003 2839251341652251385504005)
                  ·
                    refine ⟨532359626559797134782001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2839251341652251385504005 532359626559797134782001)
                    ·
                      rfl

theorem cell22_1555150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_1555150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555150 prefixEnd_1555150 := by exact prefixLift 1555150
  have htrace : WordTrace (prefixWord ++ tailWord_1555150) baseStart_1555150 baseEnd_1555150 := by
    simpa [prefixWord, tailWord_1555150, baseEnd_1555150] using wordTrace_append hprefix tailTrace_1555150
  have hstable : (prefixWord ++ tailWord_1555150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555150).length < 2 ^ (prefixWord ++ tailWord_1555150).sum := by decide
  have hdescent : baseEnd_1555150 < baseStart_1555150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555161 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 4, 4]
def baseStart_1555161 : Nat := 118140960795 + 1555161 * 2 ^ 59
def prefixEnd_1555161 : Nat := 4983230072969 + 3 ^ 40 * 1555161 * 2
def baseEnd_1555161 : Nat := 532363392084596772756967

theorem tailTrace_1555161 : CollatzResearch.WordTrace tailWord_1555161 prefixEnd_1555161 532363392084596772756967 := by
  unfold tailWord_1555161
  simp only [CollatzResearch.WordTrace]
  refine ⟨56721381518924772198385337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37814254345949848132256891 56721381518924772198385337)
  ·
    refine ⟨42541036139193579148789003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56721381518924772198385337 42541036139193579148789003)
    ·
      refine ⟨63811554208790368723183505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42541036139193579148789003 63811554208790368723183505)
      ·
        refine ⟨47858665656592776542387629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63811554208790368723183505 47858665656592776542387629)
        ·
          refine ⟨17946999621222291203395361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47858665656592776542387629 17946999621222291203395361)
          ·
            refine ⟨13460249715916718402546521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17946999621222291203395361 13460249715916718402546521)
            ·
              refine ⟨10095187286937538801909891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13460249715916718402546521 10095187286937538801909891)
              ·
                refine ⟨15142780930406308202864837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10095187286937538801909891 15142780930406308202864837)
                ·
                  refine ⟨2839271424451182788037157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15142780930406308202864837 2839271424451182788037157)
                  ·
                    refine ⟨532363392084596772756967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2839271424451182788037157 532363392084596772756967)
                    ·
                      rfl

theorem cell22_1555161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 4].length) (baseStart_1555161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555161 prefixEnd_1555161 := by exact prefixLift 1555161
  have htrace : WordTrace (prefixWord ++ tailWord_1555161) baseStart_1555161 baseEnd_1555161 := by
    simpa [prefixWord, tailWord_1555161, baseEnd_1555161] using wordTrace_append hprefix tailTrace_1555161
  have hstable : (prefixWord ++ tailWord_1555161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555161).length < 2 ^ (prefixWord ++ tailWord_1555161).sum := by decide
  have hdescent : baseEnd_1555161 < baseStart_1555161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555221 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 7]
def baseStart_1555221 : Nat := 118140960795 + 1555221 * 2 ^ 59
def prefixEnd_1555221 : Nat := 4983230072969 + 3 ^ 40 * 1555221 * 2
def baseEnd_1555221 : Nat := 177461310436925538752261

theorem tailTrace_1555221 : CollatzResearch.WordTrace tailWord_1555221 prefixEnd_1555221 177461310436925538752261 := by
  unfold tailWord_1555221
  simp only [CollatzResearch.WordTrace]
  refine ⟨56723569898707402445569517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37815713265804934963713011 56723569898707402445569517)
  ·
    refine ⟨21271338712015275917088569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56723569898707402445569517 21271338712015275917088569)
    ·
      refine ⟨15953504034011456937816427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21271338712015275917088569 15953504034011456937816427)
      ·
        refine ⟨23930256051017185406724641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15953504034011456937816427 23930256051017185406724641)
        ·
          refine ⟨17947692038262889055043481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23930256051017185406724641 17947692038262889055043481)
          ·
            refine ⟨13460769028697166791282611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17947692038262889055043481 13460769028697166791282611)
            ·
              refine ⟨20191153543045750186923917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13460769028697166791282611 20191153543045750186923917)
              ·
                refine ⟨7571682578642156320096469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20191153543045750186923917 7571682578642156320096469)
                ·
                  refine ⟨177461310436925538752261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7571682578642156320096469 177461310436925538752261)
                  ·
                    rfl

theorem cell22_1555221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_1555221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555221 prefixEnd_1555221 := by exact prefixLift 1555221
  have htrace : WordTrace (prefixWord ++ tailWord_1555221) baseStart_1555221 baseEnd_1555221 := by
    simpa [prefixWord, tailWord_1555221, baseEnd_1555221] using wordTrace_append hprefix tailTrace_1555221
  have hstable : (prefixWord ++ tailWord_1555221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555221).length < 2 ^ (prefixWord ++ tailWord_1555221).sum := by decide
  have hdescent : baseEnd_1555221 < baseStart_1555221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555311 : List Nat := [1, 1, 2, 1, 3, 1, 1, 12]
def baseStart_1555311 : Nat := 118140960795 + 1555311 * 2 ^ 59
def prefixEnd_1555311 : Nat := 4983230072969 + 3 ^ 40 * 1555311 * 2
def baseEnd_1555311 : Nat := 59157193350005153500723

theorem tailTrace_1555311 : CollatzResearch.WordTrace tailWord_1555311 prefixEnd_1555311 59157193350005153500723 := by
  unfold tailWord_1555311
  simp only [CollatzResearch.WordTrace]
  refine ⟨56726852468381347816345787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37817901645587565210897191 56726852468381347816345787)
  ·
    refine ⟨85090278702572021724518681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56726852468381347816345787 85090278702572021724518681)
    ·
      refine ⟨63817709026929016293389011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85090278702572021724518681 63817709026929016293389011)
      ·
        refine ⟨95726563540393524440083517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63817709026929016293389011 95726563540393524440083517)
        ·
          refine ⟨35897461327647571665031319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95726563540393524440083517 35897461327647571665031319)
          ·
            refine ⟨53846191991471357497546979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35897461327647571665031319 53846191991471357497546979)
            ·
              refine ⟨80769287987207036246320469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53846191991471357497546979 80769287987207036246320469)
              ·
                refine ⟨59157193350005153500723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 80769287987207036246320469 59157193350005153500723)
                ·
                  rfl

theorem cell22_1555311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 12].length) (baseStart_1555311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555311 prefixEnd_1555311 := by exact prefixLift 1555311
  have htrace : WordTrace (prefixWord ++ tailWord_1555311) baseStart_1555311 baseEnd_1555311 := by
    simpa [prefixWord, tailWord_1555311, baseEnd_1555311] using wordTrace_append hprefix tailTrace_1555311
  have hstable : (prefixWord ++ tailWord_1555311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555311).length < 2 ^ (prefixWord ++ tailWord_1555311).sum := by decide
  have hdescent : baseEnd_1555311 < baseStart_1555311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555313 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 1, 6]
def baseStart_1555313 : Nat := 118140960795 + 1555313 * 2 ^ 59
def prefixEnd_1555313 : Nat := 4983230072969 + 3 ^ 40 * 1555313 * 2
def baseEnd_1555313 : Nat := 532415424790919042956501

theorem tailTrace_1555313 : CollatzResearch.WordTrace tailWord_1555313 prefixEnd_1555313 532415424790919042956501 := by
  unfold tailWord_1555313
  simp only [CollatzResearch.WordTrace]
  refine ⟨56726925414374102157918593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37817950276249401438612395 56726925414374102157918593)
  ·
    refine ⟨42545194060780576618438945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56726925414374102157918593 42545194060780576618438945)
    ·
      refine ⟨31908895545585432463829209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42545194060780576618438945 31908895545585432463829209)
      ·
        refine ⟨23931671659189074347871907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31908895545585432463829209 23931671659189074347871907)
        ·
          refine ⟨35897507488783611521807861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23931671659189074347871907 35897507488783611521807861)
          ·
            refine ⟨3365391327073463580169487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35897507488783611521807861 3365391327073463580169487)
            ·
              refine ⟨5048086990610195370254231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3365391327073463580169487 5048086990610195370254231)
              ·
                refine ⟨7572130485915293055381347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5048086990610195370254231 7572130485915293055381347)
                ·
                  refine ⟨11358195728872939583072021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7572130485915293055381347 11358195728872939583072021)
                  ·
                    refine ⟨532415424790919042956501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11358195728872939583072021 532415424790919042956501)
                    ·
                      rfl

theorem cell22_1555313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_1555313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555313 prefixEnd_1555313 := by exact prefixLift 1555313
  have htrace : WordTrace (prefixWord ++ tailWord_1555313) baseStart_1555313 baseEnd_1555313 := by
    simpa [prefixWord, tailWord_1555313, baseEnd_1555313] using wordTrace_append hprefix tailTrace_1555313
  have hstable : (prefixWord ++ tailWord_1555313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555313).length < 2 ^ (prefixWord ++ tailWord_1555313).sum := by decide
  have hdescent : baseEnd_1555313 < baseStart_1555313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555317 : List Nat := [1, 3, 4, 1, 1, 3, 2, 3, 4]
def baseStart_1555317 : Nat := 118140960795 + 1555317 * 2 ^ 59
def prefixEnd_1555317 : Nat := 4983230072969 + 3 ^ 40 * 1555317 * 2
def baseEnd_1555317 : Nat := 177472264690888121952163

theorem tailTrace_1555317 : CollatzResearch.WordTrace tailWord_1555317 prefixEnd_1555317 177472264690888121952163 := by
  unfold tailWord_1555317
  simp only [CollatzResearch.WordTrace]
  refine ⟨56727071306359610841064205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37818047537573073894042803 56727071306359610841064205)
  ·
    refine ⟨21272651739884854065399077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56727071306359610841064205 21272651739884854065399077)
    ·
      refine ⟨3988622201228410137262327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21272651739884854065399077 3988622201228410137262327)
      ·
        refine ⟨5982933301842615205893491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3988622201228410137262327 5982933301842615205893491)
        ·
          refine ⟨8974399952763922808840237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5982933301842615205893491 8974399952763922808840237)
          ·
            refine ⟨3365399982286471053315089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8974399952763922808840237 3365399982286471053315089)
            ·
              refine ⟨2524049986714853289986317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3365399982286471053315089 2524049986714853289986317)
              ·
                refine ⟨946518745018069983744869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2524049986714853289986317 946518745018069983744869)
                ·
                  refine ⟨177472264690888121952163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 946518745018069983744869 177472264690888121952163)
                  ·
                    rfl

theorem cell22_1555317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 4].length) (baseStart_1555317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555317 prefixEnd_1555317 := by exact prefixLift 1555317
  have htrace : WordTrace (prefixWord ++ tailWord_1555317) baseStart_1555317 baseEnd_1555317 := by
    simpa [prefixWord, tailWord_1555317, baseEnd_1555317] using wordTrace_append hprefix tailTrace_1555317
  have hstable : (prefixWord ++ tailWord_1555317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555317).length < 2 ^ (prefixWord ++ tailWord_1555317).sum := by decide
  have hdescent : baseEnd_1555317 < baseStart_1555317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555360 : List Nat := [2, 1, 1, 4, 1, 1, 4, 2, 3, 3]
def baseStart_1555360 : Nat := 118140960795 + 1555360 * 2 ^ 59
def prefixEnd_1555360 : Nat := 4983230072969 + 3 ^ 40 * 1555360 * 2
def baseEnd_1555360 : Nat := 532431513851426587031357

theorem tailTrace_1555360 : CollatzResearch.WordTrace tailWord_1555360 prefixEnd_1555360 532431513851426587031357 := by
  unfold tailWord_1555360
  simp only [CollatzResearch.WordTrace]
  refine ⟨28364319822601914592439767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37819093096802552789919689 28364319822601914592439767)
  ·
    refine ⟨42546479733902871888659651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28364319822601914592439767 42546479733902871888659651)
    ·
      refine ⟨63819719600854307832989477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42546479733902871888659651 63819719600854307832989477)
      ·
        refine ⟨11966197425160182718685527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63819719600854307832989477 11966197425160182718685527)
        ·
          refine ⟨17949296137740274078028291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11966197425160182718685527 17949296137740274078028291)
          ·
            refine ⟨26923944206610411117042437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17949296137740274078028291 26923944206610411117042437)
            ·
              refine ⟨5048239538739452084445457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26923944206610411117042437 5048239538739452084445457)
              ·
                refine ⟨3786179654054589063334093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5048239538739452084445457 3786179654054589063334093)
                ·
                  refine ⟨1419817370270470898750285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3786179654054589063334093 1419817370270470898750285)
                  ·
                    refine ⟨532431513851426587031357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1419817370270470898750285 532431513851426587031357)
                    ·
                      rfl

theorem cell22_1555360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 3, 3].length) (baseStart_1555360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555360 prefixEnd_1555360 := by exact prefixLift 1555360
  have htrace : WordTrace (prefixWord ++ tailWord_1555360) baseStart_1555360 baseEnd_1555360 := by
    simpa [prefixWord, tailWord_1555360, baseEnd_1555360] using wordTrace_append hprefix tailTrace_1555360
  have hstable : (prefixWord ++ tailWord_1555360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555360).length < 2 ^ (prefixWord ++ tailWord_1555360).sum := by decide
  have hdescent : baseEnd_1555360 < baseStart_1555360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555362 : List Nat := [3, 3, 1, 2, 2, 3, 2, 6]
def baseStart_1555362 : Nat := 118140960795 + 1555362 * 2 ^ 59
def prefixEnd_1555362 : Nat := 4983230072969 + 3 ^ 40 * 1555362 * 2
def baseEnd_1555362 : Nat := 59159133165811027609039

theorem tailTrace_1555362 : CollatzResearch.WordTrace tailWord_1555362 prefixEnd_1555362 59159133165811027609039 := by
  unfold tailWord_1555362
  simp only [CollatzResearch.WordTrace]
  refine ⟨14182178147799145881613085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37819141727464389017634893 14182178147799145881613085)
  ·
    refine ⟨5318316805424679705604907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14182178147799145881613085 5318316805424679705604907)
    ·
      refine ⟨7977475208137019558407361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5318316805424679705604907 7977475208137019558407361)
      ·
        refine ⟨5983106406102764668805521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7977475208137019558407361 5983106406102764668805521)
        ·
          refine ⟨4487329804577073501604141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5983106406102764668805521 4487329804577073501604141)
          ·
            refine ⟨1682748676716402563101553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4487329804577073501604141 1682748676716402563101553)
            ·
              refine ⟨1262061507537301922326165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1682748676716402563101553 1262061507537301922326165)
              ·
                refine ⟨59159133165811027609039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1262061507537301922326165 59159133165811027609039)
                ·
                  rfl

theorem cell22_1555362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 6].length) (baseStart_1555362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555362 prefixEnd_1555362 := by exact prefixLift 1555362
  have htrace : WordTrace (prefixWord ++ tailWord_1555362) baseStart_1555362 baseEnd_1555362 := by
    simpa [prefixWord, tailWord_1555362, baseEnd_1555362] using wordTrace_append hprefix tailTrace_1555362
  have hstable : (prefixWord ++ tailWord_1555362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555362).length < 2 ^ (prefixWord ++ tailWord_1555362).sum := by decide
  have hdescent : baseEnd_1555362 < baseStart_1555362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555390 : List Nat := [4, 2, 1, 1, 1, 2, 2, 4, 5]
def baseStart_1555390 : Nat := 118140960795 + 1555390 * 2 ^ 59
def prefixEnd_1555390 : Nat := 4983230072969 + 3 ^ 40 * 1555390 * 2
def baseEnd_1555390 : Nat := 177480594488172169593755

theorem tailTrace_1555390 : CollatzResearch.WordTrace tailWord_1555390 prefixEnd_1555390 177480594488172169593755 := by
  unfold tailWord_1555390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7091216729386893038558953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37819822556730096205647749 7091216729386893038558953)
  ·
    refine ⟨5318412547040169778919215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7091216729386893038558953 5318412547040169778919215)
    ·
      refine ⟨7977618820560254668378823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5318412547040169778919215 7977618820560254668378823)
      ·
        refine ⟨11966428230840382002568235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7977618820560254668378823 11966428230840382002568235)
        ·
          refine ⟨17949642346260573003852353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11966428230840382002568235 17949642346260573003852353)
          ·
            refine ⟨13462231759695429752889265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17949642346260573003852353 13462231759695429752889265)
            ·
              refine ⟨10096673819771572314666949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13462231759695429752889265 10096673819771572314666949)
              ·
                refine ⟨1893126341207169809000053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10096673819771572314666949 1893126341207169809000053)
                ·
                  refine ⟨177480594488172169593755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1893126341207169809000053 177480594488172169593755)
                  ·
                    rfl

theorem cell22_1555390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_1555390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555390 prefixEnd_1555390 := by exact prefixLift 1555390
  have htrace : WordTrace (prefixWord ++ tailWord_1555390) baseStart_1555390 baseEnd_1555390 := by
    simpa [prefixWord, tailWord_1555390, baseEnd_1555390] using wordTrace_append hprefix tailTrace_1555390
  have hstable : (prefixWord ++ tailWord_1555390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555390).length < 2 ^ (prefixWord ++ tailWord_1555390).sum := by decide
  have hdescent : baseEnd_1555390 < baseStart_1555390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555407 : List Nat := [1, 1, 2, 1, 1, 8, 2, 1, 5]
def baseStart_1555407 : Nat := 118140960795 + 1555407 * 2 ^ 59
def prefixEnd_1555407 : Nat := 4983230072969 + 3 ^ 40 * 1555407 * 2
def baseEnd_1555407 : Nat := 177482534303978043702071

theorem tailTrace_1555407 : CollatzResearch.WordTrace tailWord_1555407 prefixEnd_1555407 177482534303978043702071 := by
  unfold tailWord_1555407
  simp only [CollatzResearch.WordTrace]
  refine ⟨56730353876033556211840475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37820235917355704141226983 56730353876033556211840475)
  ·
    refine ⟨85095530814050334317760713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56730353876033556211840475 85095530814050334317760713)
    ·
      refine ⟨63821648110537750738320535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85095530814050334317760713 63821648110537750738320535)
      ·
        refine ⟨95732472165806626107480803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63821648110537750738320535 95732472165806626107480803)
        ·
          refine ⟨143598708248709939161221205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95732472165806626107480803 143598708248709939161221205)
          ·
            refine ⟨1682797362289569599545561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 143598708248709939161221205 1682797362289569599545561)
            ·
              refine ⟨1262098021717177199659171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1682797362289569599545561 1262098021717177199659171)
              ·
                refine ⟨1893147032575765799488757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1262098021717177199659171 1893147032575765799488757)
                ·
                  refine ⟨177482534303978043702071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1893147032575765799488757 177482534303978043702071)
                  ·
                    rfl

theorem cell22_1555407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 5].length) (baseStart_1555407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555407 prefixEnd_1555407 := by exact prefixLift 1555407
  have htrace : WordTrace (prefixWord ++ tailWord_1555407) baseStart_1555407 baseEnd_1555407 := by
    simpa [prefixWord, tailWord_1555407, baseEnd_1555407] using wordTrace_append hprefix tailTrace_1555407
  have hstable : (prefixWord ++ tailWord_1555407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555407).length < 2 ^ (prefixWord ++ tailWord_1555407).sum := by decide
  have hdescent : baseEnd_1555407 < baseStart_1555407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555445 : List Nat := [1, 3, 5, 2, 1, 2, 2, 2, 1, 3]
def baseStart_1555445 : Nat := 118140960795 + 1555445 * 2 ^ 59
def prefixEnd_1555445 : Nat := 4983230072969 + 3 ^ 40 * 1555445 * 2
def baseEnd_1555445 : Nat := 532460611088514698656097

theorem tailTrace_1555445 : CollatzResearch.WordTrace tailWord_1555445 prefixEnd_1555445 532460611088514698656097 := by
  unfold tailWord_1555445
  simp only [CollatzResearch.WordTrace]
  refine ⟨56731739849895888701723789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37821159899930592467815859 56731739849895888701723789)
  ·
    refine ⟨21274402443710958263146421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56731739849895888701723789 21274402443710958263146421)
    ·
      refine ⟨1994475229097902337169977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21274402443710958263146421 1994475229097902337169977)
      ·
        refine ⟨1495856421823426752877483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1994475229097902337169977 1495856421823426752877483)
        ·
          refine ⟨2243784632735140129316225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1495856421823426752877483 2243784632735140129316225)
          ·
            refine ⟨1682838474551355096987169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2243784632735140129316225 1682838474551355096987169)
            ·
              refine ⟨1262128855913516322740377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1682838474551355096987169 1262128855913516322740377)
              ·
                refine ⟨946596641935137242055283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1262128855913516322740377 946596641935137242055283)
                ·
                  refine ⟨1419894962902705863082925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 946596641935137242055283 1419894962902705863082925)
                  ·
                    refine ⟨532460611088514698656097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1419894962902705863082925 532460611088514698656097)
                    ·
                      rfl

theorem cell22_1555445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_1555445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555445 prefixEnd_1555445 := by exact prefixLift 1555445
  have htrace : WordTrace (prefixWord ++ tailWord_1555445) baseStart_1555445 baseEnd_1555445 := by
    simpa [prefixWord, tailWord_1555445, baseEnd_1555445] using wordTrace_append hprefix tailTrace_1555445
  have hstable : (prefixWord ++ tailWord_1555445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555445).length < 2 ^ (prefixWord ++ tailWord_1555445).sum := by decide
  have hdescent : baseEnd_1555445 < baseStart_1555445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555448 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 3, 6]
def baseStart_1555448 : Nat := 118140960795 + 1555448 * 2 ^ 59
def prefixEnd_1555448 : Nat := 4983230072969 + 3 ^ 40 * 1555448 * 2
def baseEnd_1555448 : Nat := 532461638049823690831087

theorem tailTrace_1555448 : CollatzResearch.WordTrace tailWord_1555448 prefixEnd_1555448 532461638049823690831087 := by
  unfold tailWord_1555448
  simp only [CollatzResearch.WordTrace]
  refine ⟨28365924634442510107041499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37821232845923346809388665 28365924634442510107041499)
  ·
    refine ⟨42548886951663765160562249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28365924634442510107041499 42548886951663765160562249)
    ·
      refine ⟨31911665213747823870421687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42548886951663765160562249 31911665213747823870421687)
      ·
        refine ⟨47867497820621735805632531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31911665213747823870421687 47867497820621735805632531)
        ·
          refine ⟨71801246730932603708448797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47867497820621735805632531 71801246730932603708448797)
          ·
            refine ⟨26925467524099726390668299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71801246730932603708448797 26925467524099726390668299)
            ·
              refine ⟨40388201286149589586002449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26925467524099726390668299 40388201286149589586002449)
              ·
                refine ⟨30291150964612192189501837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40388201286149589586002449 30291150964612192189501837)
                ·
                  refine ⟨11359181611729572071063189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30291150964612192189501837 11359181611729572071063189)
                  ·
                    refine ⟨532461638049823690831087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11359181611729572071063189 532461638049823690831087)
                    ·
                      rfl

theorem cell22_1555448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_1555448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555448 prefixEnd_1555448 := by exact prefixLift 1555448
  have htrace : WordTrace (prefixWord ++ tailWord_1555448) baseStart_1555448 baseEnd_1555448 := by
    simpa [prefixWord, tailWord_1555448, baseEnd_1555448] using wordTrace_append hprefix tailTrace_1555448
  have hstable : (prefixWord ++ tailWord_1555448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555448).length < 2 ^ (prefixWord ++ tailWord_1555448).sum := by decide
  have hdescent : baseEnd_1555448 < baseStart_1555448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555450 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 4, 3]
def baseStart_1555450 : Nat := 118140960795 + 1555450 * 2 ^ 59
def prefixEnd_1555450 : Nat := 4983230072969 + 3 ^ 40 * 1555450 * 2
def baseEnd_1555450 : Nat := 532462322690696352281081

theorem tailTrace_1555450 : CollatzResearch.WordTrace tailWord_1555450 prefixEnd_1555450 532462322690696352281081 := by
  unfold tailWord_1555450
  simp only [CollatzResearch.WordTrace]
  refine ⟨14182980553719443638913951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37821281476585183037103869 14182980553719443638913951)
  ·
    refine ⟨21274470830579165458370927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14182980553719443638913951 21274470830579165458370927)
    ·
      refine ⟨31911706245868748187556391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21274470830579165458370927 31911706245868748187556391)
      ·
        refine ⟨47867559368803122281334587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31911706245868748187556391 47867559368803122281334587)
        ·
          refine ⟨71801339053204683422001881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47867559368803122281334587 71801339053204683422001881)
          ·
            refine ⟨53851004289903512566501411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71801339053204683422001881 53851004289903512566501411)
            ·
              refine ⟨80776506434855268849752117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53851004289903512566501411 80776506434855268849752117)
              ·
                refine ⟨7572797478267681454664261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80776506434855268849752117 7572797478267681454664261)
                ·
                  refine ⟨1419899527175190272749549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7572797478267681454664261 1419899527175190272749549)
                  ·
                    refine ⟨532462322690696352281081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1419899527175190272749549 532462322690696352281081)
                    ·
                      rfl

theorem cell22_1555450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_1555450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555450 prefixEnd_1555450 := by exact prefixLift 1555450
  have htrace : WordTrace (prefixWord ++ tailWord_1555450) baseStart_1555450 baseEnd_1555450 := by
    simpa [prefixWord, tailWord_1555450, baseEnd_1555450] using wordTrace_append hprefix tailTrace_1555450
  have hstable : (prefixWord ++ tailWord_1555450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555450).length < 2 ^ (prefixWord ++ tailWord_1555450).sum := by decide
  have hdescent : baseEnd_1555450 < baseStart_1555450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555452 : List Nat := [2, 2, 2, 1, 2, 4, 1, 4, 4]
def baseStart_1555452 : Nat := 118140960795 + 1555452 * 2 ^ 59
def prefixEnd_1555452 : Nat := 4983230072969 + 3 ^ 40 * 1555452 * 2
def baseEnd_1555452 : Nat := 177487669110523004577025

theorem tailTrace_1555452 : CollatzResearch.WordTrace tailWord_1555452 prefixEnd_1555452 177487669110523004577025 := by
  unfold tailWord_1555452
  simp only [CollatzResearch.WordTrace]
  refine ⟨28365997580435264448614305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37821330107247019264819073 28365997580435264448614305)
  ·
    refine ⟨21274498185326448336460729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28365997580435264448614305 21274498185326448336460729)
    ·
      refine ⟨15955873638994836252345547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21274498185326448336460729 15955873638994836252345547)
      ·
        refine ⟨23933810458492254378518321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15955873638994836252345547 23933810458492254378518321)
        ·
          refine ⟨17950357843869190783888741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23933810458492254378518321 17950357843869190783888741)
          ·
            refine ⟨3365692095725473271979139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17950357843869190783888741 3365692095725473271979139)
            ·
              refine ⟨5048538143588209907968709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3365692095725473271979139 5048538143588209907968709)
              ·
                refine ⟨946600901922789357744133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5048538143588209907968709 946600901922789357744133)
                ·
                  refine ⟨177487669110523004577025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 946600901922789357744133 177487669110523004577025)
                  ·
                    rfl

theorem cell22_1555452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 4].length) (baseStart_1555452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555452 prefixEnd_1555452 := by exact prefixLift 1555452
  have htrace : WordTrace (prefixWord ++ tailWord_1555452) baseStart_1555452 baseEnd_1555452 := by
    simpa [prefixWord, tailWord_1555452, baseEnd_1555452] using wordTrace_append hprefix tailTrace_1555452
  have hstable : (prefixWord ++ tailWord_1555452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555452).length < 2 ^ (prefixWord ++ tailWord_1555452).sum := by decide
  have hdescent : baseEnd_1555452 < baseStart_1555452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555467 : List Nat := [1, 1, 1, 1, 6, 2, 2, 3, 2, 3]
def baseStart_1555467 : Nat := 118140960795 + 1555467 * 2 ^ 59
def prefixEnd_1555467 : Nat := 4983230072969 + 3 ^ 40 * 1555467 * 2
def baseEnd_1555467 : Nat := 532468142138113974606029

theorem tailTrace_1555467 : CollatzResearch.WordTrace tailWord_1555467 prefixEnd_1555467 532468142138113974606029 := by
  unfold tailWord_1555467
  simp only [CollatzResearch.WordTrace]
  refine ⟨56732542255816186459024655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37821694837210790972683103 56732542255816186459024655)
  ·
    refine ⟨85098813383724279688536983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56732542255816186459024655 85098813383724279688536983)
    ·
      refine ⟨127648220075586419532805475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85098813383724279688536983 127648220075586419532805475)
      ·
        refine ⟨191472330113379629299208213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127648220075586419532805475 191472330113379629299208213)
        ·
          refine ⟨8975265474064670123400385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 191472330113379629299208213 8975265474064670123400385)
          ·
            refine ⟨6731449105548502592550289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8975265474064670123400385 6731449105548502592550289)
            ·
              refine ⟨5048586829161376944412717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6731449105548502592550289 5048586829161376944412717)
              ·
                refine ⟨1893220060935516354154769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5048586829161376944412717 1893220060935516354154769)
                ·
                  refine ⟨1419915045701637265616077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1893220060935516354154769 1419915045701637265616077)
                  ·
                    refine ⟨532468142138113974606029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1419915045701637265616077 532468142138113974606029)
                    ·
                      rfl

theorem cell22_1555467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 3].length) (baseStart_1555467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555467 prefixEnd_1555467 := by exact prefixLift 1555467
  have htrace : WordTrace (prefixWord ++ tailWord_1555467) baseStart_1555467 baseEnd_1555467 := by
    simpa [prefixWord, tailWord_1555467, baseEnd_1555467] using wordTrace_append hprefix tailTrace_1555467
  have hstable : (prefixWord ++ tailWord_1555467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555467).length < 2 ^ (prefixWord ++ tailWord_1555467).sum := by decide
  have hdescent : baseEnd_1555467 < baseStart_1555467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555488 : List Nat := [2, 1, 1, 7, 2, 1, 2, 1, 1, 4]
def baseStart_1555488 : Nat := 118140960795 + 1555488 * 2 ^ 59
def prefixEnd_1555488 : Nat := 4983230072969 + 3 ^ 40 * 1555488 * 2
def baseEnd_1555488 : Nat := 532475330867276919830965

theorem tailTrace_1555488 : CollatzResearch.WordTrace tailWord_1555488 prefixEnd_1555488 532475330867276919830965 := by
  unfold tailWord_1555488
  simp only [CollatzResearch.WordTrace]
  refine ⟨28366654094370053522769559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37822205459160071363692745 28366654094370053522769559)
  ·
    refine ⟨42549981141555080284154339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28366654094370053522769559 42549981141555080284154339)
    ·
      refine ⟨63824971712332620426231509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42549981141555080284154339 63824971712332620426231509)
      ·
        refine ⟨1495897774507795791239801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 63824971712332620426231509 1495897774507795791239801)
        ·
          refine ⟨1121923330880846843429851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1495897774507795791239801 1121923330880846843429851)
          ·
            refine ⟨1682884996321270265144777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1121923330880846843429851 1682884996321270265144777)
            ·
              refine ⟨1262163747240952698858583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1682884996321270265144777 1262163747240952698858583)
              ·
                refine ⟨1893245620861429048287875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1262163747240952698858583 1893245620861429048287875)
                ·
                  refine ⟨2839868431292143572431813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1893245620861429048287875 2839868431292143572431813)
                  ·
                    refine ⟨532475330867276919830965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2839868431292143572431813 532475330867276919830965)
                    ·
                      rfl

theorem cell22_1555488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 1, 4].length) (baseStart_1555488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555488 prefixEnd_1555488 := by exact prefixLift 1555488
  have htrace : WordTrace (prefixWord ++ tailWord_1555488) baseStart_1555488 baseEnd_1555488 := by
    simpa [prefixWord, tailWord_1555488, baseEnd_1555488] using wordTrace_append hprefix tailTrace_1555488
  have hstable : (prefixWord ++ tailWord_1555488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555488).length < 2 ^ (prefixWord ++ tailWord_1555488).sum := by decide
  have hdescent : baseEnd_1555488 < baseStart_1555488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555512 : List Nat := [2, 1, 2, 1, 5, 1, 1, 3, 3, 3]
def baseStart_1555512 : Nat := 118140960795 + 1555512 * 2 ^ 59
def prefixEnd_1555512 : Nat := 4983230072969 + 3 ^ 40 * 1555512 * 2
def baseEnd_1555512 : Nat := 532483546557748857230891

theorem tailTrace_1555512 : CollatzResearch.WordTrace tailWord_1555512 prefixEnd_1555512 532483546557748857230891 := by
  unfold tailWord_1555512
  simp only [CollatzResearch.WordTrace]
  refine ⟨28367091770326579572206395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37822789027102106096275193 28367091770326579572206395)
  ·
    refine ⟨42550637655489869358309593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28367091770326579572206395 42550637655489869358309593)
    ·
      refine ⟨31912978241617402018732195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42550637655489869358309593 31912978241617402018732195)
      ·
        refine ⟨47869467362426103028098293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31912978241617402018732195 47869467362426103028098293)
        ·
          refine ⟨4487762565227447158884215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47869467362426103028098293 4487762565227447158884215)
          ·
            refine ⟨6731643847841170738326323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4487762565227447158884215 6731643847841170738326323)
            ·
              refine ⟨10097465771761756107489485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6731643847841170738326323 10097465771761756107489485)
              ·
                refine ⟨3786549664410658540308557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10097465771761756107489485 3786549664410658540308557)
                ·
                  refine ⟨1419956124153996952615709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3786549664410658540308557 1419956124153996952615709)
                  ·
                    refine ⟨532483546557748857230891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1419956124153996952615709 532483546557748857230891)
                    ·
                      rfl

theorem cell22_1555512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_1555512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555512 prefixEnd_1555512 := by exact prefixLift 1555512
  have htrace : WordTrace (prefixWord ++ tailWord_1555512) baseStart_1555512 baseEnd_1555512 := by
    simpa [prefixWord, tailWord_1555512, baseEnd_1555512] using wordTrace_append hprefix tailTrace_1555512
  have hstable : (prefixWord ++ tailWord_1555512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555512).length < 2 ^ (prefixWord ++ tailWord_1555512).sum := by decide
  have hdescent : baseEnd_1555512 < baseStart_1555512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555525 : List Nat := [1, 3, 1, 1, 1, 3, 2, 5, 5]
def baseStart_1555525 : Nat := 118140960795 + 1555525 * 2 ^ 59
def prefixEnd_1555525 : Nat := 4983230072969 + 3 ^ 40 * 1555525 * 2
def baseEnd_1555525 : Nat := 177495998907807052218617

theorem tailTrace_1555525 : CollatzResearch.WordTrace tailWord_1555525 prefixEnd_1555525 177495998907807052218617 := by
  unfold tailWord_1555525
  simp only [CollatzResearch.WordTrace]
  refine ⟨56734657689606062364636029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37823105126404041576424019 56734657689606062364636029)
  ·
    refine ⟨21275496633602273386738511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56734657689606062364636029 21275496633602273386738511)
    ·
      refine ⟨31913244950403410080107767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21275496633602273386738511 31913244950403410080107767)
      ·
        refine ⟨47869867425605115120161651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31913244950403410080107767 47869867425605115120161651)
        ·
          refine ⟨71804801138407672680242477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47869867425605115120161651 71804801138407672680242477)
          ·
            refine ⟨26926800426902877255090929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71804801138407672680242477 26926800426902877255090929)
            ·
              refine ⟨20195100320177157941318197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26926800426902877255090929 20195100320177157941318197)
              ·
                refine ⟨1893290655016608556998581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20195100320177157941318197 1893290655016608556998581)
                ·
                  refine ⟨177495998907807052218617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1893290655016608556998581 177495998907807052218617)
                  ·
                    rfl

theorem cell22_1555525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_1555525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555525 prefixEnd_1555525 := by exact prefixLift 1555525
  have htrace : WordTrace (prefixWord ++ tailWord_1555525) baseStart_1555525 baseEnd_1555525 := by
    simpa [prefixWord, tailWord_1555525, baseEnd_1555525] using wordTrace_append hprefix tailTrace_1555525
  have hstable : (prefixWord ++ tailWord_1555525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555525).length < 2 ^ (prefixWord ++ tailWord_1555525).sum := by decide
  have hdescent : baseEnd_1555525 < baseStart_1555525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555540 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_1555540 : Nat := 118140960795 + 1555540 * 2 ^ 59
def prefixEnd_1555540 : Nat := 4983230072969 + 3 ^ 40 * 1555540 * 2
def baseEnd_1555540 : Nat := 532493131529966117530805

theorem tailTrace_1555540 : CollatzResearch.WordTrace tailWord_1555540 prefixEnd_1555540 532493131529966117530805 := by
  unfold tailWord_1555540
  simp only [CollatzResearch.WordTrace]
  refine ⟨28367602392275859963216037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37823469856367813284288049 28367602392275859963216037)
  ·
    refine ⟨5318925448551723743103007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28367602392275859963216037 5318925448551723743103007)
    ·
      refine ⟨7978388172827585614654511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5318925448551723743103007 7978388172827585614654511)
      ·
        refine ⟨11967582259241378421981767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7978388172827585614654511 11967582259241378421981767)
        ·
          refine ⟨17951373388862067632972651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11967582259241378421981767 17951373388862067632972651)
          ·
            refine ⟨26927060083293101449458977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17951373388862067632972651 26927060083293101449458977)
            ·
              refine ⟨20195295062469826087094233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26927060083293101449458977 20195295062469826087094233)
              ·
                refine ⟨15146471296852369565320675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20195295062469826087094233 15146471296852369565320675)
                ·
                  refine ⟨22719706945278554347981013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15146471296852369565320675 22719706945278554347981013)
                  ·
                    refine ⟨532493131529966117530805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22719706945278554347981013 532493131529966117530805)
                    ·
                      rfl

theorem cell22_1555540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_1555540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555540 prefixEnd_1555540 := by exact prefixLift 1555540
  have htrace : WordTrace (prefixWord ++ tailWord_1555540) baseStart_1555540 baseEnd_1555540 := by
    simpa [prefixWord, tailWord_1555540, baseEnd_1555540] using wordTrace_append hprefix tailTrace_1555540
  have hstable : (prefixWord ++ tailWord_1555540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555540).length < 2 ^ (prefixWord ++ tailWord_1555540).sum := by decide
  have hdescent : baseEnd_1555540 < baseStart_1555540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555555 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 5, 4]
def baseStart_1555555 : Nat := 118140960795 + 1555555 * 2 ^ 59
def prefixEnd_1555555 : Nat := 4983230072969 + 3 ^ 40 * 1555555 * 2
def baseEnd_1555555 : Nat := 532498266336511078405759

theorem tailTrace_1555555 : CollatzResearch.WordTrace tailWord_1555555 prefixEnd_1555555 532498266336511078405759 := by
  unfold tailWord_1555555
  simp only [CollatzResearch.WordTrace]
  refine ⟨56735751879497377488228119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37823834586331584992152079 56735751879497377488228119)
  ·
    refine ⟨85103627819246066232342179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56735751879497377488228119 85103627819246066232342179)
    ·
      refine ⟨127655441728869099348513269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85103627819246066232342179 127655441728869099348513269)
      ·
        refine ⟨11967697662081478063923119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127655441728869099348513269 11967697662081478063923119)
        ·
          refine ⟨17951546493122217095884679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11967697662081478063923119 17951546493122217095884679)
          ·
            refine ⟨26927319739683325643827019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17951546493122217095884679 26927319739683325643827019)
            ·
              refine ⟨40390979609524988465740529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26927319739683325643827019 40390979609524988465740529)
              ·
                refine ⟨30293234707143741349305397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40390979609524988465740529 30293234707143741349305397)
                ·
                  refine ⟨2839990753794725751497381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30293234707143741349305397 2839990753794725751497381)
                  ·
                    refine ⟨532498266336511078405759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2839990753794725751497381 532498266336511078405759)
                    ·
                      rfl

theorem cell22_1555555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 4].length) (baseStart_1555555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555555 prefixEnd_1555555 := by exact prefixLift 1555555
  have htrace : WordTrace (prefixWord ++ tailWord_1555555) baseStart_1555555 baseEnd_1555555 := by
    simpa [prefixWord, tailWord_1555555, baseEnd_1555555] using wordTrace_append hprefix tailTrace_1555555
  have hstable : (prefixWord ++ tailWord_1555555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555555).length < 2 ^ (prefixWord ++ tailWord_1555555).sum := by decide
  have hdescent : baseEnd_1555555 < baseStart_1555555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555602 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_1555602 : Nat := 118140960795 + 1555602 * 2 ^ 59
def prefixEnd_1555602 : Nat := 4983230072969 + 3 ^ 40 * 1555602 * 2
def baseEnd_1555602 : Nat := 532514355397018622480615

theorem tailTrace_1555602 : CollatzResearch.WordTrace tailWord_1555602 prefixEnd_1555602 532514355397018622480615 := by
  unfold tailWord_1555602
  simp only [CollatzResearch.WordTrace]
  refine ⟨14184366527581776128797265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37824977406884736343459373 14184366527581776128797265)
  ·
    refine ⟨10638274895686332096597949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14184366527581776128797265 10638274895686332096597949)
    ·
      refine ⟨3989353085882374536224231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10638274895686332096597949 3989353085882374536224231)
      ·
        refine ⟨5984029628823561804336347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3989353085882374536224231 5984029628823561804336347)
        ·
          refine ⟨8976044443235342706504521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5984029628823561804336347 8976044443235342706504521)
          ·
            refine ⟨6732033332426507029878391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8976044443235342706504521 6732033332426507029878391)
            ·
              refine ⟨10098049998639760544817587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6732033332426507029878391 10098049998639760544817587)
              ·
                refine ⟨15147074997959640817226381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10098049998639760544817587 15147074997959640817226381)
                ·
                  refine ⟨5680153124234865306459893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15147074997959640817226381 5680153124234865306459893)
                  ·
                    refine ⟨532514355397018622480615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5680153124234865306459893 532514355397018622480615)
                    ·
                      rfl

theorem cell22_1555602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_1555602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555602 prefixEnd_1555602 := by exact prefixLift 1555602
  have htrace : WordTrace (prefixWord ++ tailWord_1555602) baseStart_1555602 baseEnd_1555602 := by
    simpa [prefixWord, tailWord_1555602, baseEnd_1555602] using wordTrace_append hprefix tailTrace_1555602
  have hstable : (prefixWord ++ tailWord_1555602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555602).length < 2 ^ (prefixWord ++ tailWord_1555602).sum := by decide
  have hdescent : baseEnd_1555602 < baseStart_1555602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555615 : List Nat := [1, 1, 2, 6, 12]
def baseStart_1555615 : Nat := 118140960795 + 1555615 * 2 ^ 59
def prefixEnd_1555615 : Nat := 4983230072969 + 3 ^ 40 * 1555615 * 2
def baseEnd_1555615 : Nat := 2191435413838234246525

theorem tailTrace_1555615 : CollatzResearch.WordTrace tailWord_1555615 prefixEnd_1555615 2191435413838234246525 := by
  unfold tailWord_1555615
  simp only [CollatzResearch.WordTrace]
  refine ⟨56737940259280007735412299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37825293506186671823608199 56737940259280007735412299)
  ·
    refine ⟨85106910388920011603118449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56737940259280007735412299 85106910388920011603118449)
    ·
      refine ⟨63830182791690008702338837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85106910388920011603118449 63830182791690008702338837)
      ·
        refine ⟨2992039818360469157922133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63830182791690008702338837 2992039818360469157922133)
        ·
          refine ⟨2191435413838234246525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2992039818360469157922133 2191435413838234246525)
          ·
            rfl

theorem cell22_1555615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 12].length) (baseStart_1555615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555615 prefixEnd_1555615 := by exact prefixLift 1555615
  have htrace : WordTrace (prefixWord ++ tailWord_1555615) baseStart_1555615 baseEnd_1555615 := by
    simpa [prefixWord, tailWord_1555615, baseEnd_1555615] using wordTrace_append hprefix tailTrace_1555615
  have hstable : (prefixWord ++ tailWord_1555615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555615).length < 2 ^ (prefixWord ++ tailWord_1555615).sum := by decide
  have hdescent : baseEnd_1555615 < baseStart_1555615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555617 : List Nat := [1, 2, 3, 3, 1, 1, 1, 4, 2, 4]
def baseStart_1555617 : Nat := 118140960795 + 1555617 * 2 ^ 59
def prefixEnd_1555617 : Nat := 4983230072969 + 3 ^ 40 * 1555617 * 2
def baseEnd_1555617 : Nat := 532519490203563583355569

theorem tailTrace_1555617 : CollatzResearch.WordTrace tailWord_1555617 prefixEnd_1555617 532519490203563583355569 := by
  unfold tailWord_1555617
  simp only [CollatzResearch.WordTrace]
  refine ⟨56738013205272762076985105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37825342136848508051323403 56738013205272762076985105)
  ·
    refine ⟨42553509903954571557738829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56738013205272762076985105 42553509903954571557738829)
    ·
      refine ⟨15957566213982964334152061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42553509903954571557738829 15957566213982964334152061)
      ·
        refine ⟨5984087330243611625307023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15957566213982964334152061 5984087330243611625307023)
        ·
          refine ⟨8976130995365417437960535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5984087330243611625307023 8976130995365417437960535)
          ·
            refine ⟨13464196493048126156940803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8976130995365417437960535 13464196493048126156940803)
            ·
              refine ⟨20196294739572189235411205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13464196493048126156940803 20196294739572189235411205)
              ·
                refine ⟨3786805263669785481639601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20196294739572189235411205 3786805263669785481639601)
                ·
                  refine ⟨2840103947752339111229701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3786805263669785481639601 2840103947752339111229701)
                  ·
                    refine ⟨532519490203563583355569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2840103947752339111229701 532519490203563583355569)
                    ·
                      rfl

theorem cell22_1555617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_1555617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555617 prefixEnd_1555617 := by exact prefixLift 1555617
  have htrace : WordTrace (prefixWord ++ tailWord_1555617) baseStart_1555617 baseEnd_1555617 := by
    simpa [prefixWord, tailWord_1555617, baseEnd_1555617] using wordTrace_append hprefix tailTrace_1555617
  have hstable : (prefixWord ++ tailWord_1555617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555617).length < 2 ^ (prefixWord ++ tailWord_1555617).sum := by decide
  have hdescent : baseEnd_1555617 < baseStart_1555617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555621 : List Nat := [1, 3, 1, 2, 1, 6, 2, 2, 4]
def baseStart_1555621 : Nat := 118140960795 + 1555621 * 2 ^ 59
def prefixEnd_1555621 : Nat := 4983230072969 + 3 ^ 40 * 1555621 * 2
def baseEnd_1555621 : Nat := 177506953161769635418519

theorem tailTrace_1555621 : CollatzResearch.WordTrace tailWord_1555621 prefixEnd_1555621 177506953161769635418519 := by
  unfold tailWord_1555621
  simp only [CollatzResearch.WordTrace]
  refine ⟨56738159097258270760130717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37825439398172180506753811 56738159097258270760130717)
  ·
    refine ⟨21276809661471851535049019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56738159097258270760130717 21276809661471851535049019)
    ·
      refine ⟨31915214492207777302573529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21276809661471851535049019 31915214492207777302573529)
      ·
        refine ⟨23936410869155832976930147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31915214492207777302573529 23936410869155832976930147)
        ·
          refine ⟨35904616303733749465395221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23936410869155832976930147 35904616303733749465395221)
          ·
            refine ⟨1683028889237519506190401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35904616303733749465395221 1683028889237519506190401)
            ·
              refine ⟨1262271666928139629642801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1683028889237519506190401 1262271666928139629642801)
              ·
                refine ⟨946703750196104722232101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1262271666928139629642801 946703750196104722232101)
                ·
                  refine ⟨177506953161769635418519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 946703750196104722232101 177506953161769635418519)
                  ·
                    rfl

theorem cell22_1555621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 4].length) (baseStart_1555621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555621 prefixEnd_1555621 := by exact prefixLift 1555621
  have htrace : WordTrace (prefixWord ++ tailWord_1555621) baseStart_1555621 baseEnd_1555621 := by
    simpa [prefixWord, tailWord_1555621, baseEnd_1555621] using wordTrace_append hprefix tailTrace_1555621
  have hstable : (prefixWord ++ tailWord_1555621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555621).length < 2 ^ (prefixWord ++ tailWord_1555621).sum := by decide
  have hdescent : baseEnd_1555621 < baseStart_1555621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555647 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 5, 3]
def baseStart_1555647 : Nat := 118140960795 + 1555647 * 2 ^ 59
def prefixEnd_1555647 : Nat := 4983230072969 + 3 ^ 40 * 1555647 * 2
def baseEnd_1555647 : Nat := 532529759816653505105477

theorem tailTrace_1555647 : CollatzResearch.WordTrace tailWord_1555647 prefixEnd_1555647 532529759816653505105477 := by
  unfold tailWord_1555647
  simp only [CollatzResearch.WordTrace]
  refine ⟨56739107395164077200577195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37826071596776051467051463 56739107395164077200577195)
  ·
    refine ⟨85108661092746115800865793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56739107395164077200577195 85108661092746115800865793)
    ·
      refine ⟨63831495819559586850649345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85108661092746115800865793 63831495819559586850649345)
      ·
        refine ⟨47873621864669690137987009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63831495819559586850649345 47873621864669690137987009)
        ·
          refine ⟨35905216398502267603490257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47873621864669690137987009 35905216398502267603490257)
          ·
            refine ⟨26928912298876700702617693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35905216398502267603490257 26928912298876700702617693)
            ·
              refine ⟨10098342112078762763481635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26928912298876700702617693 10098342112078762763481635)
              ·
                refine ⟨15147513168118144145222453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10098342112078762763481635 15147513168118144145222453)
                ·
                  refine ⟨1420079359511076013614605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15147513168118144145222453 1420079359511076013614605)
                  ·
                    refine ⟨532529759816653505105477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1420079359511076013614605 532529759816653505105477)
                    ·
                      rfl

theorem cell22_1555647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 3].length) (baseStart_1555647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555647 prefixEnd_1555647 := by exact prefixLift 1555647
  have htrace : WordTrace (prefixWord ++ tailWord_1555647) baseStart_1555647 baseEnd_1555647 := by
    simpa [prefixWord, tailWord_1555647, baseEnd_1555647] using wordTrace_append hprefix tailTrace_1555647
  have hstable : (prefixWord ++ tailWord_1555647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555647).length < 2 ^ (prefixWord ++ tailWord_1555647).sum := by decide
  have hdescent : baseEnd_1555647 < baseStart_1555647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555670 : List Nat := [5, 2, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_1555670 : Nat := 118140960795 + 1555670 * 2 ^ 59
def prefixEnd_1555670 : Nat := 4983230072969 + 3 ^ 40 * 1555670 * 2
def baseEnd_1555670 : Nat := 532537633186689111780407

theorem tailTrace_1555670 : CollatzResearch.WordTrace tailWord_1555670 prefixEnd_1555670 532537633186689111780407 := by
  unfold tailWord_1555670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3546246642130047008041529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37826630849387168085776309 3546246642130047008041529)
  ·
    refine ⟨2659684981597535256031147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3546246642130047008041529 2659684981597535256031147)
    ·
      refine ⟨3989527472396302884046721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2659684981597535256031147 3989527472396302884046721)
      ·
        refine ⟨2992145604297227163035041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3989527472396302884046721 2992145604297227163035041)
        ·
          refine ⟨2244109203222920372276281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2992145604297227163035041 2244109203222920372276281)
          ·
            refine ⟨1683081902417190279207211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2244109203222920372276281 1683081902417190279207211)
            ·
              refine ⟨2524622853625785418810817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1683081902417190279207211 2524622853625785418810817)
              ·
                refine ⟨1893467140219339064108113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2524622853625785418810817 1893467140219339064108113)
                ·
                  refine ⟨1420100355164504298081085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1893467140219339064108113 1420100355164504298081085)
                  ·
                    refine ⟨532537633186689111780407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1420100355164504298081085 532537633186689111780407)
                    ·
                      rfl

theorem cell22_1555670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_1555670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555670 prefixEnd_1555670 := by exact prefixLift 1555670
  have htrace : WordTrace (prefixWord ++ tailWord_1555670) baseStart_1555670 baseEnd_1555670 := by
    simpa [prefixWord, tailWord_1555670, baseEnd_1555670] using wordTrace_append hprefix tailTrace_1555670
  have hstable : (prefixWord ++ tailWord_1555670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555670).length < 2 ^ (prefixWord ++ tailWord_1555670).sum := by decide
  have hdescent : baseEnd_1555670 < baseStart_1555670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555681 : List Nat := [1, 2, 3, 1, 3, 2, 2, 4, 1, 3]
def baseStart_1555681 : Nat := 118140960795 + 1555681 * 2 ^ 59
def prefixEnd_1555681 : Nat := 4983230072969 + 3 ^ 40 * 1555681 * 2
def baseEnd_1555681 : Nat := 532541398711488749755373

theorem tailTrace_1555681 : CollatzResearch.WordTrace tailWord_1555681 prefixEnd_1555681 532541398711488749755373 := by
  unfold tailWord_1555681
  simp only [CollatzResearch.WordTrace]
  refine ⟨56740347477040901007314897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37826898318027267338209931 56740347477040901007314897)
  ·
    refine ⟨42555260607780675755486173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56740347477040901007314897 42555260607780675755486173)
    ·
      refine ⟨15958222727917753408307315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42555260607780675755486173 15958222727917753408307315)
      ·
        refine ⟨23937334091876630112460973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15958222727917753408307315 23937334091876630112460973)
        ·
          refine ⟨8976500284453736292172865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23937334091876630112460973 8976500284453736292172865)
          ·
            refine ⟨6732375213340302219129649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8976500284453736292172865 6732375213340302219129649)
            ·
              refine ⟨5049281410005226664347237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6732375213340302219129649 5049281410005226664347237)
              ·
                refine ⟨946740264375979999565107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5049281410005226664347237 946740264375979999565107)
                ·
                  refine ⟨1420110396563969999347661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 946740264375979999565107 1420110396563969999347661)
                  ·
                    refine ⟨532541398711488749755373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1420110396563969999347661 532541398711488749755373)
                    ·
                      rfl

theorem cell22_1555681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_1555681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555681 prefixEnd_1555681 := by exact prefixLift 1555681
  have htrace : WordTrace (prefixWord ++ tailWord_1555681) baseStart_1555681 baseEnd_1555681 := by
    simpa [prefixWord, tailWord_1555681, baseEnd_1555681] using wordTrace_append hprefix tailTrace_1555681
  have hstable : (prefixWord ++ tailWord_1555681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555681).length < 2 ^ (prefixWord ++ tailWord_1555681).sum := by decide
  have hdescent : baseEnd_1555681 < baseStart_1555681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555692 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 2, 5]
def baseStart_1555692 : Nat := 118140960795 + 1555692 * 2 ^ 59
def prefixEnd_1555692 : Nat := 4983230072969 + 3 ^ 40 * 1555692 * 2
def baseEnd_1555692 : Nat := 532545164236288387730339

theorem tailTrace_1555692 : CollatzResearch.WordTrace tailWord_1555692 prefixEnd_1555692 532545164236288387730339 := by
  unfold tailWord_1555692
  simp only [CollatzResearch.WordTrace]
  refine ⟨28370374340000524942982665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37827165786667366590643553 28370374340000524942982665)
  ·
    refine ⟨21277780755000393707236999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28370374340000524942982665 21277780755000393707236999)
    ·
      refine ⟨31916671132500590560855499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21277780755000393707236999 31916671132500590560855499)
      ·
        refine ⟨47875006698750885841283249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31916671132500590560855499 47875006698750885841283249)
        ·
          refine ⟨35906255024063164380962437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47875006698750885841283249 35906255024063164380962437)
          ·
            refine ⟨6732422817011843321430457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35906255024063164380962437 6732422817011843321430457)
            ·
              refine ⟨5049317112758882491072843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6732422817011843321430457 5049317112758882491072843)
              ·
                refine ⟨7573975669138323736609265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5049317112758882491072843 7573975669138323736609265)
                ·
                  refine ⟨5680481751853742802456949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7573975669138323736609265 5680481751853742802456949)
                  ·
                    refine ⟨532545164236288387730339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5680481751853742802456949 532545164236288387730339)
                    ·
                      rfl

theorem cell22_1555692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_1555692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555692 prefixEnd_1555692 := by exact prefixLift 1555692
  have htrace : WordTrace (prefixWord ++ tailWord_1555692) baseStart_1555692 baseEnd_1555692 := by
    simpa [prefixWord, tailWord_1555692, baseEnd_1555692] using wordTrace_append hprefix tailTrace_1555692
  have hstable : (prefixWord ++ tailWord_1555692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555692).length < 2 ^ (prefixWord ++ tailWord_1555692).sum := by decide
  have hdescent : baseEnd_1555692 < baseStart_1555692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555700 : List Nat := [2, 6, 1, 2, 1, 2, 2, 6]
def baseStart_1555700 : Nat := 118140960795 + 1555700 * 2 ^ 59
def prefixEnd_1555700 : Nat := 4983230072969 + 3 ^ 40 * 1555700 * 2
def baseEnd_1555700 : Nat := 59171989199975448170035

theorem tailTrace_1555700 : CollatzResearch.WordTrace tailWord_1555700 prefixEnd_1555700 59171989199975448170035 := by
  unfold tailWord_1555700
  simp only [CollatzResearch.WordTrace]
  refine ⟨28370520231986033626128277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37827360309314711501504369 28370520231986033626128277)
  ·
    refine ⟨1329868135874345326224763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28370520231986033626128277 1329868135874345326224763)
    ·
      refine ⟨1994802203811517989337145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1329868135874345326224763 1994802203811517989337145)
      ·
        refine ⟨1496101652858638492002859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1994802203811517989337145 1496101652858638492002859)
        ·
          refine ⟨2244152479287957738004289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1496101652858638492002859 2244152479287957738004289)
          ·
            refine ⟨1683114359465968303503217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2244152479287957738004289 1683114359465968303503217)
            ·
              refine ⟨1262335769599476227627413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1683114359465968303503217 1262335769599476227627413)
              ·
                refine ⟨59171989199975448170035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1262335769599476227627413 59171989199975448170035)
                ·
                  rfl

theorem cell22_1555700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 6].length) (baseStart_1555700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555700 prefixEnd_1555700 := by exact prefixLift 1555700
  have htrace : WordTrace (prefixWord ++ tailWord_1555700) baseStart_1555700 baseEnd_1555700 := by
    simpa [prefixWord, tailWord_1555700, baseEnd_1555700] using wordTrace_append hprefix tailTrace_1555700
  have hstable : (prefixWord ++ tailWord_1555700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555700).length < 2 ^ (prefixWord ++ tailWord_1555700).sum := by decide
  have hdescent : baseEnd_1555700 < baseStart_1555700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555724 : List Nat := [2, 2, 1, 2, 2, 3, 2, 3, 1, 4]
def baseStart_1555724 : Nat := 118140960795 + 1555724 * 2 ^ 59
def prefixEnd_1555724 : Nat := 4983230072969 + 3 ^ 40 * 1555724 * 2
def baseEnd_1555724 : Nat := 532556118490250970930241

theorem tailTrace_1555724 : CollatzResearch.WordTrace tailWord_1555724 prefixEnd_1555724 532556118490250970930241 := by
  unfold tailWord_1555724
  simp only [CollatzResearch.WordTrace]
  refine ⟨28370957907942559675565113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37827943877256746234086817 28370957907942559675565113)
  ·
    refine ⟨21278218430956919756673835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28370957907942559675565113 21278218430956919756673835)
    ·
      refine ⟨31917327646435379635010753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21278218430956919756673835 31917327646435379635010753)
      ·
        refine ⟨23937995734826534726258065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31917327646435379635010753 23937995734826534726258065)
        ·
          refine ⟨17953496801119901044693549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23937995734826534726258065 17953496801119901044693549)
          ·
            refine ⟨6732561300419962891760081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17953496801119901044693549 6732561300419962891760081)
            ·
              refine ⟨5049420975314972168820061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6732561300419962891760081 5049420975314972168820061)
              ·
                refine ⟨1893532865743114563307523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5049420975314972168820061 1893532865743114563307523)
                ·
                  refine ⟨2840299298614671844961285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1893532865743114563307523 2840299298614671844961285)
                  ·
                    refine ⟨532556118490250970930241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2840299298614671844961285 532556118490250970930241)
                    ·
                      rfl

theorem cell22_1555724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_1555724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555724 prefixEnd_1555724 := by exact prefixLift 1555724
  have htrace : WordTrace (prefixWord ++ tailWord_1555724) baseStart_1555724 baseEnd_1555724 := by
    simpa [prefixWord, tailWord_1555724, baseEnd_1555724] using wordTrace_append hprefix tailTrace_1555724
  have hstable : (prefixWord ++ tailWord_1555724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555724).length < 2 ^ (prefixWord ++ tailWord_1555724).sum := by decide
  have hdescent : baseEnd_1555724 < baseStart_1555724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555805 : List Nat := [1, 4, 5, 1, 1, 1, 2, 1, 1, 5]
def baseStart_1555805 : Nat := 118140960795 + 1555805 * 2 ^ 59
def prefixEnd_1555805 : Nat := 4983230072969 + 3 ^ 40 * 1555805 * 2
def baseEnd_1555805 : Nat := 532583846445593759654993

theorem tailTrace_1555805 : CollatzResearch.WordTrace tailWord_1555805 prefixEnd_1555805 532583846445593759654993 := by
  unfold tailWord_1555805
  simp only [CollatzResearch.WordTrace]
  refine ⟨56744870128591670184828869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37829913419061113456552579 56744870128591670184828869)
  ·
    refine ⟨10639663149110938159655413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56744870128591670184828869 10639663149110938159655413)
    ·
      refine ⟨997468420229150452467695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10639663149110938159655413 997468420229150452467695)
      ·
        refine ⟨1496202630343725678701543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 997468420229150452467695 1496202630343725678701543)
        ·
          refine ⟨2244303945515588518052315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1496202630343725678701543 2244303945515588518052315)
          ·
            refine ⟨3366455918273382777078473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244303945515588518052315 3366455918273382777078473)
            ·
              refine ⟨2524841938705037082808855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3366455918273382777078473 2524841938705037082808855)
              ·
                refine ⟨3787262908057555624213283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2524841938705037082808855 3787262908057555624213283)
                ·
                  refine ⟨5680894362086333436319925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3787262908057555624213283 5680894362086333436319925)
                  ·
                    refine ⟨532583846445593759654993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5680894362086333436319925 532583846445593759654993)
                    ·
                      rfl

theorem cell22_1555805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_1555805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555805 prefixEnd_1555805 := by exact prefixLift 1555805
  have htrace : WordTrace (prefixWord ++ tailWord_1555805) baseStart_1555805 baseEnd_1555805 := by
    simpa [prefixWord, tailWord_1555805, baseEnd_1555805] using wordTrace_append hprefix tailTrace_1555805
  have hstable : (prefixWord ++ tailWord_1555805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555805).length < 2 ^ (prefixWord ++ tailWord_1555805).sum := by decide
  have hdescent : baseEnd_1555805 < baseStart_1555805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555827 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 6, 5]
def baseStart_1555827 : Nat := 118140960795 + 1555827 * 2 ^ 59
def prefixEnd_1555827 : Nat := 4983230072969 + 3 ^ 40 * 1555827 * 2
def baseEnd_1555827 : Nat := 532591377495193035604925

theorem tailTrace_1555827 : CollatzResearch.WordTrace tailWord_1555827 prefixEnd_1555827 532591377495193035604925 := by
  unfold tailWord_1555827
  simp only [CollatzResearch.WordTrace]
  refine ⟨56745672534511967942129735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37830448356341311961419823 56745672534511967942129735)
  ·
    refine ⟨85118508801767951913194603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56745672534511967942129735 85118508801767951913194603)
    ·
      refine ⟨127677763202651927869791905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85118508801767951913194603 127677763202651927869791905)
      ·
        refine ⟨95758322401988945902343929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127677763202651927869791905 95758322401988945902343929)
        ·
          refine ⟨71818741801491709426757947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95758322401988945902343929 71818741801491709426757947)
          ·
            refine ⟨107728112702237564140136921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71818741801491709426757947 107728112702237564140136921)
            ·
              refine ⟨80796084526678173105102691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107728112702237564140136921 80796084526678173105102691)
              ·
                refine ⟨121194126790017259657654037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80796084526678173105102691 121194126790017259657654037)
                ·
                  refine ⟨5680974693282059046452533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121194126790017259657654037 5680974693282059046452533)
                  ·
                    refine ⟨532591377495193035604925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5680974693282059046452533 532591377495193035604925)
                    ·
                      rfl

theorem cell22_1555827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 5].length) (baseStart_1555827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555827 prefixEnd_1555827 := by exact prefixLift 1555827
  have htrace : WordTrace (prefixWord ++ tailWord_1555827) baseStart_1555827 baseEnd_1555827 := by
    simpa [prefixWord, tailWord_1555827, baseEnd_1555827] using wordTrace_append hprefix tailTrace_1555827
  have hstable : (prefixWord ++ tailWord_1555827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555827).length < 2 ^ (prefixWord ++ tailWord_1555827).sum := by decide
  have hdescent : baseEnd_1555827 < baseStart_1555827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555844 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_1555844 : Nat := 118140960795 + 1555844 * 2 ^ 59
def prefixEnd_1555844 : Nat := 4983230072969 + 3 ^ 40 * 1555844 * 2
def baseEnd_1555844 : Nat := 532597196942610657929873

theorem tailTrace_1555844 : CollatzResearch.WordTrace tailWord_1555844 prefixEnd_1555844 532597196942610657929873 := by
  unfold tailWord_1555844
  simp only [CollatzResearch.WordTrace]
  refine ⟨28373146287725189922749293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37830861716966919896999057 28373146287725189922749293)
  ·
    refine ⟨10639929857896946221030985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28373146287725189922749293 10639929857896946221030985)
    ·
      refine ⟨7979947393422709665773239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10639929857896946221030985 7979947393422709665773239)
      ·
        refine ⟨11969921090134064498659859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7979947393422709665773239 11969921090134064498659859)
        ·
          refine ⟨17954881635201096747989789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11969921090134064498659859 17954881635201096747989789)
          ·
            refine ⟨6733080613200411280496171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17954881635201096747989789 6733080613200411280496171)
            ·
              refine ⟨10099620919800616920744257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6733080613200411280496171 10099620919800616920744257)
              ·
                refine ⟨7574715689850462690558193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10099620919800616920744257 7574715689850462690558193)
                ·
                  refine ⟨5681036767387847017918645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7574715689850462690558193 5681036767387847017918645)
                  ·
                    refine ⟨532597196942610657929873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5681036767387847017918645 532597196942610657929873)
                    ·
                      rfl

theorem cell22_1555844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_1555844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555844 prefixEnd_1555844 := by exact prefixLift 1555844
  have htrace : WordTrace (prefixWord ++ tailWord_1555844) baseStart_1555844 baseEnd_1555844 := by
    simpa [prefixWord, tailWord_1555844, baseEnd_1555844] using wordTrace_append hprefix tailTrace_1555844
  have hstable : (prefixWord ++ tailWord_1555844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555844).length < 2 ^ (prefixWord ++ tailWord_1555844).sum := by decide
  have hdescent : baseEnd_1555844 < baseStart_1555844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555857 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 10]
def baseStart_1555857 : Nat := 118140960795 + 1555857 * 2 ^ 59
def prefixEnd_1555857 : Nat := 4983230072969 + 3 ^ 40 * 1555857 * 2
def baseEnd_1555857 : Nat := 177533882369427652451611

theorem tailTrace_1555857 : CollatzResearch.WordTrace tailWord_1555857 prefixEnd_1555857 177533882369427652451611 := by
  unfold tailWord_1555857
  simp only [CollatzResearch.WordTrace]
  refine ⟨56746766724403283065721825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37831177816268855377147883 56746766724403283065721825)
  ·
    refine ⟨42560075043302462299291369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56746766724403283065721825 42560075043302462299291369)
    ·
      refine ⟨31920056282476846724468527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42560075043302462299291369 31920056282476846724468527)
      ·
        refine ⟨47880084423715270086702791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31920056282476846724468527 47880084423715270086702791)
        ·
          refine ⟨71820126635572905130054187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47880084423715270086702791 71820126635572905130054187)
          ·
            refine ⟨107730189953359357695081281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71820126635572905130054187 107730189953359357695081281)
            ·
              refine ⟨80797642465019518271310961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107730189953359357695081281 80797642465019518271310961)
              ·
                refine ⟨60598231848764638703483221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80797642465019518271310961 60598231848764638703483221)
                ·
                  refine ⟨177533882369427652451611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 60598231848764638703483221 177533882369427652451611)
                  ·
                    rfl

theorem cell22_1555857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 10].length) (baseStart_1555857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555857 prefixEnd_1555857 := by exact prefixLift 1555857
  have htrace : WordTrace (prefixWord ++ tailWord_1555857) baseStart_1555857 baseEnd_1555857 := by
    simpa [prefixWord, tailWord_1555857, baseEnd_1555857] using wordTrace_append hprefix tailTrace_1555857
  have hstable : (prefixWord ++ tailWord_1555857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555857).length < 2 ^ (prefixWord ++ tailWord_1555857).sum := by decide
  have hdescent : baseEnd_1555857 < baseStart_1555857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555889 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 3, 5]
def baseStart_1555889 : Nat := 118140960795 + 1555889 * 2 ^ 59
def prefixEnd_1555889 : Nat := 4983230072969 + 3 ^ 40 * 1555889 * 2
def baseEnd_1555889 : Nat := 532612601362245540554735

theorem tailTrace_1555889 : CollatzResearch.WordTrace tailWord_1555889 prefixEnd_1555889 532612601362245540554735 := by
  unfold tailWord_1555889
  simp only [CollatzResearch.WordTrace]
  refine ⟨56747933860287352530886721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37831955906858235020591147 56747933860287352530886721)
  ·
    refine ⟨42560950395215514398165041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56747933860287352530886721 42560950395215514398165041)
    ·
      refine ⟨31920712796411635798623781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42560950395215514398165041 31920712796411635798623781)
      ·
        refine ⟨5985133649327181712241959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31920712796411635798623781 5985133649327181712241959)
        ·
          refine ⟨8977700473990772568362939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5985133649327181712241959 8977700473990772568362939)
          ·
            refine ⟨13466550710986158852544409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8977700473990772568362939 13466550710986158852544409)
            ·
              refine ⟨10099913033239619139408307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13466550710986158852544409 10099913033239619139408307)
              ·
                refine ⟨15149869549859428709112461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10099913033239619139408307 15149869549859428709112461)
                ·
                  refine ⟨5681201081197285765917173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15149869549859428709112461 5681201081197285765917173)
                  ·
                    refine ⟨532612601362245540554735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5681201081197285765917173 532612601362245540554735)
                    ·
                      rfl

theorem cell22_1555889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_1555889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555889 prefixEnd_1555889 := by exact prefixLift 1555889
  have htrace : WordTrace (prefixWord ++ tailWord_1555889) baseStart_1555889 baseEnd_1555889 := by
    simpa [prefixWord, tailWord_1555889, baseEnd_1555889] using wordTrace_append hprefix tailTrace_1555889
  have hstable : (prefixWord ++ tailWord_1555889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555889).length < 2 ^ (prefixWord ++ tailWord_1555889).sum := by decide
  have hdescent : baseEnd_1555889 < baseStart_1555889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555904 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 4, 4]
def baseStart_1555904 : Nat := 118140960795 + 1555904 * 2 ^ 59
def prefixEnd_1555904 : Nat := 4983230072969 + 3 ^ 40 * 1555904 * 2
def baseEnd_1555904 : Nat := 532617736168790501429689

theorem tailTrace_1555904 : CollatzResearch.WordTrace tailWord_1555904 prefixEnd_1555904 532617736168790501429689 := by
  unfold tailWord_1555904
  simp only [CollatzResearch.WordTrace]
  refine ⟨28374240477616505046341383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37832320636822006728455177 28374240477616505046341383)
  ·
    refine ⟨42561360716424757569512075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28374240477616505046341383 42561360716424757569512075)
    ·
      refine ⟨63842041074637136354268113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42561360716424757569512075 63842041074637136354268113)
      ·
        refine ⟨47881530805977852265701085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63842041074637136354268113 47881530805977852265701085)
        ·
          refine ⟨17955574052241694599637907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47881530805977852265701085 17955574052241694599637907)
          ·
            refine ⟨26933361078362541899456861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17955574052241694599637907 26933361078362541899456861)
            ·
              refine ⟨10100010404385953212296323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26933361078362541899456861 10100010404385953212296323)
              ·
                refine ⟨15150015606578929818444485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10100010404385953212296323 15150015606578929818444485)
                ·
                  refine ⟨2840627926233549340958341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15150015606578929818444485 2840627926233549340958341)
                  ·
                    refine ⟨532617736168790501429689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2840627926233549340958341 532617736168790501429689)
                    ·
                      rfl

theorem cell22_1555904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 4, 4].length) (baseStart_1555904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555904 prefixEnd_1555904 := by exact prefixLift 1555904
  have htrace : WordTrace (prefixWord ++ tailWord_1555904) baseStart_1555904 baseEnd_1555904 := by
    simpa [prefixWord, tailWord_1555904, baseEnd_1555904] using wordTrace_append hprefix tailTrace_1555904
  have hstable : (prefixWord ++ tailWord_1555904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555904).length < 2 ^ (prefixWord ++ tailWord_1555904).sum := by decide
  have hdescent : baseEnd_1555904 < baseStart_1555904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555908 : List Nat := [2, 3, 3, 2, 1, 3, 1, 1, 6]
def baseStart_1555908 : Nat := 118140960795 + 1555908 * 2 ^ 59
def prefixEnd_1555908 : Nat := 4983230072969 + 3 ^ 40 * 1555908 * 2
def baseEnd_1555908 : Nat := 177539701816845274776559

theorem tailTrace_1555908 : CollatzResearch.WordTrace tailWord_1555908 prefixEnd_1555908 177539701816845274776559 := by
  unfold tailWord_1555908
  simp only [CollatzResearch.WordTrace]
  refine ⟨28374313423609259387914189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37832417898145679183885585 28374313423609259387914189)
  ·
    refine ⟨10640367533853472270467821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28374313423609259387914189 10640367533853472270467821)
    ·
      refine ⟨3990137825195052101425433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10640367533853472270467821 3990137825195052101425433)
      ·
        refine ⟨2992603368896289076069075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3990137825195052101425433 2992603368896289076069075)
        ·
          refine ⟨4488905053344433614103613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2992603368896289076069075 4488905053344433614103613)
          ·
            refine ⟨1683339395004162605288855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4488905053344433614103613 1683339395004162605288855)
            ·
              refine ⟨2525009092506243907933283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1683339395004162605288855 2525009092506243907933283)
              ·
                refine ⟨3787513638759365861899925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2525009092506243907933283 3787513638759365861899925)
                ·
                  refine ⟨177539701816845274776559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3787513638759365861899925 177539701816845274776559)
                  ·
                    rfl

theorem cell22_1555908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_1555908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555908 prefixEnd_1555908 := by exact prefixLift 1555908
  have htrace : WordTrace (prefixWord ++ tailWord_1555908) baseStart_1555908 baseEnd_1555908 := by
    simpa [prefixWord, tailWord_1555908, baseEnd_1555908] using wordTrace_append hprefix tailTrace_1555908
  have hstable : (prefixWord ++ tailWord_1555908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555908).length < 2 ^ (prefixWord ++ tailWord_1555908).sum := by decide
  have hdescent : baseEnd_1555908 < baseStart_1555908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555964 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 7]
def baseStart_1555964 : Nat := 118140960795 + 1555964 * 2 ^ 59
def prefixEnd_1555964 : Nat := 4983230072969 + 3 ^ 40 * 1555964 * 2
def baseEnd_1555964 : Nat := 177546091798323448309835

theorem tailTrace_1555964 : CollatzResearch.WordTrace tailWord_1555964 prefixEnd_1555964 177546091798323448309835 := by
  unfold tailWord_1555964
  simp only [CollatzResearch.WordTrace]
  refine ⟨28375334667507820169933473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37833779556677093559911297 28375334667507820169933473)
  ·
    refine ⟨21281501000630865127450105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28375334667507820169933473 21281501000630865127450105)
    ·
      refine ⟨15961125750473148845587579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21281501000630865127450105 15961125750473148845587579)
      ·
        refine ⟨23941688625709723268381369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15961125750473148845587579 23941688625709723268381369)
        ·
          refine ⟨17956266469282292451286027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23941688625709723268381369 17956266469282292451286027)
          ·
            refine ⟨26934399703923438676929041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17956266469282292451286027 26934399703923438676929041)
            ·
              refine ⟨20200799777942579007696781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26934399703923438676929041 20200799777942579007696781)
              ·
                refine ⟨7575299916728467127886293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20200799777942579007696781 7575299916728467127886293)
                ·
                  refine ⟨177546091798323448309835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7575299916728467127886293 177546091798323448309835)
                  ·
                    rfl

theorem cell22_1555964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_1555964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1555964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1555964 prefixEnd_1555964 := by exact prefixLift 1555964
  have htrace : WordTrace (prefixWord ++ tailWord_1555964) baseStart_1555964 baseEnd_1555964 := by
    simpa [prefixWord, tailWord_1555964, baseEnd_1555964] using wordTrace_append hprefix tailTrace_1555964
  have hstable : (prefixWord ++ tailWord_1555964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555964).length < 2 ^ (prefixWord ++ tailWord_1555964).sum := by decide
  have hdescent : baseEnd_1555964 < baseStart_1555964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556026 : List Nat := [3, 1, 1, 1, 3, 2, 4, 1, 6]
def baseStart_1556026 : Nat := 118140960795 + 1556026 * 2 ^ 59
def prefixEnd_1556026 : Nat := 4983230072969 + 3 ^ 40 * 1556026 * 2
def baseEnd_1556026 : Nat := 177553166420674283293105

theorem tailTrace_1556026 : CollatzResearch.WordTrace tailWord_1556026 prefixEnd_1556026 177553166420674283293105 := by
  unfold tailWord_1556026
  simp only [CollatzResearch.WordTrace]
  refine ⟨14188232665197756232155983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37835287107194016619082621 14188232665197756232155983)
  ·
    refine ⟨21282348997796634348233975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14188232665197756232155983 21282348997796634348233975)
    ·
      refine ⟨31923523496694951522350963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21282348997796634348233975 31923523496694951522350963)
      ·
        refine ⟨47885285245042427283526445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31923523496694951522350963 47885285245042427283526445)
        ·
          refine ⟨17956981966890910231322417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47885285245042427283526445 17956981966890910231322417)
          ·
            refine ⟨13467736475168182673491813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17956981966890910231322417 13467736475168182673491813)
            ·
              refine ⟨2525200589094034251279715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13467736475168182673491813 2525200589094034251279715)
              ·
                refine ⟨3787800883641051376919573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2525200589094034251279715 3787800883641051376919573)
                ·
                  refine ⟨177553166420674283293105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3787800883641051376919573 177553166420674283293105)
                  ·
                    rfl

theorem cell22_1556026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_1556026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556026 prefixEnd_1556026 := by exact prefixLift 1556026
  have htrace : WordTrace (prefixWord ++ tailWord_1556026) baseStart_1556026 baseEnd_1556026 := by
    simpa [prefixWord, tailWord_1556026, baseEnd_1556026] using wordTrace_append hprefix tailTrace_1556026
  have hstable : (prefixWord ++ tailWord_1556026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556026).length < 2 ^ (prefixWord ++ tailWord_1556026).sum := by decide
  have hdescent : baseEnd_1556026 < baseStart_1556026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556056 : List Nat := [2, 1, 2, 2, 1, 2, 1, 5, 2, 4]
def baseStart_1556056 : Nat := 118140960795 + 1556056 * 2 ^ 59
def prefixEnd_1556056 : Nat := 4983230072969 + 3 ^ 40 * 1556056 * 2
def baseEnd_1556056 : Nat := 532669768875112771629223

theorem tailTrace_1556056 : CollatzResearch.WordTrace tailWord_1556056 prefixEnd_1556056 532669768875112771629223 := by
  unfold tailWord_1556056
  simp only [CollatzResearch.WordTrace]
  refine ⟨28377012425341170026108011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37836016567121560034810681 28377012425341170026108011)
  ·
    refine ⟨42565518638011755039162017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28377012425341170026108011 42565518638011755039162017)
    ·
      refine ⟨31924138978508816279371513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42565518638011755039162017 31924138978508816279371513)
      ·
        refine ⟨23943104233881612209528635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31924138978508816279371513 23943104233881612209528635)
        ·
          refine ⟨35914656350822418314292953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23943104233881612209528635 35914656350822418314292953)
          ·
            refine ⟨26935992263116813735719715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35914656350822418314292953 26935992263116813735719715)
            ·
              refine ⟨40403988394675220603579573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26935992263116813735719715 40403988394675220603579573)
              ·
                refine ⟨3787873912000801931585585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40403988394675220603579573 3787873912000801931585585)
                ·
                  refine ⟨2840905434000601448689189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3787873912000801931585585 2840905434000601448689189)
                  ·
                    refine ⟨532669768875112771629223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2840905434000601448689189 532669768875112771629223)
                    ·
                      rfl

theorem cell22_1556056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_1556056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556056 prefixEnd_1556056 := by exact prefixLift 1556056
  have htrace : WordTrace (prefixWord ++ tailWord_1556056) baseStart_1556056 baseEnd_1556056 := by
    simpa [prefixWord, tailWord_1556056, baseEnd_1556056] using wordTrace_append hprefix tailTrace_1556056
  have hstable : (prefixWord ++ tailWord_1556056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556056).length < 2 ^ (prefixWord ++ tailWord_1556056).sum := by decide
  have hdescent : baseEnd_1556056 < baseStart_1556056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556060 : List Nat := [2, 2, 4, 1, 2, 1, 3, 3, 4]
def baseStart_1556060 : Nat := 118140960795 + 1556060 * 2 ^ 59
def prefixEnd_1556060 : Nat := 4983230072969 + 3 ^ 40 * 1556060 * 2
def baseEnd_1556060 : Nat := 177557046052286031509737

theorem tailTrace_1556060 : CollatzResearch.WordTrace tailWord_1556060 prefixEnd_1556060 177557046052286031509737 := by
  unfold tailWord_1556060
  simp only [CollatzResearch.WordTrace]
  refine ⟨28377085371333924367680817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37836113828445232490241089 28377085371333924367680817)
  ·
    refine ⟨21282814028500443275760613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28377085371333924367680817 21282814028500443275760613)
    ·
      refine ⟨3990527630343833114205115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21282814028500443275760613 3990527630343833114205115)
      ·
        refine ⟨5985791445515749671307673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3990527630343833114205115 5985791445515749671307673)
        ·
          refine ⟨4489343584136812253480755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5985791445515749671307673 4489343584136812253480755)
          ·
            refine ⟨6734015376205218380221133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4489343584136812253480755 6734015376205218380221133)
            ·
              refine ⟨2525255766076956892582925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6734015376205218380221133 2525255766076956892582925)
              ·
                refine ⟨946970912278858834718597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2525255766076956892582925 946970912278858834718597)
                ·
                  refine ⟨177557046052286031509737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 946970912278858834718597 177557046052286031509737)
                  ·
                    rfl

theorem cell22_1556060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 4].length) (baseStart_1556060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556060 prefixEnd_1556060 := by exact prefixLift 1556060
  have htrace : WordTrace (prefixWord ++ tailWord_1556060) baseStart_1556060 baseEnd_1556060 := by
    simpa [prefixWord, tailWord_1556060, baseEnd_1556060] using wordTrace_append hprefix tailTrace_1556060
  have hstable : (prefixWord ++ tailWord_1556060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556060).length < 2 ^ (prefixWord ++ tailWord_1556060).sum := by decide
  have hdescent : baseEnd_1556060 < baseStart_1556060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556077 : List Nat := [1, 5, 1, 1, 4, 1, 3, 2, 4]
def baseStart_1556077 : Nat := 118140960795 + 1556077 * 2 ^ 59
def prefixEnd_1556077 : Nat := 4983230072969 + 3 ^ 40 * 1556077 * 2
def baseEnd_1556077 : Nat := 177558985868091905618053

theorem tailTrace_1556077 : CollatzResearch.WordTrace tailWord_1556077 prefixEnd_1556077 177558985868091905618053 := by
  unfold tailWord_1556077
  simp only [CollatzResearch.WordTrace]
  refine ⟨56754790783606260638730485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37836527189070840425820323 56754790783606260638730485)
  ·
    refine ⟨5320761635963086934880983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56754790783606260638730485 5320761635963086934880983)
    ·
      refine ⟨7981142453944630402321475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5320761635963086934880983 7981142453944630402321475)
      ·
        refine ⟨11971713680916945603482213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7981142453944630402321475 11971713680916945603482213)
        ·
          refine ⟨2244696315171927300652915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11971713680916945603482213 2244696315171927300652915)
          ·
            refine ⟨3367044472757890950979373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244696315171927300652915 3367044472757890950979373)
            ·
              refine ⟨1262641677284209106617265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3367044472757890950979373 1262641677284209106617265)
              ·
                refine ⟨946981257963156829962949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1262641677284209106617265 946981257963156829962949)
                ·
                  refine ⟨177558985868091905618053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 946981257963156829962949 177558985868091905618053)
                  ·
                    rfl

theorem cell22_1556077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_1556077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556077 prefixEnd_1556077 := by exact prefixLift 1556077
  have htrace : WordTrace (prefixWord ++ tailWord_1556077) baseStart_1556077 baseEnd_1556077 := by
    simpa [prefixWord, tailWord_1556077, baseEnd_1556077] using wordTrace_append hprefix tailTrace_1556077
  have hstable : (prefixWord ++ tailWord_1556077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556077).length < 2 ^ (prefixWord ++ tailWord_1556077).sum := by decide
  have hdescent : baseEnd_1556077 < baseStart_1556077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556131 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 2, 5]
def baseStart_1556131 : Nat := 118140960795 + 1556131 * 2 ^ 59
def prefixEnd_1556131 : Nat := 4983230072969 + 3 ^ 40 * 1556131 * 2
def baseEnd_1556131 : Nat := 532695442907837576003993

theorem tailTrace_1556131 : CollatzResearch.WordTrace tailWord_1556131 prefixEnd_1556131 532695442907837576003993 := by
  unfold tailWord_1556131
  simp only [CollatzResearch.WordTrace]
  refine ⟨56756760325410627861196247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37837840216940418574130831 56756760325410627861196247)
  ·
    refine ⟨85135140488115941791794371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56756760325410627861196247 85135140488115941791794371)
    ·
      refine ⟨127702710732173912687691557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85135140488115941791794371 127702710732173912687691557)
      ·
        refine ⟨23944258262282608628942167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127702710732173912687691557 23944258262282608628942167)
        ·
          refine ⟨35916387393423912943413251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23944258262282608628942167 35916387393423912943413251)
          ·
            refine ⟨53874581090135869415119877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35916387393423912943413251 53874581090135869415119877)
            ·
              refine ⟨10101483954400475515334977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53874581090135869415119877 10101483954400475515334977)
              ·
                refine ⟨7576112965800356636501233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10101483954400475515334977 7576112965800356636501233)
                ·
                  refine ⟨5682084724350267477375925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7576112965800356636501233 5682084724350267477375925)
                  ·
                    refine ⟨532695442907837576003993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5682084724350267477375925 532695442907837576003993)
                    ·
                      rfl

theorem cell22_1556131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 5].length) (baseStart_1556131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556131 prefixEnd_1556131 := by exact prefixLift 1556131
  have htrace : WordTrace (prefixWord ++ tailWord_1556131) baseStart_1556131 baseEnd_1556131 := by
    simpa [prefixWord, tailWord_1556131, baseEnd_1556131] using wordTrace_append hprefix tailTrace_1556131
  have hstable : (prefixWord ++ tailWord_1556131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556131).length < 2 ^ (prefixWord ++ tailWord_1556131).sum := by decide
  have hdescent : baseEnd_1556131 < baseStart_1556131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556176 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 3, 5]
def baseStart_1556176 : Nat := 118140960795 + 1556176 * 2 ^ 59
def prefixEnd_1556176 : Nat := 4983230072969 + 3 ^ 40 * 1556176 * 2
def baseEnd_1556176 : Nat := 532710847327472458628855

theorem tailTrace_1556176 : CollatzResearch.WordTrace tailWord_1556176 prefixEnd_1556176 532710847327472458628855 := by
  unfold tailWord_1556176
  simp only [CollatzResearch.WordTrace]
  refine ⟨28379200805123800273292191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37838934406831733697722921 28379200805123800273292191)
  ·
    refine ⟨42568801207685700409938287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28379200805123800273292191 42568801207685700409938287)
    ·
      refine ⟨63853201811528550614907431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42568801207685700409938287 63853201811528550614907431)
      ·
        refine ⟨95779802717292825922361147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63853201811528550614907431 95779802717292825922361147)
        ·
          refine ⟨143669704075939238883541721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95779802717292825922361147 143669704075939238883541721)
          ·
            refine ⟨107752278056954429162656291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143669704075939238883541721 107752278056954429162656291)
            ·
              refine ⟨161628417085431643743984437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107752278056954429162656291 161628417085431643743984437)
              ·
                refine ⟨15152664101759216600998541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161628417085431643743984437 15152664101759216600998541)
                ·
                  refine ⟨5682249038159706225374453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15152664101759216600998541 5682249038159706225374453)
                  ·
                    refine ⟨532710847327472458628855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5682249038159706225374453 532710847327472458628855)
                    ·
                      rfl

theorem cell22_1556176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_1556176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556176 prefixEnd_1556176 := by exact prefixLift 1556176
  have htrace : WordTrace (prefixWord ++ tailWord_1556176) baseStart_1556176 baseEnd_1556176 := by
    simpa [prefixWord, tailWord_1556176, baseEnd_1556176] using wordTrace_append hprefix tailTrace_1556176
  have hstable : (prefixWord ++ tailWord_1556176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556176).length < 2 ^ (prefixWord ++ tailWord_1556176).sum := by decide
  have hdescent : baseEnd_1556176 < baseStart_1556176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556195 : List Nat := [1, 1, 1, 7, 2, 1, 2, 1, 6]
def baseStart_1556195 : Nat := 118140960795 + 1556195 * 2 ^ 59
def prefixEnd_1556195 : Nat := 4983230072969 + 3 ^ 40 * 1556195 * 2
def baseEnd_1556195 : Nat := 177572450471920914134599

theorem tailTrace_1556195 : CollatzResearch.WordTrace tailWord_1556195 prefixEnd_1556195 177572450471920914134599 := by
  unfold tailWord_1556195
  simp only [CollatzResearch.WordTrace]
  refine ⟨56759094597178766791526039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37839396398119177861017359 56759094597178766791526039)
  ·
    refine ⟨85138641895768150187289059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56759094597178766791526039 85138641895768150187289059)
    ·
      refine ⟨127707962843652225280933589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85138641895768150187289059 127707962843652225280933589)
      ·
        refine ⟨2993155379148099030021881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 127707962843652225280933589 2993155379148099030021881)
        ·
          refine ⟨2244866534361074272516411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2993155379148099030021881 2244866534361074272516411)
          ·
            refine ⟨3367299801541611408774617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244866534361074272516411 3367299801541611408774617)
            ·
              refine ⟨2525474851156208556580963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3367299801541611408774617 2525474851156208556580963)
              ·
                refine ⟨3788212276734312834871445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2525474851156208556580963 3788212276734312834871445)
                ·
                  refine ⟨177572450471920914134599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3788212276734312834871445 177572450471920914134599)
                  ·
                    rfl

theorem cell22_1556195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 6].length) (baseStart_1556195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556195 prefixEnd_1556195 := by exact prefixLift 1556195
  have htrace : WordTrace (prefixWord ++ tailWord_1556195) baseStart_1556195 baseEnd_1556195 := by
    simpa [prefixWord, tailWord_1556195, baseEnd_1556195] using wordTrace_append hprefix tailTrace_1556195
  have hstable : (prefixWord ++ tailWord_1556195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556195).length < 2 ^ (prefixWord ++ tailWord_1556195).sum := by decide
  have hdescent : baseEnd_1556195 < baseStart_1556195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556212 : List Nat := [2, 6, 1, 1, 1, 1, 2, 2, 6]
def baseStart_1556212 : Nat := 118140960795 + 1556212 * 2 ^ 59
def prefixEnd_1556212 : Nat := 4983230072969 + 3 ^ 40 * 1556212 * 2
def baseEnd_1556212 : Nat := 177574390287726788242915

theorem tailTrace_1556212 : CollatzResearch.WordTrace tailWord_1556212 prefixEnd_1556212 177574390287726788242915 := by
  unfold tailWord_1556212
  simp only [CollatzResearch.WordTrace]
  refine ⟨28379857319058589347447445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37839809758744785796596593 28379857319058589347447445)
  ·
    refine ⟨1330305811830871375661599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28379857319058589347447445 1330305811830871375661599)
    ·
      refine ⟨1995458717746307063492399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1330305811830871375661599 1995458717746307063492399)
      ·
        refine ⟨2993188076619460595238599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1995458717746307063492399 2993188076619460595238599)
        ·
          refine ⟨4489782114929190892857899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2993188076619460595238599 4489782114929190892857899)
          ·
            refine ⟨6734673172393786339286849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4489782114929190892857899 6734673172393786339286849)
            ·
              refine ⟨5051004879295339754465137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6734673172393786339286849 5051004879295339754465137)
              ·
                refine ⟨3788253659471504815848853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5051004879295339754465137 3788253659471504815848853)
                ·
                  refine ⟨177574390287726788242915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3788253659471504815848853 177574390287726788242915)
                  ·
                    rfl

theorem cell22_1556212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_1556212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556212 prefixEnd_1556212 := by exact prefixLift 1556212
  have htrace : WordTrace (prefixWord ++ tailWord_1556212) baseStart_1556212 baseEnd_1556212 := by
    simpa [prefixWord, tailWord_1556212, baseEnd_1556212] using wordTrace_append hprefix tailTrace_1556212
  have hstable : (prefixWord ++ tailWord_1556212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556212).length < 2 ^ (prefixWord ++ tailWord_1556212).sum := by decide
  have hdescent : baseEnd_1556212 < baseStart_1556212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556223 : List Nat := [1, 1, 2, 2, 1, 3, 6, 6]
def baseStart_1556223 : Nat := 118140960795 + 1556223 * 2 ^ 59
def prefixEnd_1556223 : Nat := 4983230072969 + 3 ^ 40 * 1556223 * 2
def baseEnd_1556223 : Nat := 59191881820886666967079

theorem tailTrace_1556223 : CollatzResearch.WordTrace tailWord_1556223 prefixEnd_1556223 59191881820886666967079 := by
  unfold tailWord_1556223
  simp only [CollatzResearch.WordTrace]
  refine ⟨56760115841077327573545323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37840077227384885049030215 56760115841077327573545323)
  ·
    refine ⟨85140173761615991360317985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56760115841077327573545323 85140173761615991360317985)
    ·
      refine ⟨63855130321211993520238489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85140173761615991360317985 63855130321211993520238489)
      ·
        refine ⟨47891347740908995140178867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63855130321211993520238489 47891347740908995140178867)
        ·
          refine ⟨71837021611363492710268301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47891347740908995140178867 71837021611363492710268301)
          ·
            refine ⟨26938883104261309766350613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71837021611363492710268301 26938883104261309766350613)
            ·
              refine ⟨1262760145512248895297685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26938883104261309766350613 1262760145512248895297685)
              ·
                refine ⟨59191881820886666967079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1262760145512248895297685 59191881820886666967079)
                ·
                  rfl

theorem cell22_1556223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 6].length) (baseStart_1556223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556223 prefixEnd_1556223 := by exact prefixLift 1556223
  have htrace : WordTrace (prefixWord ++ tailWord_1556223) baseStart_1556223 baseEnd_1556223 := by
    simpa [prefixWord, tailWord_1556223, baseEnd_1556223] using wordTrace_append hprefix tailTrace_1556223
  have hstable : (prefixWord ++ tailWord_1556223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556223).length < 2 ^ (prefixWord ++ tailWord_1556223).sum := by decide
  have hdescent : baseEnd_1556223 < baseStart_1556223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556242 : List Nat := [3, 2, 4, 1, 1, 2, 1, 2, 2, 4]
def baseStart_1556242 : Nat := 118140960795 + 1556242 * 2 ^ 59
def prefixEnd_1556242 : Nat := 4983230072969 + 3 ^ 40 * 1556242 * 2
def baseEnd_1556242 : Nat := 532733440476270286478653

theorem tailTrace_1556242 : CollatzResearch.WordTrace tailWord_1556242 prefixEnd_1556242 532733440476270286478653 := by
  unfold tailWord_1556242
  simp only [CollatzResearch.WordTrace]
  refine ⟨14190202207002123454621745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37840539218672329212324653 14190202207002123454621745)
  ·
    refine ⟨10642651655251592590966309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14190202207002123454621745 10642651655251592590966309)
    ·
      refine ⟨1995497185359673610806183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10642651655251592590966309 1995497185359673610806183)
      ·
        refine ⟨2993245778039510416209275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1995497185359673610806183 2993245778039510416209275)
        ·
          refine ⟨4489868667059265624313913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2993245778039510416209275 4489868667059265624313913)
          ·
            refine ⟨3367401500294449218235435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4489868667059265624313913 3367401500294449218235435)
            ·
              refine ⟨5051102250441673827353153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3367401500294449218235435 5051102250441673827353153)
              ·
                refine ⟨3788326687831255370514865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5051102250441673827353153 3788326687831255370514865)
                ·
                  refine ⟨2841245015873441527886149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3788326687831255370514865 2841245015873441527886149)
                  ·
                    refine ⟨532733440476270286478653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2841245015873441527886149 532733440476270286478653)
                    ·
                      rfl

theorem cell22_1556242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_1556242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556242 prefixEnd_1556242 := by exact prefixLift 1556242
  have htrace : WordTrace (prefixWord ++ tailWord_1556242) baseStart_1556242 baseEnd_1556242 := by
    simpa [prefixWord, tailWord_1556242, baseEnd_1556242] using wordTrace_append hprefix tailTrace_1556242
  have hstable : (prefixWord ++ tailWord_1556242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556242).length < 2 ^ (prefixWord ++ tailWord_1556242).sum := by decide
  have hdescent : baseEnd_1556242 < baseStart_1556242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556306 : List Nat := [3, 2, 2, 1, 1, 5, 2, 2, 1, 3]
def baseStart_1556306 : Nat := 118140960795 + 1556306 * 2 ^ 59
def prefixEnd_1556306 : Nat := 4983230072969 + 3 ^ 40 * 1556306 * 2
def baseEnd_1556306 : Nat := 532755348984195452878457

theorem tailTrace_1556306 : CollatzResearch.WordTrace tailWord_1556306 prefixEnd_1556306 532755348984195452878457 := by
  unfold tailWord_1556306
  simp only [CollatzResearch.WordTrace]
  refine ⟨14190785774944158187204193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37842095399851088499211181 14190785774944158187204193)
  ·
    refine ⟨10643089331208118640403145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14190785774944158187204193 10643089331208118640403145)
    ·
      refine ⟨7982316998406088980302359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10643089331208118640403145 7982316998406088980302359)
      ·
        refine ⟨11973475497609133470453539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7982316998406088980302359 11973475497609133470453539)
        ·
          refine ⟨17960213246413700205680309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11973475497609133470453539 17960213246413700205680309)
          ·
            refine ⟨1683769991851284394282529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17960213246413700205680309 1683769991851284394282529)
            ·
              refine ⟨1262827493888463295711897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1683769991851284394282529 1262827493888463295711897)
              ·
                refine ⟨947120620416347471783923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1262827493888463295711897 947120620416347471783923)
                ·
                  refine ⟨1420680930624521207675885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947120620416347471783923 1420680930624521207675885)
                  ·
                    refine ⟨532755348984195452878457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1420680930624521207675885 532755348984195452878457)
                    ·
                      rfl

theorem cell22_1556306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_1556306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556306 prefixEnd_1556306 := by exact prefixLift 1556306
  have htrace : WordTrace (prefixWord ++ tailWord_1556306) baseStart_1556306 baseEnd_1556306 := by
    simpa [prefixWord, tailWord_1556306, baseEnd_1556306] using wordTrace_append hprefix tailTrace_1556306
  have hstable : (prefixWord ++ tailWord_1556306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556306).length < 2 ^ (prefixWord ++ tailWord_1556306).sum := by decide
  have hdescent : baseEnd_1556306 < baseStart_1556306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556313 : List Nat := [1, 2, 1, 2, 2, 3, 2, 3, 6]
def baseStart_1556313 : Nat := 118140960795 + 1556313 * 2 ^ 59
def prefixEnd_1556313 : Nat := 4983230072969 + 3 ^ 40 * 1556313 * 2
def baseEnd_1556313 : Nat := 177585915075749922651145

theorem tailTrace_1556313 : CollatzResearch.WordTrace tailWord_1556313 prefixEnd_1556313 177585915075749922651145 := by
  unfold tailWord_1556313
  simp only [CollatzResearch.WordTrace]
  refine ⟨56763398410751272944321593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37842265607167515296214395 56763398410751272944321593)
  ·
    refine ⟨42572548808063454708241195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56763398410751272944321593 42572548808063454708241195)
    ·
      refine ⟨63858823212095182062361793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42572548808063454708241195 63858823212095182062361793)
      ·
        refine ⟨47894117409071386546771345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63858823212095182062361793 47894117409071386546771345)
        ·
          refine ⟨35920588056803539910078509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47894117409071386546771345 35920588056803539910078509)
          ·
            refine ⟨13470220521301327466279441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35920588056803539910078509 13470220521301327466279441)
            ·
              refine ⟨10102665390975995599709581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13470220521301327466279441 10102665390975995599709581)
              ·
                refine ⟨3788499521615998349891093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10102665390975995599709581 3788499521615998349891093)
                ·
                  refine ⟨177585915075749922651145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3788499521615998349891093 177585915075749922651145)
                  ·
                    rfl

theorem cell22_1556313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 6].length) (baseStart_1556313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556313 prefixEnd_1556313 := by exact prefixLift 1556313
  have htrace : WordTrace (prefixWord ++ tailWord_1556313) baseStart_1556313 baseEnd_1556313 := by
    simpa [prefixWord, tailWord_1556313, baseEnd_1556313] using wordTrace_append hprefix tailTrace_1556313
  have hstable : (prefixWord ++ tailWord_1556313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556313).length < 2 ^ (prefixWord ++ tailWord_1556313).sum := by decide
  have hdescent : baseEnd_1556313 < baseStart_1556313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556345 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 4, 3]
def baseStart_1556345 : Nat := 118140960795 + 1556345 * 2 ^ 59
def prefixEnd_1556345 : Nat := 4983230072969 + 3 ^ 40 * 1556345 * 2
def baseEnd_1556345 : Nat := 532768699481212351153337

theorem tailTrace_1556345 : CollatzResearch.WordTrace tailWord_1556345 prefixEnd_1556345 532768699481212351153337 := by
  unfold tailWord_1556345
  simp only [CollatzResearch.WordTrace]
  refine ⟨56764565546635342409486489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37843043697756894939657659 56764565546635342409486489)
  ·
    refine ⟨42573424159976506807114867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56764565546635342409486489 42573424159976506807114867)
    ·
      refine ⟨63860136239964760210672301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42573424159976506807114867 63860136239964760210672301)
      ·
        refine ⟨23947551089986785079002113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63860136239964760210672301 23947551089986785079002113)
        ·
          refine ⟨17960663317490088809251585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23947551089986785079002113 17960663317490088809251585)
          ·
            refine ⟨13470497488117566606938689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17960663317490088809251585 13470497488117566606938689)
            ·
              refine ⟨10102873116088174955204017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13470497488117566606938689 10102873116088174955204017)
              ·
                refine ⟨7577154837066131216403013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10102873116088174955204017 7577154837066131216403013)
                ·
                  refine ⟨1420716531949899603075565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7577154837066131216403013 1420716531949899603075565)
                  ·
                    refine ⟨532768699481212351153337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1420716531949899603075565 532768699481212351153337)
                    ·
                      rfl

theorem cell22_1556345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 3].length) (baseStart_1556345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556345 prefixEnd_1556345 := by exact prefixLift 1556345
  have htrace : WordTrace (prefixWord ++ tailWord_1556345) baseStart_1556345 baseEnd_1556345 := by
    simpa [prefixWord, tailWord_1556345, baseEnd_1556345] using wordTrace_append hprefix tailTrace_1556345
  have hstable : (prefixWord ++ tailWord_1556345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556345).length < 2 ^ (prefixWord ++ tailWord_1556345).sum := by decide
  have hdescent : baseEnd_1556345 < baseStart_1556345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556403 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 9]
def baseStart_1556403 : Nat := 118140960795 + 1556403 * 2 ^ 59
def prefixEnd_1556403 : Nat := 4983230072969 + 3 ^ 40 * 1556403 * 2
def baseEnd_1556403 : Nat := 177596184688839844401053

theorem tailTrace_1556403 : CollatzResearch.WordTrace tailWord_1556403 prefixEnd_1556403 177596184688839844401053 := by
  unfold tailWord_1556403
  simp only [CollatzResearch.WordTrace]
  refine ⟨56766680980425218315097863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37844453986950145543398575 56766680980425218315097863)
  ·
    refine ⟨85150021470637827472646795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56766680980425218315097863 85150021470637827472646795)
    ·
      refine ⟨127725032205956741208970193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85150021470637827472646795 127725032205956741208970193)
      ·
        refine ⟨95793774154467555906727645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127725032205956741208970193 95793774154467555906727645)
        ·
          refine ⟨35922665307925333465022867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95793774154467555906727645 35922665307925333465022867)
          ·
            refine ⟨53883997961888000197534301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35922665307925333465022867 53883997961888000197534301)
            ·
              refine ⟨20206499235708000074075363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53883997961888000197534301 20206499235708000074075363)
              ·
                refine ⟨30309748853562000111113045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20206499235708000074075363 30309748853562000111113045)
                ·
                  refine ⟨177596184688839844401053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30309748853562000111113045 177596184688839844401053)
                  ·
                    rfl

theorem cell22_1556403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 9].length) (baseStart_1556403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556403 prefixEnd_1556403 := by exact prefixLift 1556403
  have htrace : WordTrace (prefixWord ++ tailWord_1556403) baseStart_1556403 baseEnd_1556403 := by
    simpa [prefixWord, tailWord_1556403, baseEnd_1556403] using wordTrace_append hprefix tailTrace_1556403
  have hstable : (prefixWord ++ tailWord_1556403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556403).length < 2 ^ (prefixWord ++ tailWord_1556403).sum := by decide
  have hdescent : baseEnd_1556403 < baseStart_1556403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556424 : List Nat := [2, 1, 3, 1, 4, 3, 1, 1, 3, 3]
def baseStart_1556424 : Nat := 118140960795 + 1556424 * 2 ^ 59
def prefixEnd_1556424 : Nat := 4983230072969 + 3 ^ 40 * 1556424 * 2
def baseEnd_1556424 : Nat := 532795742795682478428095

theorem tailTrace_1556424 : CollatzResearch.WordTrace tailWord_1556424 prefixEnd_1556424 532795742795682478428095 := by
  unfold tailWord_1556424
  simp only [CollatzResearch.WordTrace]
  refine ⟨28383723456674569450806163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37844964608899425934408217 28383723456674569450806163)
  ·
    refine ⟨42575585185011854176209245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28383723456674569450806163 42575585185011854176209245)
    ·
      refine ⟨15965844444379445316078467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42575585185011854176209245 15965844444379445316078467)
      ·
        refine ⟨23948766666569167974117701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15965844444379445316078467 23948766666569167974117701)
        ·
          refine ⟨4490393749981718995147069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23948766666569167974117701 4490393749981718995147069)
          ·
            refine ⟨1683897656243144623180151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4490393749981718995147069 1683897656243144623180151)
            ·
              refine ⟨2525846484364716934770227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1683897656243144623180151 2525846484364716934770227)
              ·
                refine ⟨3788769726547075402155341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2525846484364716934770227 3788769726547075402155341)
                ·
                  refine ⟨1420788647455153275808253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3788769726547075402155341 1420788647455153275808253)
                  ·
                    refine ⟨532795742795682478428095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1420788647455153275808253 532795742795682478428095)
                    ·
                      rfl

theorem cell22_1556424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_1556424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556424 prefixEnd_1556424 := by exact prefixLift 1556424
  have htrace : WordTrace (prefixWord ++ tailWord_1556424) baseStart_1556424 baseEnd_1556424 := by
    simpa [prefixWord, tailWord_1556424, baseEnd_1556424] using wordTrace_append hprefix tailTrace_1556424
  have hstable : (prefixWord ++ tailWord_1556424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556424).length < 2 ^ (prefixWord ++ tailWord_1556424).sum := by decide
  have hdescent : baseEnd_1556424 < baseStart_1556424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556437 : List Nat := [1, 3, 2, 3, 2, 2, 1, 3, 5]
def baseStart_1556437 : Nat := 118140960795 + 1556437 * 2 ^ 59
def prefixEnd_1556437 : Nat := 4983230072969 + 3 ^ 40 * 1556437 * 2
def baseEnd_1556437 : Nat := 177600064320451592617685

theorem tailTrace_1556437 : CollatzResearch.WordTrace tailWord_1556437 prefixEnd_1556437 177600064320451592617685 := by
  unfold tailWord_1556437
  simp only [CollatzResearch.WordTrace]
  refine ⟨56767921062302042121835565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37845280708201361414557043 56767921062302042121835565)
  ·
    refine ⟨21287970398363265795688337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56767921062302042121835565 21287970398363265795688337)
    ·
      refine ⟨15965977798772449346766253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21287970398363265795688337 15965977798772449346766253)
      ·
        refine ⟨5987241674539668505037345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15965977798772449346766253 5987241674539668505037345)
        ·
          refine ⟨4490431255904751378778009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5987241674539668505037345 4490431255904751378778009)
          ·
            refine ⟨3367823441928563534083507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4490431255904751378778009 3367823441928563534083507)
            ·
              refine ⟨5051735162892845301125261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3367823441928563534083507 5051735162892845301125261)
              ·
                refine ⟨1894400686084816987921973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5051735162892845301125261 1894400686084816987921973)
                ·
                  refine ⟨177600064320451592617685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1894400686084816987921973 177600064320451592617685)
                  ·
                    rfl

theorem cell22_1556437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_1556437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556437 prefixEnd_1556437 := by exact prefixLift 1556437
  have htrace : WordTrace (prefixWord ++ tailWord_1556437) baseStart_1556437 baseEnd_1556437 := by
    simpa [prefixWord, tailWord_1556437, baseEnd_1556437] using wordTrace_append hprefix tailTrace_1556437
  have hstable : (prefixWord ++ tailWord_1556437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556437).length < 2 ^ (prefixWord ++ tailWord_1556437).sum := by decide
  have hdescent : baseEnd_1556437 < baseStart_1556437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556516 : List Nat := [2, 3, 1, 4, 2, 1, 2, 3, 4]
def baseStart_1556516 : Nat := 118140960795 + 1556516 * 2 ^ 59
def prefixEnd_1556516 : Nat := 4983230072969 + 3 ^ 40 * 1556516 * 2
def baseEnd_1556516 : Nat := 177609078758608301709271

theorem tailTrace_1556516 : CollatzResearch.WordTrace tailWord_1556516 prefixEnd_1556516 177609078758608301709271 := by
  unfold tailWord_1556516
  simp only [CollatzResearch.WordTrace]
  refine ⟨28385401214507919306980701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37847201619343892409307601 28385401214507919306980701)
  ·
    refine ⟨10644525455440469740117763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28385401214507919306980701 10644525455440469740117763)
    ·
      refine ⟨15966788183160704610176645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10644525455440469740117763 15966788183160704610176645)
      ·
        refine ⟨2993772784342632114408121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15966788183160704610176645 2993772784342632114408121)
        ·
          refine ⟨2245329588256974085806091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2993772784342632114408121 2245329588256974085806091)
          ·
            refine ⟨3367994382385461128709137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2245329588256974085806091 3367994382385461128709137)
            ·
              refine ⟨2525995786789095846531853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3367994382385461128709137 2525995786789095846531853)
              ·
                refine ⟨947248420045910942449445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2525995786789095846531853 947248420045910942449445)
                ·
                  refine ⟨177609078758608301709271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 947248420045910942449445 177609078758608301709271)
                  ·
                    rfl

theorem cell22_1556516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_1556516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556516 prefixEnd_1556516 := by exact prefixLift 1556516
  have htrace : WordTrace (prefixWord ++ tailWord_1556516) baseStart_1556516 baseEnd_1556516 := by
    simpa [prefixWord, tailWord_1556516, baseEnd_1556516] using wordTrace_append hprefix tailTrace_1556516
  have hstable : (prefixWord ++ tailWord_1556516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556516).length < 2 ^ (prefixWord ++ tailWord_1556516).sum := by decide
  have hdescent : baseEnd_1556516 < baseStart_1556516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556572 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 7]
def baseStart_1556572 : Nat := 118140960795 + 1556572 * 2 ^ 59
def prefixEnd_1556572 : Nat := 4983230072969 + 3 ^ 40 * 1556572 * 2
def baseEnd_1556572 : Nat := 177615468740086475242547

theorem tailTrace_1556572 : CollatzResearch.WordTrace tailWord_1556572 prefixEnd_1556572 177615468740086475242547 := by
  unfold tailWord_1556572
  simp only [CollatzResearch.WordTrace]
  refine ⟨28386422458406480088999985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37848563277875306785333313 28386422458406480088999985)
  ·
    refine ⟨21289816843804860066749989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28386422458406480088999985 21289816843804860066749989)
    ·
      refine ⟨3991840658213411262515623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21289816843804860066749989 3991840658213411262515623)
      ·
        refine ⟨5987760987320116893773435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3991840658213411262515623 5987760987320116893773435)
        ·
          refine ⟨8981641480980175340660153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5987760987320116893773435 8981641480980175340660153)
          ·
            refine ⟨6736231110735131505495115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8981641480980175340660153 6736231110735131505495115)
            ·
              refine ⟨10104346666102697258242673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6736231110735131505495115 10104346666102697258242673)
              ·
                refine ⟨7578259999577022943682005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10104346666102697258242673 7578259999577022943682005)
                ·
                  refine ⟨177615468740086475242547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7578259999577022943682005 177615468740086475242547)
                  ·
                    rfl

theorem cell22_1556572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_1556572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556572 prefixEnd_1556572 := by exact prefixLift 1556572
  have htrace : WordTrace (prefixWord ++ tailWord_1556572) baseStart_1556572 baseEnd_1556572 := by
    simpa [prefixWord, tailWord_1556572, baseEnd_1556572] using wordTrace_append hprefix tailTrace_1556572
  have hstable : (prefixWord ++ tailWord_1556572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556572).length < 2 ^ (prefixWord ++ tailWord_1556572).sum := by decide
  have hdescent : baseEnd_1556572 < baseStart_1556572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556576 : List Nat := [2, 1, 1, 3, 2, 3, 3, 3, 1, 3]
def baseStart_1556576 : Nat := 118140960795 + 1556576 * 2 ^ 59
def prefixEnd_1556576 : Nat := 4983230072969 + 3 ^ 40 * 1556576 * 2
def baseEnd_1556576 : Nat := 532847775502004748627629

theorem tailTrace_1556576 : CollatzResearch.WordTrace tailWord_1556576 prefixEnd_1556576 532847775502004748627629 := by
  unfold tailWord_1556576
  simp only [CollatzResearch.WordTrace]
  refine ⟨28386495404399234430572791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37848660539198979240763721 28386495404399234430572791)
  ·
    refine ⟨42579743106598851645859187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28386495404399234430572791 42579743106598851645859187)
    ·
      refine ⟨63869614659898277468788781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42579743106598851645859187 63869614659898277468788781)
      ·
        refine ⟨23951105497461854050795793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63869614659898277468788781 23951105497461854050795793)
        ·
          refine ⟨17963329123096390538096845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23951105497461854050795793 17963329123096390538096845)
          ·
            refine ⟨6736248421161146451786317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17963329123096390538096845 6736248421161146451786317)
            ·
              refine ⟨2526093157935429919419869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6736248421161146451786317 2526093157935429919419869)
              ·
                refine ⟨947284934225786219782451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2526093157935429919419869 947284934225786219782451)
                ·
                  refine ⟨1420927401338679329673677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947284934225786219782451 1420927401338679329673677)
                  ·
                    refine ⟨532847775502004748627629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1420927401338679329673677 532847775502004748627629)
                    ·
                      rfl

theorem cell22_1556576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 1, 3].length) (baseStart_1556576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556576 prefixEnd_1556576 := by exact prefixLift 1556576
  have htrace : WordTrace (prefixWord ++ tailWord_1556576) baseStart_1556576 baseEnd_1556576 := by
    simpa [prefixWord, tailWord_1556576, baseEnd_1556576] using wordTrace_append hprefix tailTrace_1556576
  have hstable : (prefixWord ++ tailWord_1556576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556576).length < 2 ^ (prefixWord ++ tailWord_1556576).sum := by decide
  have hdescent : baseEnd_1556576 < baseStart_1556576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556636 : List Nat := [2, 2, 3, 2, 1, 1, 5, 1, 1, 4]
def baseStart_1556636 : Nat := 118140960795 + 1556636 * 2 ^ 59
def prefixEnd_1556636 : Nat := 4983230072969 + 3 ^ 40 * 1556636 * 2
def baseEnd_1556636 : Nat := 532868314728184592127445

theorem tailTrace_1556636 : CollatzResearch.WordTrace tailWord_1556636 prefixEnd_1556636 532868314728184592127445 := by
  unfold tailWord_1556636
  simp only [CollatzResearch.WordTrace]
  refine ⟨28387589594290549554164881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37850119459054066072219841 28387589594290549554164881)
  ·
    refine ⟨21290692195717912165623661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28387589594290549554164881 21290692195717912165623661)
    ·
      refine ⟨7984009573394217062108873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21290692195717912165623661 7984009573394217062108873)
      ·
        refine ⟨5988007180045662796581655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7984009573394217062108873 5988007180045662796581655)
        ·
          refine ⟨8982010770068494194872483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5988007180045662796581655 8982010770068494194872483)
          ·
            refine ⟨13473016155102741292308725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8982010770068494194872483 13473016155102741292308725)
            ·
              refine ⟨1263095264540881996153943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13473016155102741292308725 1263095264540881996153943)
              ·
                refine ⟨1894642896811322994230915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1263095264540881996153943 1894642896811322994230915)
                ·
                  refine ⟨2841964345216984491346373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1894642896811322994230915 2841964345216984491346373)
                  ·
                    refine ⟨532868314728184592127445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2841964345216984491346373 532868314728184592127445)
                    ·
                      rfl

theorem cell22_1556636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_1556636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556636 prefixEnd_1556636 := by exact prefixLift 1556636
  have htrace : WordTrace (prefixWord ++ tailWord_1556636) baseStart_1556636 baseEnd_1556636 := by
    simpa [prefixWord, tailWord_1556636, baseEnd_1556636] using wordTrace_append hprefix tailTrace_1556636
  have hstable : (prefixWord ++ tailWord_1556636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556636).length < 2 ^ (prefixWord ++ tailWord_1556636).sum := by decide
  have hdescent : baseEnd_1556636 < baseStart_1556636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556711 : List Nat := [1, 1, 5, 3, 1, 1, 1, 3, 3, 3]
def baseStart_1556711 : Nat := 118140960795 + 1556711 * 2 ^ 59
def prefixEnd_1556711 : Nat := 4983230072969 + 3 ^ 40 * 1556711 * 2
def baseEnd_1556711 : Nat := 532893988760909396502215

theorem tailTrace_1556711 : CollatzResearch.WordTrace tailWord_1556711 prefixEnd_1556711 532893988760909396502215 := by
  unfold tailWord_1556711
  simp only [CollatzResearch.WordTrace]
  refine ⟨56777914663309386917309987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37851943108872924611539991 56777914663309386917309987)
  ·
    refine ⟨85166871994964080375964981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56777914663309386917309987 85166871994964080375964981)
    ·
      refine ⟨7984394249527882535246717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85166871994964080375964981 7984394249527882535246717)
      ·
        refine ⟨2994147843572955950717519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7984394249527882535246717 2994147843572955950717519)
        ·
          refine ⟨4491221765359433926076279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2994147843572955950717519 4491221765359433926076279)
          ·
            refine ⟨6736832648039150889114419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4491221765359433926076279 6736832648039150889114419)
            ·
              refine ⟨10105248972058726333671629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6736832648039150889114419 10105248972058726333671629)
              ·
                refine ⟨3789468364522022375126861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10105248972058726333671629 3789468364522022375126861)
                ·
                  refine ⟨1421050636695758390672573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3789468364522022375126861 1421050636695758390672573)
                  ·
                    refine ⟨532893988760909396502215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1421050636695758390672573 532893988760909396502215)
                    ·
                      rfl

theorem cell22_1556711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_1556711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556711 prefixEnd_1556711 := by exact prefixLift 1556711
  have htrace : WordTrace (prefixWord ++ tailWord_1556711) baseStart_1556711 baseEnd_1556711 := by
    simpa [prefixWord, tailWord_1556711, baseEnd_1556711] using wordTrace_append hprefix tailTrace_1556711
  have hstable : (prefixWord ++ tailWord_1556711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556711).length < 2 ^ (prefixWord ++ tailWord_1556711).sum := by decide
  have hdescent : baseEnd_1556711 < baseStart_1556711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556769 : List Nat := [1, 2, 3, 2, 1, 1, 5, 1, 6]
def baseStart_1556769 : Nat := 118140960795 + 1556769 * 2 ^ 59
def prefixEnd_1556769 : Nat := 4983230072969 + 3 ^ 40 * 1556769 * 2
def baseEnd_1556769 : Nat := 177637947782072192850679

theorem tailTrace_1556769 : CollatzResearch.WordTrace tailWord_1556769 prefixEnd_1556769 177637947782072192850679 := by
  unfold tailWord_1556769
  simp only [CollatzResearch.WordTrace]
  refine ⟨56780030097099262822921361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37853353398066175215280907 56780030097099262822921361)
  ·
    refine ⟨42585022572824447117191021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56780030097099262822921361 42585022572824447117191021)
    ·
      refine ⟨15969383464809167668946633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42585022572824447117191021 15969383464809167668946633)
      ·
        refine ⟨11977037598606875751709975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15969383464809167668946633 11977037598606875751709975)
        ·
          refine ⟨17965556397910313627564963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11977037598606875751709975 17965556397910313627564963)
          ·
            refine ⟨26948334596865470441347445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17965556397910313627564963 26948334596865470441347445)
            ·
              refine ⟨2526406368456137853876323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26948334596865470441347445 2526406368456137853876323)
              ·
                refine ⟨3789609552684206780814485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2526406368456137853876323 3789609552684206780814485)
                ·
                  refine ⟨177637947782072192850679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3789609552684206780814485 177637947782072192850679)
                  ·
                    rfl

theorem cell22_1556769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 6].length) (baseStart_1556769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556769 prefixEnd_1556769 := by exact prefixLift 1556769
  have htrace : WordTrace (prefixWord ++ tailWord_1556769) baseStart_1556769 baseEnd_1556769 := by
    simpa [prefixWord, tailWord_1556769, baseEnd_1556769] using wordTrace_append hprefix tailTrace_1556769
  have hstable : (prefixWord ++ tailWord_1556769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556769).length < 2 ^ (prefixWord ++ tailWord_1556769).sum := by decide
  have hdescent : baseEnd_1556769 < baseStart_1556769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556775 : List Nat := [1, 1, 8, 1, 1, 1, 1, 3, 5]
def baseStart_1556775 : Nat := 118140960795 + 1556775 * 2 ^ 59
def prefixEnd_1556775 : Nat := 4983230072969 + 3 ^ 40 * 1556775 * 2
def baseEnd_1556775 : Nat := 177638632422944854300673

theorem tailTrace_1556775 : CollatzResearch.WordTrace tailWord_1556775 prefixEnd_1556775 177638632422944854300673 := by
  unfold tailWord_1556775
  simp only [CollatzResearch.WordTrace]
  refine ⟨56780248935077525847639779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37853499290051683898426519 56780248935077525847639779)
  ·
    refine ⟨85170373402616288771459669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56780248935077525847639779 85170373402616288771459669)
    ·
      refine ⟨998090313311909634040543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 85170373402616288771459669 998090313311909634040543)
      ·
        refine ⟨1497135469967864451060815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 998090313311909634040543 1497135469967864451060815)
        ·
          refine ⟨2245703204951796676591223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1497135469967864451060815 2245703204951796676591223)
          ·
            refine ⟨3368554807427695014886835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2245703204951796676591223 3368554807427695014886835)
            ·
              refine ⟨5052832211141542522330253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3368554807427695014886835 5052832211141542522330253)
              ·
                refine ⟨1894812079178078445873845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5052832211141542522330253 1894812079178078445873845)
                ·
                  refine ⟨177638632422944854300673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1894812079178078445873845 177638632422944854300673)
                  ·
                    rfl

theorem cell22_1556775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 5].length) (baseStart_1556775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556775 prefixEnd_1556775 := by exact prefixLift 1556775
  have htrace : WordTrace (prefixWord ++ tailWord_1556775) baseStart_1556775 baseEnd_1556775 := by
    simpa [prefixWord, tailWord_1556775, baseEnd_1556775] using wordTrace_append hprefix tailTrace_1556775
  have hstable : (prefixWord ++ tailWord_1556775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556775).length < 2 ^ (prefixWord ++ tailWord_1556775).sum := by decide
  have hdescent : baseEnd_1556775 < baseStart_1556775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556784 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 6, 3]
def baseStart_1556784 : Nat := 118140960795 + 1556784 * 2 ^ 59
def prefixEnd_1556784 : Nat := 4983230072969 + 3 ^ 40 * 1556784 * 2
def baseEnd_1556784 : Nat := 532918978152761539426991

theorem tailTrace_1556784 : CollatzResearch.WordTrace tailWord_1556784 prefixEnd_1556784 532918978152761539426991 := by
  unfold tailWord_1556784
  simp only [CollatzResearch.WordTrace]
  refine ⟨28390288596022460192358703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37853718128029946923144937 28390288596022460192358703)
  ·
    refine ⟨42585432894033690288538055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28390288596022460192358703 42585432894033690288538055)
    ·
      refine ⟨63878149341050535432807083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42585432894033690288538055 63878149341050535432807083)
      ·
        refine ⟨95817224011575803149210625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63878149341050535432807083 95817224011575803149210625)
        ·
          refine ⟨71862918008681852361907969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95817224011575803149210625 71862918008681852361907969)
          ·
            refine ⟨53897188506511389271430977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71862918008681852361907969 53897188506511389271430977)
            ·
              refine ⟨40422891379883541953573233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53897188506511389271430977 40422891379883541953573233)
              ·
                refine ⟨30317168534912656465179925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40422891379883541953573233 30317168534912656465179925)
                ·
                  refine ⟨1421117275074030771805309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30317168534912656465179925 1421117275074030771805309)
                  ·
                    refine ⟨532918978152761539426991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1421117275074030771805309 532918978152761539426991)
                    ·
                      rfl

theorem cell22_1556784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 6, 3].length) (baseStart_1556784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556784 prefixEnd_1556784 := by exact prefixLift 1556784
  have htrace : WordTrace (prefixWord ++ tailWord_1556784) baseStart_1556784 baseEnd_1556784 := by
    simpa [prefixWord, tailWord_1556784, baseEnd_1556784] using wordTrace_append hprefix tailTrace_1556784
  have hstable : (prefixWord ++ tailWord_1556784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556784).length < 2 ^ (prefixWord ++ tailWord_1556784).sum := by decide
  have hdescent : baseEnd_1556784 < baseStart_1556784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556788 : List Nat := [2, 5, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_1556788 : Nat := 118140960795 + 1556788 * 2 ^ 59
def prefixEnd_1556788 : Nat := 4983230072969 + 3 ^ 40 * 1556788 * 2
def baseEnd_1556788 : Nat := 532920347434506862326979

theorem tailTrace_1556788 : CollatzResearch.WordTrace tailWord_1556788 prefixEnd_1556788 532920347434506862326979 := by
  unfold tailWord_1556788
  simp only [CollatzResearch.WordTrace]
  refine ⟨28390361542015214533931509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37853815389353619378575345 28390361542015214533931509)
  ·
    refine ⟨2661596394563926362556079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28390361542015214533931509 2661596394563926362556079)
    ·
      refine ⟨3992394591845889543834119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2661596394563926362556079 3992394591845889543834119)
      ·
        refine ⟨5988591887768834315751179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3992394591845889543834119 5988591887768834315751179)
        ·
          refine ⟨8982887831653251473626769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5988591887768834315751179 8982887831653251473626769)
          ·
            refine ⟨6737165873739938605220077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8982887831653251473626769 6737165873739938605220077)
            ·
              refine ⟨2526437202652476976957529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6737165873739938605220077 2526437202652476976957529)
              ·
                refine ⟨1894827901989357732718147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2526437202652476976957529 1894827901989357732718147)
                ·
                  refine ⟨2842241852984036599077221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1894827901989357732718147 2842241852984036599077221)
                  ·
                    refine ⟨532920347434506862326979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2842241852984036599077221 532920347434506862326979)
                    ·
                      rfl

theorem cell22_1556788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_1556788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556788 prefixEnd_1556788 := by exact prefixLift 1556788
  have htrace : WordTrace (prefixWord ++ tailWord_1556788) baseStart_1556788 baseEnd_1556788 := by
    simpa [prefixWord, tailWord_1556788, baseEnd_1556788] using wordTrace_append hprefix tailTrace_1556788
  have hstable : (prefixWord ++ tailWord_1556788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556788).length < 2 ^ (prefixWord ++ tailWord_1556788).sum := by decide
  have hdescent : baseEnd_1556788 < baseStart_1556788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556820 : List Nat := [2, 4, 1, 1, 2, 4, 2, 2, 4]
def baseStart_1556820 : Nat := 118140960795 + 1556820 * 2 ^ 59
def prefixEnd_1556820 : Nat := 4983230072969 + 3 ^ 40 * 1556820 * 2
def baseEnd_1556820 : Nat := 177643767229489815175627

theorem tailTrace_1556820 : CollatzResearch.WordTrace tailWord_1556820 prefixEnd_1556820 177643767229489815175627 := by
  unfold tailWord_1556820
  simp only [CollatzResearch.WordTrace]
  refine ⟨28390945109957249266513957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37854593479942999022018609 28390945109957249266513957)
  ·
    refine ⟨5323302208116984237471367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28390945109957249266513957 5323302208116984237471367)
    ·
      refine ⟨7984953312175476356207051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5323302208116984237471367 7984953312175476356207051)
      ·
        refine ⟨11977429968263214534310577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7984953312175476356207051 11977429968263214534310577)
        ·
          refine ⟨8983072476197410900732933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11977429968263214534310577 8983072476197410900732933)
          ·
            refine ⟨1684326089287014543887425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8983072476197410900732933 1684326089287014543887425)
            ·
              refine ⟨1263244566965260907915569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1684326089287014543887425 1263244566965260907915569)
              ·
                refine ⟨947433425223945680936677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1263244566965260907915569 947433425223945680936677)
                ·
                  refine ⟨177643767229489815175627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 947433425223945680936677 177643767229489815175627)
                  ·
                    rfl

theorem cell22_1556820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_1556820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556820 prefixEnd_1556820 := by exact prefixLift 1556820
  have htrace : WordTrace (prefixWord ++ tailWord_1556820) baseStart_1556820 baseEnd_1556820 := by
    simpa [prefixWord, tailWord_1556820, baseEnd_1556820] using wordTrace_append hprefix tailTrace_1556820
  have hstable : (prefixWord ++ tailWord_1556820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556820).length < 2 ^ (prefixWord ++ tailWord_1556820).sum := by decide
  have hdescent : baseEnd_1556820 < baseStart_1556820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556876 : List Nat := [2, 2, 1, 2, 1, 4, 3, 2, 5]
def baseStart_1556876 : Nat := 118140960795 + 1556876 * 2 ^ 59
def prefixEnd_1556876 : Nat := 4983230072969 + 3 ^ 40 * 1556876 * 2
def baseEnd_1556876 : Nat := 177650157210967988708903

theorem tailTrace_1556876 : CollatzResearch.WordTrace tailWord_1556876 prefixEnd_1556876 177650157210967988708903 := by
  unfold tailWord_1556876
  simp only [CollatzResearch.WordTrace]
  refine ⟨28391966353855810048533241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37855955138474413398044321 28391966353855810048533241)
  ·
    refine ⟨21293974765391857536399931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28391966353855810048533241 21293974765391857536399931)
    ·
      refine ⟨31940962148087786304599897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21293974765391857536399931 31940962148087786304599897)
      ·
        refine ⟨23955721611065839728449923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31940962148087786304599897 23955721611065839728449923)
        ·
          refine ⟨35933582416598759592674885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23955721611065839728449923 35933582416598759592674885)
          ·
            refine ⟨6737546703112267423626541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35933582416598759592674885 6737546703112267423626541)
            ·
              refine ⟨2526580013667100283859953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6737546703112267423626541 2526580013667100283859953)
              ·
                refine ⟨1894935010250325212894965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2526580013667100283859953 1894935010250325212894965)
                ·
                  refine ⟨177650157210967988708903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1894935010250325212894965 177650157210967988708903)
                  ·
                    rfl

theorem cell22_1556876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_1556876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556876 prefixEnd_1556876 := by exact prefixLift 1556876
  have htrace : WordTrace (prefixWord ++ tailWord_1556876) baseStart_1556876 baseEnd_1556876 := by
    simpa [prefixWord, tailWord_1556876, baseEnd_1556876] using wordTrace_append hprefix tailTrace_1556876
  have hstable : (prefixWord ++ tailWord_1556876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556876).length < 2 ^ (prefixWord ++ tailWord_1556876).sum := by decide
  have hdescent : baseEnd_1556876 < baseStart_1556876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556886 : List Nat := [5, 3, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_1556886 : Nat := 118140960795 + 1556886 * 2 ^ 59
def prefixEnd_1556886 : Nat := 4983230072969 + 3 ^ 40 * 1556886 * 2
def baseEnd_1556886 : Nat := 532953894837267273376679

theorem tailTrace_1556886 : CollatzResearch.WordTrace tailWord_1556886 prefixEnd_1556886 532953894837267273376679 := by
  unfold tailWord_1556886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3549018589854711987808157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37856198291783594536620341 3549018589854711987808157)
  ·
    refine ⟨1330881971195516995428059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3549018589854711987808157 1330881971195516995428059)
    ·
      refine ⟨1996322956793275493142089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1330881971195516995428059 1996322956793275493142089)
      ·
        refine ⟨1497242217594956619856567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1996322956793275493142089 1497242217594956619856567)
        ·
          refine ⟨2245863326392434929784851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1497242217594956619856567 2245863326392434929784851)
          ·
            refine ⟨3368794989588652394677277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2245863326392434929784851 3368794989588652394677277)
            ·
              refine ⟨1263298121095744648003979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3368794989588652394677277 1263298121095744648003979)
              ·
                refine ⟨1894947181643616972005969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1263298121095744648003979 1894947181643616972005969)
                ·
                  refine ⟨1421210386232712729004477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1894947181643616972005969 1421210386232712729004477)
                  ·
                    refine ⟨532953894837267273376679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1421210386232712729004477 532953894837267273376679)
                    ·
                      rfl

theorem cell22_1556886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_1556886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556886 prefixEnd_1556886 := by exact prefixLift 1556886
  have htrace : WordTrace (prefixWord ++ tailWord_1556886) baseStart_1556886 baseEnd_1556886 := by
    simpa [prefixWord, tailWord_1556886, baseEnd_1556886] using wordTrace_append hprefix tailTrace_1556886
  have hstable : (prefixWord ++ tailWord_1556886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556886).length < 2 ^ (prefixWord ++ tailWord_1556886).sum := by decide
  have hdescent : baseEnd_1556886 < baseStart_1556886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556953 : List Nat := [1, 2, 1, 2, 4, 1, 3, 3, 2, 3]
def baseStart_1556953 : Nat := 118140960795 + 1556953 * 2 ^ 59
def prefixEnd_1556953 : Nat := 4983230072969 + 3 ^ 40 * 1556953 * 2
def baseEnd_1556953 : Nat := 532976830306501431951473

theorem tailTrace_1556953 : CollatzResearch.WordTrace tailWord_1556953 prefixEnd_1556953 532976830306501431951473 := by
  unfold tailWord_1556953
  simp only [CollatzResearch.WordTrace]
  refine ⟨56786741128432662247619513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37857827418955108165079675 56786741128432662247619513)
  ·
    refine ⟨42590055846324496685714635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56786741128432662247619513 42590055846324496685714635)
    ·
      refine ⟨63885083769486745028571953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42590055846324496685714635 63885083769486745028571953)
      ·
        refine ⟨47913812827115058771428965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63885083769486745028571953 47913812827115058771428965)
        ·
          refine ⟨8983839905084073519642931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47913812827115058771428965 8983839905084073519642931)
          ·
            refine ⟨13475759857626110279464397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8983839905084073519642931 13475759857626110279464397)
            ·
              refine ⟨5053409946609791354799149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13475759857626110279464397 5053409946609791354799149)
              ·
                refine ⟨1895028729978671758049681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5053409946609791354799149 1895028729978671758049681)
                ·
                  refine ⟨1421271547484003818537261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1895028729978671758049681 1421271547484003818537261)
                  ·
                    refine ⟨532976830306501431951473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1421271547484003818537261 532976830306501431951473)
                    ·
                      rfl

theorem cell22_1556953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 3].length) (baseStart_1556953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556953 prefixEnd_1556953 := by exact prefixLift 1556953
  have htrace : WordTrace (prefixWord ++ tailWord_1556953) baseStart_1556953 baseEnd_1556953 := by
    simpa [prefixWord, tailWord_1556953, baseEnd_1556953] using wordTrace_append hprefix tailTrace_1556953
  have hstable : (prefixWord ++ tailWord_1556953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556953).length < 2 ^ (prefixWord ++ tailWord_1556953).sum := by decide
  have hdescent : baseEnd_1556953 < baseStart_1556953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556968 : List Nat := [2, 1, 4, 1, 1, 4, 2, 1, 2, 4]
def baseStart_1556968 : Nat := 118140960795 + 1556968 * 2 ^ 59
def prefixEnd_1556968 : Nat := 4983230072969 + 3 ^ 40 * 1556968 * 2
def baseEnd_1556968 : Nat := 532981965113046392826427

theorem tailTrace_1556968 : CollatzResearch.WordTrace tailWord_1556968 prefixEnd_1556968 532981965113046392826427 := by
  unfold tailWord_1556968
  simp only [CollatzResearch.WordTrace]
  refine ⟨28393644111689159904707779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37858192148918879872943705 28393644111689159904707779)
  ·
    refine ⟨42590466167533739857061669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28393644111689159904707779 42590466167533739857061669)
    ·
      refine ⟨7985712406412576223199063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42590466167533739857061669 7985712406412576223199063)
      ·
        refine ⟨11978568609618864334798595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7985712406412576223199063 11978568609618864334798595)
        ·
          refine ⟨17967852914428296502197893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11978568609618864334798595 17967852914428296502197893)
          ·
            refine ⟨3368972421455305594162105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17967852914428296502197893 3368972421455305594162105)
            ·
              refine ⟨2526729316091479195621579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3368972421455305594162105 2526729316091479195621579)
              ·
                refine ⟨3790093974137218793432369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2526729316091479195621579 3790093974137218793432369)
                ·
                  refine ⟨2842570480602914095074277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3790093974137218793432369 2842570480602914095074277)
                  ·
                    refine ⟨532981965113046392826427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2842570480602914095074277 532981965113046392826427)
                    ·
                      rfl

theorem cell22_1556968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_1556968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1556968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1556968 prefixEnd_1556968 := by exact prefixLift 1556968
  have htrace : WordTrace (prefixWord ++ tailWord_1556968) baseStart_1556968 baseEnd_1556968 := by
    simpa [prefixWord, tailWord_1556968, baseEnd_1556968] using wordTrace_append hprefix tailTrace_1556968
  have hstable : (prefixWord ++ tailWord_1556968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556968).length < 2 ^ (prefixWord ++ tailWord_1556968).sum := by decide
  have hdescent : baseEnd_1556968 < baseStart_1556968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557011 : List Nat := [1, 1, 1, 2, 1, 5, 1, 5, 5]
def baseStart_1557011 : Nat := 118140960795 + 1557011 * 2 ^ 59
def prefixEnd_1557011 : Nat := 4983230072969 + 3 ^ 40 * 1557011 * 2
def baseEnd_1557011 : Nat := 177665561630602871333765

theorem tailTrace_1557011 : CollatzResearch.WordTrace tailWord_1557011 prefixEnd_1557011 177665561630602871333765 := by
  unfold tailWord_1557011
  simp only [CollatzResearch.WordTrace]
  refine ⟨56788856562222538153230887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37859237708148358768820591 56788856562222538153230887)
  ·
    refine ⟨85183284843333807229846331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56788856562222538153230887 85183284843333807229846331)
    ·
      refine ⟨127774927265000710844769497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85183284843333807229846331 127774927265000710844769497)
      ·
        refine ⟨95831195448750533133577123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127774927265000710844769497 95831195448750533133577123)
        ·
          refine ⟨143746793173125799700365685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95831195448750533133577123 143746793173125799700365685)
          ·
            refine ⟨13476261859980543721909283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143746793173125799700365685 13476261859980543721909283)
            ·
              refine ⟨20214392789970815582863925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13476261859980543721909283 20214392789970815582863925)
              ·
                refine ⟨1895099324059763960893493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20214392789970815582863925 1895099324059763960893493)
                ·
                  refine ⟨177665561630602871333765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1895099324059763960893493 177665561630602871333765)
                  ·
                    rfl

theorem cell22_1557011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 5].length) (baseStart_1557011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557011 prefixEnd_1557011 := by exact prefixLift 1557011
  have htrace : WordTrace (prefixWord ++ tailWord_1557011) baseStart_1557011 baseEnd_1557011 := by
    simpa [prefixWord, tailWord_1557011, baseEnd_1557011] using wordTrace_append hprefix tailTrace_1557011
  have hstable : (prefixWord ++ tailWord_1557011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557011).length < 2 ^ (prefixWord ++ tailWord_1557011).sum := by decide
  have hdescent : baseEnd_1557011 < baseStart_1557011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557026 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_1557026 : Nat := 118140960795 + 1557026 * 2 ^ 59
def prefixEnd_1557026 : Nat := 4983230072969 + 3 ^ 40 * 1557026 * 2
def baseEnd_1557026 : Nat := 533001819698353574876249

theorem tailTrace_1557026 : CollatzResearch.WordTrace tailWord_1557026 prefixEnd_1557026 533001819698353574876249 := by
  unfold tailWord_1557026
  simp only [CollatzResearch.WordTrace]
  refine ⟨14197350914292048928756733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37859602438112130476684621 14197350914292048928756733)
  ·
    refine ⟨5324006592859518348283775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14197350914292048928756733 5324006592859518348283775)
    ·
      refine ⟨7986009889289277522425663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5324006592859518348283775 7986009889289277522425663)
      ·
        refine ⟨11979014833933916283638495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7986009889289277522425663 11979014833933916283638495)
        ·
          refine ⟨17968522250900874425457743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11979014833933916283638495 17968522250900874425457743)
          ·
            refine ⟨26952783376351311638186615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17968522250900874425457743 26952783376351311638186615)
            ·
              refine ⟨40429175064526967457279923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26952783376351311638186615 40429175064526967457279923)
              ·
                refine ⟨60643762596790451185919885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40429175064526967457279923 60643762596790451185919885)
                ·
                  refine ⟨22741410973796419194719957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60643762596790451185919885 22741410973796419194719957)
                  ·
                    refine ⟨533001819698353574876249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22741410973796419194719957 533001819698353574876249)
                    ·
                      rfl

theorem cell22_1557026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_1557026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557026 prefixEnd_1557026 := by exact prefixLift 1557026
  have htrace : WordTrace (prefixWord ++ tailWord_1557026) baseStart_1557026 baseEnd_1557026 := by
    simpa [prefixWord, tailWord_1557026, baseEnd_1557026] using wordTrace_append hprefix tailTrace_1557026
  have hstable : (prefixWord ++ tailWord_1557026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557026).length < 2 ^ (prefixWord ++ tailWord_1557026).sum := by decide
  have hdescent : baseEnd_1557026 < baseStart_1557026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557032 : List Nat := [2, 1, 5, 2, 1, 1, 1, 5, 1, 3]
def baseStart_1557032 : Nat := 118140960795 + 1557032 * 2 ^ 59
def prefixEnd_1557032 : Nat := 4983230072969 + 3 ^ 40 * 1557032 * 2
def baseEnd_1557032 : Nat := 533003873620971559226231

theorem tailTrace_1557032 : CollatzResearch.WordTrace tailWord_1557032 prefixEnd_1557032 533003873620971559226231 := by
  unfold tailWord_1557032
  simp only [CollatzResearch.WordTrace]
  refine ⟨28394811247573229369872675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37859748330097639159830233 28394811247573229369872675)
  ·
    refine ⟨42592216871359844054809013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28394811247573229369872675 42592216871359844054809013)
    ·
      refine ⟨3993020331689985380138345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42592216871359844054809013 3993020331689985380138345)
      ·
        refine ⟨2994765248767489035103759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3993020331689985380138345 2994765248767489035103759)
        ·
          refine ⟨4492147873151233552655639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2994765248767489035103759 4492147873151233552655639)
          ·
            refine ⟨6738221809726850328983459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4492147873151233552655639 6738221809726850328983459)
            ·
              refine ⟨10107332714590275493475189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6738221809726850328983459 10107332714590275493475189)
              ·
                refine ⟨947562441992838327513299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10107332714590275493475189 947562441992838327513299)
                ·
                  refine ⟨1421343662989257491269949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947562441992838327513299 1421343662989257491269949)
                  ·
                    refine ⟨533003873620971559226231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1421343662989257491269949 533003873620971559226231)
                    ·
                      rfl

theorem cell22_1557032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_1557032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557032 prefixEnd_1557032 := by exact prefixLift 1557032
  have htrace : WordTrace (prefixWord ++ tailWord_1557032) baseStart_1557032 baseEnd_1557032 := by
    simpa [prefixWord, tailWord_1557032, baseEnd_1557032] using wordTrace_append hprefix tailTrace_1557032
  have hstable : (prefixWord ++ tailWord_1557032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557032).length < 2 ^ (prefixWord ++ tailWord_1557032).sum := by decide
  have hdescent : baseEnd_1557032 < baseStart_1557032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557056 : List Nat := [2, 1, 1, 2, 2, 2, 3, 3, 6]
def baseStart_1557056 : Nat := 118140960795 + 1557056 * 2 ^ 59
def prefixEnd_1557056 : Nat := 4983230072969 + 3 ^ 40 * 1557056 * 2
def baseEnd_1557056 : Nat := 177670696437147832208719

theorem tailTrace_1557056 : CollatzResearch.WordTrace tailWord_1557056 prefixEnd_1557056 177670696437147832208719 := by
  unfold tailWord_1557056
  simp only [CollatzResearch.WordTrace]
  refine ⟨28395248923529755419309511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37860331898039673892412681 28395248923529755419309511)
  ·
    refine ⟨42592873385294633128964267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28395248923529755419309511 42592873385294633128964267)
    ·
      refine ⟨63889310077941949693446401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42592873385294633128964267 63889310077941949693446401)
      ·
        refine ⟨47916982558456462270084801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63889310077941949693446401 47916982558456462270084801)
        ·
          refine ⟨35937736918842346702563601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47916982558456462270084801 35937736918842346702563601)
          ·
            refine ⟨26953302689131760026922701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35937736918842346702563601 26953302689131760026922701)
            ·
              refine ⟨10107488508424410010096013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26953302689131760026922701 10107488508424410010096013)
              ·
                refine ⟨3790308190659153753786005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10107488508424410010096013 3790308190659153753786005)
                ·
                  refine ⟨177670696437147832208719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3790308190659153753786005 177670696437147832208719)
                  ·
                    rfl

theorem cell22_1557056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 6].length) (baseStart_1557056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557056 prefixEnd_1557056 := by exact prefixLift 1557056
  have htrace : WordTrace (prefixWord ++ tailWord_1557056) baseStart_1557056 baseEnd_1557056 := by
    simpa [prefixWord, tailWord_1557056, baseEnd_1557056] using wordTrace_append hprefix tailTrace_1557056
  have hstable : (prefixWord ++ tailWord_1557056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557056).length < 2 ^ (prefixWord ++ tailWord_1557056).sum := by decide
  have hdescent : baseEnd_1557056 < baseStart_1557056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557088 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 4, 3]
def baseStart_1557088 : Nat := 118140960795 + 1557088 * 2 ^ 59
def prefixEnd_1557088 : Nat := 4983230072969 + 3 ^ 40 * 1557088 * 2
def baseEnd_1557088 : Nat := 533023043565406079826059

theorem tailTrace_1557088 : CollatzResearch.WordTrace tailWord_1557088 prefixEnd_1557088 533023043565406079826059 := by
  unfold tailWord_1557088
  simp only [CollatzResearch.WordTrace]
  refine ⟨28395832491471790151891959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37861109988629053535855945 28395832491471790151891959)
  ·
    refine ⟨42593748737207685227837939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28395832491471790151891959 42593748737207685227837939)
    ·
      refine ⟨63890623105811527841756909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42593748737207685227837939 63890623105811527841756909)
      ·
        refine ⟨23958983664679322940658841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63890623105811527841756909 23958983664679322940658841)
        ·
          refine ⟨17969237748509492205494131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23958983664679322940658841 17969237748509492205494131)
          ·
            refine ⟨26953856622764238308241197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17969237748509492205494131 26953856622764238308241197)
            ·
              refine ⟨10107696233536589365590449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26953856622764238308241197 10107696233536589365590449)
              ·
                refine ⟨7580772175152442024192837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10107696233536589365590449 7580772175152442024192837)
                ·
                  refine ⟨1421394782841082879536157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7580772175152442024192837 1421394782841082879536157)
                  ·
                    refine ⟨533023043565406079826059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1421394782841082879536157 533023043565406079826059)
                    ·
                      rfl

theorem cell22_1557088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 4, 3].length) (baseStart_1557088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557088 prefixEnd_1557088 := by exact prefixLift 1557088
  have htrace : WordTrace (prefixWord ++ tailWord_1557088) baseStart_1557088 baseEnd_1557088 := by
    simpa [prefixWord, tailWord_1557088, baseEnd_1557088] using wordTrace_append hprefix tailTrace_1557088
  have hstable : (prefixWord ++ tailWord_1557088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557088).length < 2 ^ (prefixWord ++ tailWord_1557088).sum := by decide
  have hdescent : baseEnd_1557088 < baseStart_1557088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557131 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 4, 6]
def baseStart_1557131 : Nat := 118140960795 + 1557131 * 2 ^ 59
def prefixEnd_1557131 : Nat := 4983230072969 + 3 ^ 40 * 1557131 * 2
def baseEnd_1557131 : Nat := 533037763344168301000927

theorem tailTrace_1557131 : CollatzResearch.WordTrace tailWord_1557131 prefixEnd_1557131 533037763344168301000927 := by
  unfold tailWord_1557131
  simp only [CollatzResearch.WordTrace]
  refine ⟨56793233321787798647599247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37862155547858532431732831 56793233321787798647599247)
  ·
    refine ⟨85189849982681697971398871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56793233321787798647599247 85189849982681697971398871)
    ·
      refine ⟨127784774974022546957098307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85189849982681697971398871 127784774974022546957098307)
      ·
        refine ⟨191677162461033820435647461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127784774974022546957098307 191677162461033820435647461)
        ·
          refine ⟨35939467961443841331683899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191677162461033820435647461 35939467961443841331683899)
          ·
            refine ⟨53909201942165761997525849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35939467961443841331683899 53909201942165761997525849)
            ·
              refine ⟨40431901456624321498144387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53909201942165761997525849 40431901456624321498144387)
              ·
                refine ⟨60647852184936482247216581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40431901456624321498144387 60647852184936482247216581)
                ·
                  refine ⟨11371472284675590421353109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60647852184936482247216581 11371472284675590421353109)
                  ·
                    refine ⟨533037763344168301000927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11371472284675590421353109 533037763344168301000927)
                    ·
                      rfl

theorem cell22_1557131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 6].length) (baseStart_1557131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557131 prefixEnd_1557131 := by exact prefixLift 1557131
  have htrace : WordTrace (prefixWord ++ tailWord_1557131) baseStart_1557131 baseEnd_1557131 := by
    simpa [prefixWord, tailWord_1557131, baseEnd_1557131] using wordTrace_append hprefix tailTrace_1557131
  have hstable : (prefixWord ++ tailWord_1557131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557131).length < 2 ^ (prefixWord ++ tailWord_1557131).sum := by decide
  have hdescent : baseEnd_1557131 < baseStart_1557131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557167 : List Nat := [1, 1, 2, 1, 2, 6, 1, 4, 1, 3]
def baseStart_1557167 : Nat := 118140960795 + 1557167 * 2 ^ 59
def prefixEnd_1557167 : Nat := 4983230072969 + 3 ^ 40 * 1557167 * 2
def baseEnd_1557167 : Nat := 533050086879876207100817

theorem tailTrace_1557167 : CollatzResearch.WordTrace tailWord_1557167 prefixEnd_1557167 533050086879876207100817 := by
  unfold tailWord_1557167
  simp only [CollatzResearch.WordTrace]
  refine ⟨56794546349657376795909755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37863030899771584530606503 56794546349657376795909755)
  ·
    refine ⟨85191819524486065193864633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56794546349657376795909755 85191819524486065193864633)
    ·
      refine ⟨63893864643364548895398475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85191819524486065193864633 63893864643364548895398475)
      ·
        refine ⟨95840796965046823343097713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63893864643364548895398475 95840796965046823343097713)
        ·
          refine ⟨71880597723785117507323285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95840796965046823343097713 71880597723785117507323285)
          ·
            refine ⟨3369403018302427383155779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71880597723785117507323285 3369403018302427383155779)
            ·
              refine ⟨5054104527453641074733669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3369403018302427383155779 5054104527453641074733669)
              ·
                refine ⟨947644598897557701512563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5054104527453641074733669 947644598897557701512563)
                ·
                  refine ⟨1421466898346336552268845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947644598897557701512563 1421466898346336552268845)
                  ·
                    refine ⟨533050086879876207100817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1421466898346336552268845 533050086879876207100817)
                    ·
                      rfl

theorem cell22_1557167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 1, 3].length) (baseStart_1557167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557167 prefixEnd_1557167 := by exact prefixLift 1557167
  have htrace : WordTrace (prefixWord ++ tailWord_1557167) baseStart_1557167 baseEnd_1557167 := by
    simpa [prefixWord, tailWord_1557167, baseEnd_1557167] using wordTrace_append hprefix tailTrace_1557167
  have hstable : (prefixWord ++ tailWord_1557167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557167).length < 2 ^ (prefixWord ++ tailWord_1557167).sum := by decide
  have hdescent : baseEnd_1557167 < baseStart_1557167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557178 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 2, 5]
def baseStart_1557178 : Nat := 118140960795 + 1557178 * 2 ^ 59
def prefixEnd_1557178 : Nat := 4983230072969 + 3 ^ 40 * 1557178 * 2
def baseEnd_1557178 : Nat := 533053852404675845075783

theorem tailTrace_1557178 : CollatzResearch.WordTrace tailWord_1557178 prefixEnd_1557178 533053852404675845075783 := by
  unfold tailWord_1557178
  simp only [CollatzResearch.WordTrace]
  refine ⟨14198736888154381418640047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37863298368411683783040125 14198736888154381418640047)
  ·
    refine ⟨21298105332231572127960071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14198736888154381418640047 21298105332231572127960071)
    ·
      refine ⟨31947157998347358191940107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21298105332231572127960071 31947157998347358191940107)
      ·
        refine ⟨47920736997521037287910161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31947157998347358191940107 47920736997521037287910161)
        ·
          refine ⟨35940552748140777965932621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47920736997521037287910161 35940552748140777965932621)
          ·
            refine ⟨13477707280552791737224733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35940552748140777965932621 13477707280552791737224733)
            ·
              refine ⟨5054140230207296901459275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13477707280552791737224733 5054140230207296901459275)
              ·
                refine ⟨7581210345310945352188913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5054140230207296901459275 7581210345310945352188913)
                ·
                  refine ⟨5685907758983209014141685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7581210345310945352188913 5685907758983209014141685)
                  ·
                    refine ⟨533053852404675845075783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5685907758983209014141685 533053852404675845075783)
                    ·
                      rfl

theorem cell22_1557178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_1557178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557178 prefixEnd_1557178 := by exact prefixLift 1557178
  have htrace : WordTrace (prefixWord ++ tailWord_1557178) baseStart_1557178 baseEnd_1557178 := by
    simpa [prefixWord, tailWord_1557178, baseEnd_1557178] using wordTrace_append hprefix tailTrace_1557178
  have hstable : (prefixWord ++ tailWord_1557178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557178).length < 2 ^ (prefixWord ++ tailWord_1557178).sum := by decide
  have hdescent : baseEnd_1557178 < baseStart_1557178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557210 : List Nat := [3, 1, 1, 2, 2, 2, 3, 3, 1, 4]
def baseStart_1557210 : Nat := 118140960795 + 1557210 * 2 ^ 59
def prefixEnd_1557210 : Nat := 4983230072969 + 3 ^ 40 * 1557210 * 2
def baseEnd_1557210 : Nat := 533064806658638428275685

theorem tailTrace_1557210 : CollatzResearch.WordTrace tailWord_1557210 prefixEnd_1557210 533064806658638428275685 := by
  unfold tailWord_1557210
  simp only [CollatzResearch.WordTrace]
  refine ⟨14199028672125398784931271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37864076459001063426483389 14199028672125398784931271)
  ·
    refine ⟨21298543008188098177396907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14199028672125398784931271 21298543008188098177396907)
    ·
      refine ⟨31947814512282147266095361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21298543008188098177396907 31947814512282147266095361)
      ·
        refine ⟨23960860884211610449571521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31947814512282147266095361 23960860884211610449571521)
        ·
          refine ⟨17970645663158707837178641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23960860884211610449571521 17970645663158707837178641)
          ·
            refine ⟨13477984247369030877883981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17970645663158707837178641 13477984247369030877883981)
            ·
              refine ⟨5054244092763386579206493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13477984247369030877883981 5054244092763386579206493)
              ·
                refine ⟨1895341534786269967202435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5054244092763386579206493 1895341534786269967202435)
                ·
                  refine ⟨2843012302179404950803653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1895341534786269967202435 2843012302179404950803653)
                  ·
                    refine ⟨533064806658638428275685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2843012302179404950803653 533064806658638428275685)
                    ·
                      rfl

theorem cell22_1557210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_1557210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557210 prefixEnd_1557210 := by exact prefixLift 1557210
  have htrace : WordTrace (prefixWord ++ tailWord_1557210) baseStart_1557210 baseEnd_1557210 := by
    simpa [prefixWord, tailWord_1557210, baseEnd_1557210] using wordTrace_append hprefix tailTrace_1557210
  have hstable : (prefixWord ++ tailWord_1557210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557210).length < 2 ^ (prefixWord ++ tailWord_1557210).sum := by decide
  have hdescent : baseEnd_1557210 < baseStart_1557210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557225 : List Nat := [1, 2, 1, 1, 1, 2, 6, 4, 4]
def baseStart_1557225 : Nat := 118140960795 + 1557225 * 2 ^ 59
def prefixEnd_1557225 : Nat := 4983230072969 + 3 ^ 40 * 1557225 * 2
def baseEnd_1557225 : Nat := 177689980488394463050213

theorem tailTrace_1557225 : CollatzResearch.WordTrace tailWord_1557225 prefixEnd_1557225 177689980488394463050213 := by
  unfold tailWord_1557225
  simp only [CollatzResearch.WordTrace]
  refine ⟨56796661783447252701521129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37864441188964835134347419 56796661783447252701521129)
  ·
    refine ⟨42597496337585439526140847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56796661783447252701521129 42597496337585439526140847)
    ·
      refine ⟨63896244506378159289211271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42597496337585439526140847 63896244506378159289211271)
      ·
        refine ⟨95844366759567238933816907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63896244506378159289211271 95844366759567238933816907)
        ·
          refine ⟨143766550139350858400725361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95844366759567238933816907 143766550139350858400725361)
          ·
            refine ⟨107824912604513143800544021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143766550139350858400725361 107824912604513143800544021)
            ·
              refine ⟨5054292778336553615650501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107824912604513143800544021 5054292778336553615650501)
              ·
                refine ⟨947679895938103802934469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5054292778336553615650501 947679895938103802934469)
                ·
                  refine ⟨177689980488394463050213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 947679895938103802934469 177689980488394463050213)
                  ·
                    rfl

theorem cell22_1557225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 4].length) (baseStart_1557225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557225 prefixEnd_1557225 := by exact prefixLift 1557225
  have htrace : WordTrace (prefixWord ++ tailWord_1557225) baseStart_1557225 baseEnd_1557225 := by
    simpa [prefixWord, tailWord_1557225, baseEnd_1557225] using wordTrace_append hprefix tailTrace_1557225
  have hstable : (prefixWord ++ tailWord_1557225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557225).length < 2 ^ (prefixWord ++ tailWord_1557225).sum := by decide
  have hdescent : baseEnd_1557225 < baseStart_1557225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557255 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 1, 6]
def baseStart_1557255 : Nat := 118140960795 + 1557255 * 2 ^ 59
def prefixEnd_1557255 : Nat := 4983230072969 + 3 ^ 40 * 1557255 * 2
def baseEnd_1557255 : Nat := 533080211078273310900547

theorem tailTrace_1557255 : CollatzResearch.WordTrace tailWord_1557255 prefixEnd_1557255 533080211078273310900547 := by
  unfold tailWord_1557255
  simp only [CollatzResearch.WordTrace]
  refine ⟨56797755973338567825113219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37865170648892378550075479 56797755973338567825113219)
  ·
    refine ⟨85196633960007851737669829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56797755973338567825113219 85196633960007851737669829)
    ·
      refine ⟨15974368867501472200813093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85196633960007851737669829 15974368867501472200813093)
      ·
        refine ⟨2995194162656526037652455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15974368867501472200813093 2995194162656526037652455)
        ·
          refine ⟨4492791243984789056478683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2995194162656526037652455 4492791243984789056478683)
          ·
            refine ⟨6739186865977183584718025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4492791243984789056478683 6739186865977183584718025)
            ·
              refine ⟨5054390149482887688538519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6739186865977183584718025 5054390149482887688538519)
              ·
                refine ⟨7581585224224331532807779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5054390149482887688538519 7581585224224331532807779)
                ·
                  refine ⟨11372377836336497299211669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7581585224224331532807779 11372377836336497299211669)
                  ·
                    refine ⟨533080211078273310900547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11372377836336497299211669 533080211078273310900547)
                    ·
                      rfl

theorem cell22_1557255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_1557255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557255 prefixEnd_1557255 := by exact prefixLift 1557255
  have htrace : WordTrace (prefixWord ++ tailWord_1557255) baseStart_1557255 baseEnd_1557255 := by
    simpa [prefixWord, tailWord_1557255, baseEnd_1557255] using wordTrace_append hprefix tailTrace_1557255
  have hstable : (prefixWord ++ tailWord_1557255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557255).length < 2 ^ (prefixWord ++ tailWord_1557255).sum := by decide
  have hdescent : baseEnd_1557255 < baseStart_1557255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557283 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 2, 6]
def baseStart_1557283 : Nat := 118140960795 + 1557283 * 2 ^ 59
def prefixEnd_1557283 : Nat := 4983230072969 + 3 ^ 40 * 1557283 * 2
def baseEnd_1557283 : Nat := 533089796050490571200461

theorem tailTrace_1557283 : CollatzResearch.WordTrace tailWord_1557283 prefixEnd_1557283 533089796050490571200461 := by
  unfold tailWord_1557283
  simp only [CollatzResearch.WordTrace]
  refine ⟨56798777217237128607132503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37865851478158085738088335 56798777217237128607132503)
  ·
    refine ⟨85198165825855692910698755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56798777217237128607132503 85198165825855692910698755)
    ·
      refine ⟨127797248738783539366048133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85198165825855692910698755 127797248738783539366048133)
      ·
        refine ⟨23961984138521913631134025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127797248738783539366048133 23961984138521913631134025)
        ·
          refine ⟨17971488103891435223350519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23961984138521913631134025 17971488103891435223350519)
          ·
            refine ⟨26957232155837152835025779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17971488103891435223350519 26957232155837152835025779)
            ·
              refine ⟨40435848233755729252538669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26957232155837152835025779 40435848233755729252538669)
              ·
                refine ⟨15163443087658398469702001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40435848233755729252538669 15163443087658398469702001)
                ·
                  refine ⟨11372582315743798852276501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15163443087658398469702001 11372582315743798852276501)
                  ·
                    refine ⟨533089796050490571200461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11372582315743798852276501 533089796050490571200461)
                    ·
                      rfl

theorem cell22_1557283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 6].length) (baseStart_1557283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557283 prefixEnd_1557283 := by exact prefixLift 1557283
  have htrace : WordTrace (prefixWord ++ tailWord_1557283) baseStart_1557283 baseEnd_1557283 := by
    simpa [prefixWord, tailWord_1557283, baseEnd_1557283] using wordTrace_append hprefix tailTrace_1557283
  have hstable : (prefixWord ++ tailWord_1557283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557283).length < 2 ^ (prefixWord ++ tailWord_1557283).sum := by decide
  have hdescent : baseEnd_1557283 < baseStart_1557283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557330 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_1557330 : Nat := 118140960795 + 1557330 * 2 ^ 59
def prefixEnd_1557330 : Nat := 4983230072969 + 3 ^ 40 * 1557330 * 2
def baseEnd_1557330 : Nat := 533105885110998115275317

theorem tailTrace_1557330 : CollatzResearch.WordTrace tailWord_1557330 prefixEnd_1557330 533105885110998115275317 := by
  unfold tailWord_1557330
  simp only [CollatzResearch.WordTrace]
  refine ⟨14200122862016713908523361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37866994298711237089395629 14200122862016713908523361)
  ·
    refine ⟨10650092146512535431392521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14200122862016713908523361 10650092146512535431392521)
    ·
      refine ⟨7987569109884401573544391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10650092146512535431392521 7987569109884401573544391)
      ·
        refine ⟨11981353664826602360316587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7987569109884401573544391 11981353664826602360316587)
        ·
          refine ⟨17972030497239903540474881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11981353664826602360316587 17972030497239903540474881)
          ·
            refine ⟨13479022872929927655356161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17972030497239903540474881 13479022872929927655356161)
            ·
              refine ⟨10109267154697445741517121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13479022872929927655356161 10109267154697445741517121)
              ·
                refine ⟨7581950366023084306137841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10109267154697445741517121 7581950366023084306137841)
                ·
                  refine ⟨5686462774517313229603381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7581950366023084306137841 5686462774517313229603381)
                  ·
                    refine ⟨533105885110998115275317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5686462774517313229603381 533105885110998115275317)
                    ·
                      rfl

theorem cell22_1557330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_1557330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557330 prefixEnd_1557330 := by exact prefixLift 1557330
  have htrace : WordTrace (prefixWord ++ tailWord_1557330) baseStart_1557330 baseEnd_1557330 := by
    simpa [prefixWord, tailWord_1557330, baseEnd_1557330] using wordTrace_append hprefix tailTrace_1557330
  have hstable : (prefixWord ++ tailWord_1557330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557330).length < 2 ^ (prefixWord ++ tailWord_1557330).sum := by decide
  have hdescent : baseEnd_1557330 < baseStart_1557330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557375 : List Nat := [1, 1, 2, 2, 1, 1, 6, 2, 1, 5]
def baseStart_1557375 : Nat := 118140960795 + 1557375 * 2 ^ 59
def prefixEnd_1557375 : Nat := 4983230072969 + 3 ^ 40 * 1557375 * 2
def baseEnd_1557375 : Nat := 533121289530632997900179

theorem tailTrace_1557375 : CollatzResearch.WordTrace tailWord_1557375 prefixEnd_1557375 533121289530632997900179 := by
  unfold tailWord_1557375
  simp only [CollatzResearch.WordTrace]
  refine ⟨56802132732903828319481579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37868088488602552212987719 56802132732903828319481579)
  ·
    refine ⟨85203199099355742479222369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56802132732903828319481579 85203199099355742479222369)
    ·
      refine ⟨63902399324516806859416777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85203199099355742479222369 63902399324516806859416777)
      ·
        refine ⟨47926799493387605144562583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63902399324516806859416777 47926799493387605144562583)
        ·
          refine ⟨71890199240081407716843875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47926799493387605144562583 71890199240081407716843875)
          ·
            refine ⟨107835298860122111575265813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71890199240081407716843875 107835298860122111575265813)
            ·
              refine ⟨5054779634068223980090585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107835298860122111575265813 5054779634068223980090585)
              ·
                refine ⟨3791084725551167985067939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5054779634068223980090585 3791084725551167985067939)
                ·
                  refine ⟨5686627088326751977601909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3791084725551167985067939 5686627088326751977601909)
                  ·
                    refine ⟨533121289530632997900179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5686627088326751977601909 533121289530632997900179)
                    ·
                      rfl

theorem cell22_1557375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 5].length) (baseStart_1557375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557375 prefixEnd_1557375 := by exact prefixLift 1557375
  have htrace : WordTrace (prefixWord ++ tailWord_1557375) baseStart_1557375 baseEnd_1557375 := by
    simpa [prefixWord, tailWord_1557375, baseEnd_1557375] using wordTrace_append hprefix tailTrace_1557375
  have hstable : (prefixWord ++ tailWord_1557375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557375).length < 2 ^ (prefixWord ++ tailWord_1557375).sum := by decide
  have hdescent : baseEnd_1557375 < baseStart_1557375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557394 : List Nat := [3, 2, 3, 2, 2, 1, 2, 1, 6]
def baseStart_1557394 : Nat := 118140960795 + 1557394 * 2 ^ 59
def prefixEnd_1557394 : Nat := 4983230072969 + 3 ^ 40 * 1557394 * 2
def baseEnd_1557394 : Nat := 177709264539641093891707

theorem tailTrace_1557394 : CollatzResearch.WordTrace tailWord_1557394 prefixEnd_1557394 177709264539641093891707 := by
  unfold tailWord_1557394
  simp only [CollatzResearch.WordTrace]
  refine ⟨14200706429958748641105809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37868550479889996376282157 14200706429958748641105809)
  ·
    refine ⟨10650529822469061480829357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14200706429958748641105809 10650529822469061480829357)
    ·
      refine ⟨3993948683425898055311009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10650529822469061480829357 3993948683425898055311009)
      ·
        refine ⟨2995461512569423541483257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3993948683425898055311009 2995461512569423541483257)
        ·
          refine ⟨2246596134427067656112443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2995461512569423541483257 2246596134427067656112443)
          ·
            refine ⟨3369894201640601484168665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2246596134427067656112443 3369894201640601484168665)
            ·
              refine ⟨2527420651230451113126499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3369894201640601484168665 2527420651230451113126499)
              ·
                refine ⟨3791130976845676669689749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2527420651230451113126499 3791130976845676669689749)
                ·
                  refine ⟨177709264539641093891707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3791130976845676669689749 177709264539641093891707)
                  ·
                    rfl

theorem cell22_1557394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_1557394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557394 prefixEnd_1557394 := by exact prefixLift 1557394
  have htrace : WordTrace (prefixWord ++ tailWord_1557394) baseStart_1557394 baseEnd_1557394 := by
    simpa [prefixWord, tailWord_1557394, baseEnd_1557394] using wordTrace_append hprefix tailTrace_1557394
  have hstable : (prefixWord ++ tailWord_1557394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557394).length < 2 ^ (prefixWord ++ tailWord_1557394).sum := by decide
  have hdescent : baseEnd_1557394 < baseStart_1557394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557405 : List Nat := [1, 4, 2, 1, 2, 1, 2, 9]
def baseStart_1557405 : Nat := 118140960795 + 1557405 * 2 ^ 59
def prefixEnd_1557405 : Nat := 4983230072969 + 3 ^ 40 * 1557405 * 2
def baseEnd_1557405 : Nat := 59236839904858102183343

theorem tailTrace_1557405 : CollatzResearch.WordTrace tailWord_1557405 prefixEnd_1557405 59236839904858102183343 := by
  unfold tailWord_1557405
  simp only [CollatzResearch.WordTrace]
  refine ⟨56803226922795143443073669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37868817948530095628715779 56803226922795143443073669)
  ·
    refine ⟨10650605048024089395576313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56803226922795143443073669 10650605048024089395576313)
    ·
      refine ⟨7987953786018067046682235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10650605048024089395576313 7987953786018067046682235)
      ·
        refine ⟨11981930679027100570023353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7987953786018067046682235 11981930679027100570023353)
        ·
          refine ⟨8986448009270325427517515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11981930679027100570023353 8986448009270325427517515)
          ·
            refine ⟨13479672013905488141276273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8986448009270325427517515 13479672013905488141276273)
            ·
              refine ⟨10109754010429116105957205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13479672013905488141276273 10109754010429116105957205)
              ·
                refine ⟨59236839904858102183343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10109754010429116105957205 59236839904858102183343)
                ·
                  rfl

theorem cell22_1557405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 9].length) (baseStart_1557405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557405 prefixEnd_1557405 := by exact prefixLift 1557405
  have htrace : WordTrace (prefixWord ++ tailWord_1557405) baseStart_1557405 baseEnd_1557405 := by
    simpa [prefixWord, tailWord_1557405, baseEnd_1557405] using wordTrace_append hprefix tailTrace_1557405
  have hstable : (prefixWord ++ tailWord_1557405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557405).length < 2 ^ (prefixWord ++ tailWord_1557405).sum := by decide
  have hdescent : baseEnd_1557405 < baseStart_1557405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557409 : List Nat := [1, 2, 3, 4, 1, 3, 1, 1, 1, 5]
def baseStart_1557409 : Nat := 118140960795 + 1557409 * 2 ^ 59
def prefixEnd_1557409 : Nat := 4983230072969 + 3 ^ 40 * 1557409 * 2
def baseEnd_1557409 : Nat := 533132928425468242550075

theorem tailTrace_1557409 : CollatzResearch.WordTrace tailWord_1557409 prefixEnd_1557409 533132928425468242550075 := by
  unfold tailWord_1557409
  simp only [CollatzResearch.WordTrace]
  refine ⟨56803372814780652126219281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37868915209853768084146187 56803372814780652126219281)
  ·
    refine ⟨42602529611085489094664461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56803372814780652126219281 42602529611085489094664461)
    ·
      refine ⟨15975948604157058410499173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42602529611085489094664461 15975948604157058410499173)
      ·
        refine ⟨2995490363279448451968595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15975948604157058410499173 2995490363279448451968595)
        ·
          refine ⟨4493235544919172677952893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2995490363279448451968595 4493235544919172677952893)
          ·
            refine ⟨1684963329344689754232335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4493235544919172677952893 1684963329344689754232335)
            ·
              refine ⟨2527444994017034631348503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1684963329344689754232335 2527444994017034631348503)
              ·
                refine ⟨3791167491025551947022755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2527444994017034631348503 3791167491025551947022755)
                ·
                  refine ⟨5686751236538327920534133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3791167491025551947022755 5686751236538327920534133)
                  ·
                    refine ⟨533132928425468242550075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5686751236538327920534133 533132928425468242550075)
                    ·
                      rfl

theorem cell22_1557409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_1557409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557409 prefixEnd_1557409 := by exact prefixLift 1557409
  have htrace : WordTrace (prefixWord ++ tailWord_1557409) baseStart_1557409 baseEnd_1557409 := by
    simpa [prefixWord, tailWord_1557409, baseEnd_1557409] using wordTrace_append hprefix tailTrace_1557409
  have hstable : (prefixWord ++ tailWord_1557409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557409).length < 2 ^ (prefixWord ++ tailWord_1557409).sum := by decide
  have hdescent : baseEnd_1557409 < baseStart_1557409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557428 : List Nat := [2, 5, 2, 1, 1, 3, 1, 3, 4]
def baseStart_1557428 : Nat := 118140960795 + 1557428 * 2 ^ 59
def prefixEnd_1557428 : Nat := 4983230072969 + 3 ^ 40 * 1557428 * 2
def baseEnd_1557428 : Nat := 177713144171252842108339

theorem tailTrace_1557428 : CollatzResearch.WordTrace tailWord_1557428 prefixEnd_1557428 177713144171252842108339 := by
  unfold tailWord_1557428
  simp only [CollatzResearch.WordTrace]
  refine ⟨28402032900855909185580469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37869377201141212247440625 28402032900855909185580469)
  ·
    refine ⟨2662690584455241486148169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28402032900855909185580469 2662690584455241486148169)
    ·
      refine ⟨1997017938341431114611127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2662690584455241486148169 1997017938341431114611127)
      ·
        refine ⟨2995526907512146671916691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1997017938341431114611127 2995526907512146671916691)
        ·
          refine ⟨4493290361268220007875037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2995526907512146671916691 4493290361268220007875037)
          ·
            refine ⟨1684983885475582502953139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4493290361268220007875037 1684983885475582502953139)
            ·
              refine ⟨2527475828213373754429709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1684983885475582502953139 2527475828213373754429709)
              ·
                refine ⟨947803435580015157911141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2527475828213373754429709 947803435580015157911141)
                ·
                  refine ⟨177713144171252842108339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 947803435580015157911141 177713144171252842108339)
                  ·
                    rfl

theorem cell22_1557428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_1557428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557428 prefixEnd_1557428 := by exact prefixLift 1557428
  have htrace : WordTrace (prefixWord ++ tailWord_1557428) baseStart_1557428 baseEnd_1557428 := by
    simpa [prefixWord, tailWord_1557428, baseEnd_1557428] using wordTrace_append hprefix tailTrace_1557428
  have hstable : (prefixWord ++ tailWord_1557428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557428).length < 2 ^ (prefixWord ++ tailWord_1557428).sum := by decide
  have hdescent : baseEnd_1557428 < baseStart_1557428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557454 : List Nat := [4, 1, 1, 1, 2, 3, 3, 1, 3, 3]
def baseStart_1557454 : Nat := 118140960795 + 1557454 * 2 ^ 59
def prefixEnd_1557454 : Nat := 4983230072969 + 3 ^ 40 * 1557454 * 2
def baseEnd_1557454 : Nat := 533148332845103125174937

theorem tailTrace_1557454 : CollatzResearch.WordTrace tailWord_1557454 prefixEnd_1557454 533148332845103125174937 := by
  unfold tailWord_1557454
  simp only [CollatzResearch.WordTrace]
  refine ⟨7100626762452203101450927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37870009399745083207738277 7100626762452203101450927)
  ·
    refine ⟨10650940143678304652176391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7100626762452203101450927 10650940143678304652176391)
    ·
      refine ⟨15976410215517456978264587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10650940143678304652176391 15976410215517456978264587)
      ·
        refine ⟨23964615323276185467396881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15976410215517456978264587 23964615323276185467396881)
        ·
          refine ⟨17973461492457139100547661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23964615323276185467396881 17973461492457139100547661)
          ·
            refine ⟨6740048059671427162705373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17973461492457139100547661 6740048059671427162705373)
            ·
              refine ⟨2527518022376785186014515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6740048059671427162705373 2527518022376785186014515)
              ·
                refine ⟨3791277033565177779021773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2527518022376785186014515 3791277033565177779021773)
                ·
                  refine ⟨1421728887586941667133165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3791277033565177779021773 1421728887586941667133165)
                  ·
                    refine ⟨533148332845103125174937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1421728887586941667133165 533148332845103125174937)
                    ·
                      rfl

theorem cell22_1557454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_1557454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557454 prefixEnd_1557454 := by exact prefixLift 1557454
  have htrace : WordTrace (prefixWord ++ tailWord_1557454) baseStart_1557454 baseEnd_1557454 := by
    simpa [prefixWord, tailWord_1557454, baseEnd_1557454] using wordTrace_append hprefix tailTrace_1557454
  have hstable : (prefixWord ++ tailWord_1557454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557454).length < 2 ^ (prefixWord ++ tailWord_1557454).sum := by decide
  have hdescent : baseEnd_1557454 < baseStart_1557454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557561 : List Nat := [1, 2, 1, 5, 2, 1, 3, 2, 2, 3]
def baseStart_1557561 : Nat := 118140960795 + 1557561 * 2 ^ 59
def prefixEnd_1557561 : Nat := 4983230072969 + 3 ^ 40 * 1557561 * 2
def baseEnd_1557561 : Nat := 533184961131790512749609

theorem tailTrace_1557561 : CollatzResearch.WordTrace tailWord_1557561 prefixEnd_1557561 533184961131790512749609 := by
  unfold tailWord_1557561
  simp only [CollatzResearch.WordTrace]
  refine ⟨56808916710229982085752537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37872611140153321390501691 56808916710229982085752537)
  ·
    refine ⟨42606687532672486564314403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56808916710229982085752537 42606687532672486564314403)
    ·
      refine ⟨63910031299008729846471605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42606687532672486564314403 63910031299008729846471605)
      ·
        refine ⟨5991565434282068423106713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63910031299008729846471605 5991565434282068423106713)
        ·
          refine ⟨4493674075711551317330035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5991565434282068423106713 4493674075711551317330035)
          ·
            refine ⟨6740511113567326975995053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4493674075711551317330035 6740511113567326975995053)
            ·
              refine ⟨2527691667587747615998145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6740511113567326975995053 2527691667587747615998145)
              ·
                refine ⟨1895768750690810711998609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2527691667587747615998145 1895768750690810711998609)
                ·
                  refine ⟨1421826563018108033998957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1895768750690810711998609 1421826563018108033998957)
                  ·
                    refine ⟨533184961131790512749609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1421826563018108033998957 533184961131790512749609)
                    ·
                      rfl

theorem cell22_1557561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 3].length) (baseStart_1557561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557561 prefixEnd_1557561 := by exact prefixLift 1557561
  have htrace : WordTrace (prefixWord ++ tailWord_1557561) baseStart_1557561 baseEnd_1557561 := by
    simpa [prefixWord, tailWord_1557561, baseEnd_1557561] using wordTrace_append hprefix tailTrace_1557561
  have hstable : (prefixWord ++ tailWord_1557561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557561).length < 2 ^ (prefixWord ++ tailWord_1557561).sum := by decide
  have hdescent : baseEnd_1557561 < baseStart_1557561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557589 : List Nat := [1, 3, 2, 2, 1, 2, 1, 4, 3, 3]
def baseStart_1557589 : Nat := 118140960795 + 1557589 * 2 ^ 59
def prefixEnd_1557589 : Nat := 4983230072969 + 3 ^ 40 * 1557589 * 2
def baseEnd_1557589 : Nat := 533194546104007773049523

theorem tailTrace_1557589 : CollatzResearch.WordTrace tailWord_1557589 prefixEnd_1557589 533194546104007773049523 := by
  unfold tailWord_1557589
  simp only [CollatzResearch.WordTrace]
  refine ⟨56809937954128542867771821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37873291969419028578514547 56809937954128542867771821)
  ·
    refine ⟨21303726732798203575414433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56809937954128542867771821 21303726732798203575414433)
    ·
      refine ⟨15977795049598652681560825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21303726732798203575414433 15977795049598652681560825)
      ·
        refine ⟨11983346287198989511170619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15977795049598652681560825 11983346287198989511170619)
        ·
          refine ⟨17975019430798484266755929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11983346287198989511170619 17975019430798484266755929)
          ·
            refine ⟨13481264573098863200066947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17975019430798484266755929 13481264573098863200066947)
            ·
              refine ⟨20221896859648294800100421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13481264573098863200066947 20221896859648294800100421)
              ·
                refine ⟨3791605661184055275018829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20221896859648294800100421 3791605661184055275018829)
                ·
                  refine ⟨1421852122944020728132061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3791605661184055275018829 1421852122944020728132061)
                  ·
                    refine ⟨533194546104007773049523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1421852122944020728132061 533194546104007773049523)
                    ·
                      rfl

theorem cell22_1557589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_1557589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557589 prefixEnd_1557589 := by exact prefixLift 1557589
  have htrace : WordTrace (prefixWord ++ tailWord_1557589) baseStart_1557589 baseEnd_1557589 := by
    simpa [prefixWord, tailWord_1557589, baseEnd_1557589] using wordTrace_append hprefix tailTrace_1557589
  have hstable : (prefixWord ++ tailWord_1557589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557589).length < 2 ^ (prefixWord ++ tailWord_1557589).sum := by decide
  have hdescent : baseEnd_1557589 < baseStart_1557589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557617 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 2, 5]
def baseStart_1557617 : Nat := 118140960795 + 1557617 * 2 ^ 59
def prefixEnd_1557617 : Nat := 4983230072969 + 3 ^ 40 * 1557617 * 2
def baseEnd_1557617 : Nat := 533204131076225033349437

theorem tailTrace_1557617 : CollatzResearch.WordTrace tailWord_1557617 prefixEnd_1557617 533204131076225033349437 := by
  unfold tailWord_1557617
  simp only [CollatzResearch.WordTrace]
  refine ⟨56810959198027103649791105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37873972798684735766527403 56810959198027103649791105)
  ·
    refine ⟨42608219398520327737343329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56810959198027103649791105 42608219398520327737343329)
    ·
      refine ⟨31956164548890245803007497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42608219398520327737343329 31956164548890245803007497)
      ·
        refine ⟨23967123411667684352255623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31956164548890245803007497 23967123411667684352255623)
        ·
          refine ⟨35950685117501526528383435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23967123411667684352255623 35950685117501526528383435)
          ·
            refine ⟨53926027676252289792575153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35950685117501526528383435 53926027676252289792575153)
            ·
              refine ⟨40444520757189217344431365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53926027676252289792575153 40444520757189217344431365)
              ·
                refine ⟨7583347641972978252080881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40444520757189217344431365 7583347641972978252080881)
                ·
                  refine ⟨5687510731479733689060661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7583347641972978252080881 5687510731479733689060661)
                  ·
                    refine ⟨533204131076225033349437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5687510731479733689060661 533204131076225033349437)
                    ·
                      rfl

theorem cell22_1557617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_1557617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557617 prefixEnd_1557617 := by exact prefixLift 1557617
  have htrace : WordTrace (prefixWord ++ tailWord_1557617) baseStart_1557617 baseEnd_1557617 := by
    simpa [prefixWord, tailWord_1557617, baseEnd_1557617] using wordTrace_append hprefix tailTrace_1557617
  have hstable : (prefixWord ++ tailWord_1557617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557617).length < 2 ^ (prefixWord ++ tailWord_1557617).sum := by decide
  have hdescent : baseEnd_1557617 < baseStart_1557617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557623 : List Nat := [1, 1, 3, 1, 1, 4, 5, 2, 1, 3]
def baseStart_1557623 : Nat := 118140960795 + 1557623 * 2 ^ 59
def prefixEnd_1557623 : Nat := 4983230072969 + 3 ^ 40 * 1557623 * 2
def baseEnd_1557623 : Nat := 533206184998843017699419

theorem tailTrace_1557623 : CollatzResearch.WordTrace tailWord_1557623 prefixEnd_1557623 533206184998843017699419 := by
  unfold tailWord_1557623
  simp only [CollatzResearch.WordTrace]
  refine ⟨56811178036005366674509523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37874118690670244449673015 56811178036005366674509523)
  ·
    refine ⟨85216767054008050011764285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56811178036005366674509523 85216767054008050011764285)
    ·
      refine ⟨31956287645253018754411607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85216767054008050011764285 31956287645253018754411607)
      ·
        refine ⟨47934431467879528131617411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31956287645253018754411607 47934431467879528131617411)
        ·
          refine ⟨71901647201819292197426117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47934431467879528131617411 71901647201819292197426117)
          ·
            refine ⟨13481558850341117287017397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71901647201819292197426117 13481558850341117287017397)
            ·
              refine ⟨1263896142219479745657881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13481558850341117287017397 1263896142219479745657881)
              ·
                refine ⟨947922106664609809243411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1263896142219479745657881 947922106664609809243411)
                ·
                  refine ⟨1421883159996914713865117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947922106664609809243411 1421883159996914713865117)
                  ·
                    refine ⟨533206184998843017699419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1421883159996914713865117 533206184998843017699419)
                    ·
                      rfl

theorem cell22_1557623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 1, 3].length) (baseStart_1557623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557623 prefixEnd_1557623 := by exact prefixLift 1557623
  have htrace : WordTrace (prefixWord ++ tailWord_1557623) baseStart_1557623 baseEnd_1557623 := by
    simpa [prefixWord, tailWord_1557623, baseEnd_1557623] using wordTrace_append hprefix tailTrace_1557623
  have hstable : (prefixWord ++ tailWord_1557623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557623).length < 2 ^ (prefixWord ++ tailWord_1557623).sum := by decide
  have hdescent : baseEnd_1557623 < baseStart_1557623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557636 : List Nat := [2, 3, 2, 1, 2, 2, 4, 1, 5]
def baseStart_1557636 : Nat := 118140960795 + 1557636 * 2 ^ 59
def prefixEnd_1557636 : Nat := 4983230072969 + 3 ^ 40 * 1557636 * 2
def baseEnd_1557636 : Nat := 177736878388171772374793

theorem tailTrace_1557636 : CollatzResearch.WordTrace tailWord_1557636 prefixEnd_1557636 177736878388171772374793 := by
  unfold tailWord_1557636
  simp only [CollatzResearch.WordTrace]
  refine ⟨28405826092479134947366381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37874434789972179929821841 28405826092479134947366381)
  ·
    refine ⟨10652184784679675605262393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28405826092479134947366381 10652184784679675605262393)
    ·
      refine ⟨7989138588509756703946795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10652184784679675605262393 7989138588509756703946795)
      ·
        refine ⟨11983707882764635055920193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7989138588509756703946795 11983707882764635055920193)
        ·
          refine ⟨8987780912073476291940145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11983707882764635055920193 8987780912073476291940145)
          ·
            refine ⟨6740835684055107218955109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8987780912073476291940145 6740835684055107218955109)
            ·
              refine ⟨1263906690760332603554083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6740835684055107218955109 1263906690760332603554083)
              ·
                refine ⟨1895860036140498905331125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1263906690760332603554083 1895860036140498905331125)
                ·
                  refine ⟨177736878388171772374793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1895860036140498905331125 177736878388171772374793)
                  ·
                    rfl

theorem cell22_1557636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_1557636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557636 prefixEnd_1557636 := by exact prefixLift 1557636
  have htrace : WordTrace (prefixWord ++ tailWord_1557636) baseStart_1557636 baseEnd_1557636 := by
    simpa [prefixWord, tailWord_1557636, baseEnd_1557636] using wordTrace_append hprefix tailTrace_1557636
  have hstable : (prefixWord ++ tailWord_1557636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557636).length < 2 ^ (prefixWord ++ tailWord_1557636).sum := by decide
  have hdescent : baseEnd_1557636 < baseStart_1557636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557679 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 4, 3]
def baseStart_1557679 : Nat := 118140960795 + 1557679 * 2 ^ 59
def prefixEnd_1557679 : Nat := 4983230072969 + 3 ^ 40 * 1557679 * 2
def baseEnd_1557679 : Nat := 533225354943277538299247

theorem tailTrace_1557679 : CollatzResearch.WordTrace tailWord_1557679 prefixEnd_1557679 533225354943277538299247 := by
  unfold tailWord_1557679
  simp only [CollatzResearch.WordTrace]
  refine ⟨56813220523802488238548091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37875480349201658825698727 56813220523802488238548091)
  ·
    refine ⟨85219830785703732357822137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56813220523802488238548091 85219830785703732357822137)
    ·
      refine ⟨63914873089277799268366603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85219830785703732357822137 63914873089277799268366603)
      ·
        refine ⟨95872309633916698902549905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63914873089277799268366603 95872309633916698902549905)
        ·
          refine ⟨71904232225437524176912429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95872309633916698902549905 71904232225437524176912429)
          ·
            refine ⟨26964087084539071566342161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71904232225437524176912429 26964087084539071566342161)
            ·
              refine ⟨20223065313404303674756621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26964087084539071566342161 20223065313404303674756621)
              ·
                refine ⟨7583649492526613878033733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20223065313404303674756621 7583649492526613878033733)
                ·
                  refine ⟨1421934279848740102131325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7583649492526613878033733 1421934279848740102131325)
                  ·
                    refine ⟨533225354943277538299247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1421934279848740102131325 533225354943277538299247)
                    ·
                      rfl

theorem cell22_1557679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 3].length) (baseStart_1557679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557679 prefixEnd_1557679 := by exact prefixLift 1557679
  have htrace : WordTrace (prefixWord ++ tailWord_1557679) baseStart_1557679 baseEnd_1557679 := by
    simpa [prefixWord, tailWord_1557679, baseEnd_1557679] using wordTrace_append hprefix tailTrace_1557679
  have hstable : (prefixWord ++ tailWord_1557679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557679).length < 2 ^ (prefixWord ++ tailWord_1557679).sum := by decide
  have hdescent : baseEnd_1557679 < baseStart_1557679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557696 : List Nat := [2, 1, 1, 2, 6, 1, 2, 1, 1, 5]
def baseStart_1557696 : Nat := 118140960795 + 1557696 * 2 ^ 59
def prefixEnd_1557696 : Nat := 4983230072969 + 3 ^ 40 * 1557696 * 2
def baseEnd_1557696 : Nat := 533231174390695160624195

theorem tailTrace_1557696 : CollatzResearch.WordTrace tailWord_1557696 prefixEnd_1557696 533231174390695160624195 := by
  unfold tailWord_1557696
  simp only [CollatzResearch.WordTrace]
  refine ⟨28406920282370450070958471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37875893709827266761277961 28406920282370450070958471)
  ·
    refine ⟨42610380423555675106437707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28406920282370450070958471 42610380423555675106437707)
    ·
      refine ⟨63915570635333512659656561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42610380423555675106437707 63915570635333512659656561)
      ·
        refine ⟨47936677976500134494742421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63915570635333512659656561 47936677976500134494742421)
        ·
          refine ⟨2247031780148443804441051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47936677976500134494742421 2247031780148443804441051)
          ·
            refine ⟨3370547670222665706661577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247031780148443804441051 3370547670222665706661577)
            ·
              refine ⟨2527910752666999279996183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3370547670222665706661577 2527910752666999279996183)
              ·
                refine ⟨3791866129000498919994275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2527910752666999279996183 3791866129000498919994275)
                ·
                  refine ⟨5687799193500748379991413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3791866129000498919994275 5687799193500748379991413)
                  ·
                    refine ⟨533231174390695160624195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5687799193500748379991413 533231174390695160624195)
                    ·
                      rfl

theorem cell22_1557696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 1, 5].length) (baseStart_1557696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557696 prefixEnd_1557696 := by exact prefixLift 1557696
  have htrace : WordTrace (prefixWord ++ tailWord_1557696) baseStart_1557696 baseEnd_1557696 := by
    simpa [prefixWord, tailWord_1557696, baseEnd_1557696] using wordTrace_append hprefix tailTrace_1557696
  have hstable : (prefixWord ++ tailWord_1557696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557696).length < 2 ^ (prefixWord ++ tailWord_1557696).sum := by decide
  have hdescent : baseEnd_1557696 < baseStart_1557696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557707 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 1, 9]
def baseStart_1557707 : Nat := 118140960795 + 1557707 * 2 ^ 59
def prefixEnd_1557707 : Nat := 4983230072969 + 3 ^ 40 * 1557707 * 2
def baseEnd_1557707 : Nat := 533234939915494798599161

theorem tailTrace_1557707 : CollatzResearch.WordTrace tailWord_1557707 prefixEnd_1557707 533234939915494798599161 := by
  unfold tailWord_1557707
  simp only [CollatzResearch.WordTrace]
  refine ⟨56814241767701049020567375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37876161178467366013711583 56814241767701049020567375)
  ·
    refine ⟨85221362651551573530851063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56814241767701049020567375 85221362651551573530851063)
    ·
      refine ⟨127832043977327360296276595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85221362651551573530851063 127832043977327360296276595)
      ·
        refine ⟨191748065965991040444414893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127832043977327360296276595 191748065965991040444414893)
        ·
          refine ⟨71905524737246640166655585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191748065965991040444414893 71905524737246640166655585)
          ·
            refine ⟨53929143552934980124991689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71905524737246640166655585 53929143552934980124991689)
            ·
              refine ⟨40446857664701235093743767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53929143552934980124991689 40446857664701235093743767)
              ·
                refine ⟨60670286497051852640615651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40446857664701235093743767 60670286497051852640615651)
                ·
                  refine ⟨91005429745577778960923477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60670286497051852640615651 91005429745577778960923477)
                  ·
                    refine ⟨533234939915494798599161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 91005429745577778960923477 533234939915494798599161)
                    ·
                      rfl

theorem cell22_1557707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 9].length) (baseStart_1557707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557707 prefixEnd_1557707 := by exact prefixLift 1557707
  have htrace : WordTrace (prefixWord ++ tailWord_1557707) baseStart_1557707 baseEnd_1557707 := by
    simpa [prefixWord, tailWord_1557707, baseEnd_1557707] using wordTrace_append hprefix tailTrace_1557707
  have hstable : (prefixWord ++ tailWord_1557707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557707).length < 2 ^ (prefixWord ++ tailWord_1557707).sum := by decide
  have hdescent : baseEnd_1557707 < baseStart_1557707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557758 : List Nat := [4, 2, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_1557758 : Nat := 118140960795 + 1557758 * 2 ^ 59
def prefixEnd_1557758 : Nat := 4983230072969 + 3 ^ 40 * 1557758 * 2
def baseEnd_1557758 : Nat := 533252398257747665574005

theorem tailTrace_1557758 : CollatzResearch.WordTrace tailWord_1557758 prefixEnd_1557758 533252398257747665574005 := by
  unfold tailWord_1557758
  simp only [CollatzResearch.WordTrace]
  refine ⟨7102012736314535591334241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37877401260344189820449285 7102012736314535591334241)
  ·
    refine ⟨5326509552235901693500681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7102012736314535591334241 5326509552235901693500681)
    ·
      refine ⟨3994882164176926270125511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5326509552235901693500681 3994882164176926270125511)
      ·
        refine ⟨5992323246265389405188267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3994882164176926270125511 5992323246265389405188267)
        ·
          refine ⟨8988484869398084107782401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5992323246265389405188267 8988484869398084107782401)
          ·
            refine ⟨6741363652048563080836801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8988484869398084107782401 6741363652048563080836801)
            ·
              refine ⟨5056022739036422310627601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6741363652048563080836801 5056022739036422310627601)
              ·
                refine ⟨3792017054277316732970701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5056022739036422310627601 3792017054277316732970701)
                ·
                  refine ⟨1422006395353993774864013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3792017054277316732970701 1422006395353993774864013)
                  ·
                    refine ⟨533252398257747665574005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1422006395353993774864013 533252398257747665574005)
                    ·
                      rfl

theorem cell22_1557758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_1557758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557758 prefixEnd_1557758 := by exact prefixLift 1557758
  have htrace : WordTrace (prefixWord ++ tailWord_1557758) baseStart_1557758 baseEnd_1557758 := by
    simpa [prefixWord, tailWord_1557758, baseEnd_1557758] using wordTrace_append hprefix tailTrace_1557758
  have hstable : (prefixWord ++ tailWord_1557758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557758).length < 2 ^ (prefixWord ++ tailWord_1557758).sum := by decide
  have hdescent : baseEnd_1557758 < baseStart_1557758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557792 : List Nat := [2, 1, 1, 5, 3, 1, 3, 2, 1, 3]
def baseStart_1557792 : Nat := 118140960795 + 1557792 * 2 ^ 59
def prefixEnd_1557792 : Nat := 4983230072969 + 3 ^ 40 * 1557792 * 2
def baseEnd_1557792 : Nat := 533264037152582910223901

theorem tailTrace_1557792 : CollatzResearch.WordTrace tailWord_1557792 prefixEnd_1557792 533264037152582910223901 := by
  unfold tailWord_1557792
  simp only [CollatzResearch.WordTrace]
  refine ⟨28408670986196554268705815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37878227981595405691607753 28408670986196554268705815)
  ·
    refine ⟨42613006479294831403058723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28408670986196554268705815 42613006479294831403058723)
    ·
      refine ⟨63919509718942247104588085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42613006479294831403058723 63919509718942247104588085)
      ·
        refine ⟨5992454036150835666055133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63919509718942247104588085 5992454036150835666055133)
        ·
          refine ⟨2247170263556563374770675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5992454036150835666055133 2247170263556563374770675)
          ·
            refine ⟨3370755395334845062156013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247170263556563374770675 3370755395334845062156013)
            ·
              refine ⟨1264033273250566898308505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3370755395334845062156013 1264033273250566898308505)
              ·
                refine ⟨948024954937925173731379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1264033273250566898308505 948024954937925173731379)
                ·
                  refine ⟨1422037432406887760597069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 948024954937925173731379 1422037432406887760597069)
                  ·
                    refine ⟨533264037152582910223901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1422037432406887760597069 533264037152582910223901)
                    ·
                      rfl

theorem cell22_1557792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 1, 3].length) (baseStart_1557792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557792 prefixEnd_1557792 := by exact prefixLift 1557792
  have htrace : WordTrace (prefixWord ++ tailWord_1557792) baseStart_1557792 baseEnd_1557792 := by
    simpa [prefixWord, tailWord_1557792, baseEnd_1557792] using wordTrace_append hprefix tailTrace_1557792
  have hstable : (prefixWord ++ tailWord_1557792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557792).length < 2 ^ (prefixWord ++ tailWord_1557792).sum := by decide
  have hdescent : baseEnd_1557792 < baseStart_1557792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557805 : List Nat := [1, 5, 3, 1, 1, 1, 4, 1, 5]
def baseStart_1557805 : Nat := 118140960795 + 1557805 * 2 ^ 59
def prefixEnd_1557805 : Nat := 4983230072969 + 3 ^ 40 * 1557805 * 2
def baseEnd_1557805 : Nat := 177756162439418403216287

theorem tailTrace_1557805 : CollatzResearch.WordTrace tailWord_1557805 prefixEnd_1557805 177756162439418403216287 := by
  unfold tailWord_1557805
  simp only [CollatzResearch.WordTrace]
  refine ⟨56817816121346011757634869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37878544080897341171756579 56817816121346011757634869)
  ·
    refine ⟨5326670261376188602278269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56817816121346011757634869 5326670261376188602278269)
    ·
      refine ⟨1997501348016070725854351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5326670261376188602278269 1997501348016070725854351)
      ·
        refine ⟨2996252022024106088781527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1997501348016070725854351 2996252022024106088781527)
        ·
          refine ⟨4494378033036159133172291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2996252022024106088781527 4494378033036159133172291)
          ·
            refine ⟨6741567049554238699758437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4494378033036159133172291 6741567049554238699758437)
            ·
              refine ⟨1264043821791419756204707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6741567049554238699758437 1264043821791419756204707)
              ·
                refine ⟨1896065732687129634307061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1264043821791419756204707 1896065732687129634307061)
                ·
                  refine ⟨177756162439418403216287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1896065732687129634307061 177756162439418403216287)
                  ·
                    rfl

theorem cell22_1557805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_1557805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557805 prefixEnd_1557805 := by exact prefixLift 1557805
  have htrace : WordTrace (prefixWord ++ tailWord_1557805) baseStart_1557805 baseEnd_1557805 := by
    simpa [prefixWord, tailWord_1557805, baseEnd_1557805] using wordTrace_append hprefix tailTrace_1557805
  have hstable : (prefixWord ++ tailWord_1557805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557805).length < 2 ^ (prefixWord ++ tailWord_1557805).sum := by decide
  have hdescent : baseEnd_1557805 < baseStart_1557805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557829 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 1, 6]
def baseStart_1557829 : Nat := 118140960795 + 1557829 * 2 ^ 59
def prefixEnd_1557829 : Nat := 4983230072969 + 3 ^ 40 * 1557829 * 2
def baseEnd_1557829 : Nat := 533276703008727147048787

theorem tailTrace_1557829 : CollatzResearch.WordTrace tailWord_1557829 prefixEnd_1557829 533276703008727147048787 := by
  unfold tailWord_1557829
  simp only [CollatzResearch.WordTrace]
  refine ⟨56818691473259063856508541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37879127648839375904339027 56818691473259063856508541)
  ·
    refine ⟨21307009302472148946190703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56818691473259063856508541 21307009302472148946190703)
    ·
      refine ⟨31960513953708223419286055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21307009302472148946190703 31960513953708223419286055)
      ·
        refine ⟨47940770930562335128929083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31960513953708223419286055 47940770930562335128929083)
        ·
          refine ⟨71911156395843502693393625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47940770930562335128929083 71911156395843502693393625)
          ·
            refine ⟨53933367296882627020045219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71911156395843502693393625 53933367296882627020045219)
            ·
              refine ⟨80900050945323940530067829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53933367296882627020045219 80900050945323940530067829)
              ·
                refine ⟨7584379776124119424693859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80900050945323940530067829 7584379776124119424693859)
                ·
                  refine ⟨11376569664186179137040789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7584379776124119424693859 11376569664186179137040789)
                  ·
                    refine ⟨533276703008727147048787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11376569664186179137040789 533276703008727147048787)
                    ·
                      rfl

theorem cell22_1557829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_1557829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557829 prefixEnd_1557829 := by exact prefixLift 1557829
  have htrace : WordTrace (prefixWord ++ tailWord_1557829) baseStart_1557829 baseEnd_1557829 := by
    simpa [prefixWord, tailWord_1557829, baseEnd_1557829] using wordTrace_append hprefix tailTrace_1557829
  have hstable : (prefixWord ++ tailWord_1557829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557829).length < 2 ^ (prefixWord ++ tailWord_1557829).sum := by decide
  have hdescent : baseEnd_1557829 < baseStart_1557829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557831 : List Nat := [1, 1, 4, 1, 2, 4, 1, 2, 1, 5]
def baseStart_1557831 : Nat := 118140960795 + 1557831 * 2 ^ 59
def prefixEnd_1557831 : Nat := 4983230072969 + 3 ^ 40 * 1557831 * 2
def baseEnd_1557831 : Nat := 533277387649599808498781

theorem tailTrace_1557831 : CollatzResearch.WordTrace tailWord_1557831 prefixEnd_1557831 533277387649599808498781 := by
  unfold tailWord_1557831
  simp only [CollatzResearch.WordTrace]
  refine ⟨56818764419251818198081347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37879176279501212132054231 56818764419251818198081347)
  ·
    refine ⟨85228146628877727297122021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56818764419251818198081347 85228146628877727297122021)
    ·
      refine ⟨15980277492914573868210379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85228146628877727297122021 15980277492914573868210379)
      ·
        refine ⟨23970416239371860802315569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15980277492914573868210379 23970416239371860802315569)
        ·
          refine ⟨17977812179528895601736677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23970416239371860802315569 17977812179528895601736677)
          ·
            refine ⟨3370839783661667925325627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17977812179528895601736677 3370839783661667925325627)
            ·
              refine ⟨5056259675492501887988441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3370839783661667925325627 5056259675492501887988441)
              ·
                refine ⟨3792194756619376415991331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5056259675492501887988441 3792194756619376415991331)
                ·
                  refine ⟨5688292134929064623986997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3792194756619376415991331 5688292134929064623986997)
                  ·
                    refine ⟨533277387649599808498781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5688292134929064623986997 533277387649599808498781)
                    ·
                      rfl

theorem cell22_1557831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_1557831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557831 prefixEnd_1557831 := by exact prefixLift 1557831
  have htrace : WordTrace (prefixWord ++ tailWord_1557831) baseStart_1557831 baseEnd_1557831 := by
    simpa [prefixWord, tailWord_1557831, baseEnd_1557831] using wordTrace_append hprefix tailTrace_1557831
  have hstable : (prefixWord ++ tailWord_1557831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557831).length < 2 ^ (prefixWord ++ tailWord_1557831).sum := by decide
  have hdescent : baseEnd_1557831 < baseStart_1557831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557848 : List Nat := [2, 1, 2, 2, 1, 1, 6, 2, 2, 3]
def baseStart_1557848 : Nat := 118140960795 + 1557848 * 2 ^ 59
def prefixEnd_1557848 : Nat := 4983230072969 + 3 ^ 40 * 1557848 * 2
def baseEnd_1557848 : Nat := 533283207097017430823729

theorem tailTrace_1557848 : CollatzResearch.WordTrace tailWord_1557848 prefixEnd_1557848 533283207097017430823729 := by
  unfold tailWord_1557848
  simp only [CollatzResearch.WordTrace]
  refine ⟨28409692230095115050725099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37879589640126820067633465 28409692230095115050725099)
  ·
    refine ⟨42614538345142672576087649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28409692230095115050725099 42614538345142672576087649)
    ·
      refine ⟨31960903758857004432065737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42614538345142672576087649 31960903758857004432065737)
      ·
        refine ⟨23970677819142753324049303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31960903758857004432065737 23970677819142753324049303)
        ·
          refine ⟨35956016728714129986073955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23970677819142753324049303 35956016728714129986073955)
          ·
            refine ⟨53934025093071194979110933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35956016728714129986073955 53934025093071194979110933)
            ·
              refine ⟨2528157426237712264645825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53934025093071194979110933 2528157426237712264645825)
              ·
                refine ⟨1896118069678284198484369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2528157426237712264645825 1896118069678284198484369)
                ·
                  refine ⟨1422088552258713148863277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1896118069678284198484369 1422088552258713148863277)
                  ·
                    refine ⟨533283207097017430823729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1422088552258713148863277 533283207097017430823729)
                    ·
                      rfl

theorem cell22_1557848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_1557848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557848 prefixEnd_1557848 := by exact prefixLift 1557848
  have htrace : WordTrace (prefixWord ++ tailWord_1557848) baseStart_1557848 baseEnd_1557848 := by
    simpa [prefixWord, tailWord_1557848, baseEnd_1557848] using wordTrace_append hprefix tailTrace_1557848
  have hstable : (prefixWord ++ tailWord_1557848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557848).length < 2 ^ (prefixWord ++ tailWord_1557848).sum := by decide
  have hdescent : baseEnd_1557848 < baseStart_1557848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557886 : List Nat := [4, 2, 3, 2, 2, 1, 2, 1, 1, 4]
def baseStart_1557886 : Nat := 118140960795 + 1557886 * 2 ^ 59
def prefixEnd_1557886 : Nat := 4983230072969 + 3 ^ 40 * 1557886 * 2
def baseEnd_1557886 : Nat := 533296215273597998373613

theorem tailTrace_1557886 : CollatzResearch.WordTrace tailWord_1557886 prefixEnd_1557886 533296215273597998373613 := by
  unfold tailWord_1557886
  simp only [CollatzResearch.WordTrace]
  refine ⟨7102596304256570323916689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37880513622701708394222341 7102596304256570323916689)
  ·
    refine ⟨5326947228192427742937517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7102596304256570323916689 5326947228192427742937517)
    ·
      refine ⟨1997605210572160403601569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5326947228192427742937517 1997605210572160403601569)
      ·
        refine ⟨1498203907929120302701177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1997605210572160403601569 1498203907929120302701177)
        ·
          refine ⟨1123652930946840227025883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1498203907929120302701177 1123652930946840227025883)
          ·
            refine ⟨1685479396420260340538825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123652930946840227025883 1685479396420260340538825)
            ·
              refine ⟨1264109547315195255404119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1685479396420260340538825 1264109547315195255404119)
              ·
                refine ⟨1896164320972792883106179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1264109547315195255404119 1896164320972792883106179)
                ·
                  refine ⟨2844246481459189324659269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1896164320972792883106179 2844246481459189324659269)
                  ·
                    refine ⟨533296215273597998373613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2844246481459189324659269 533296215273597998373613)
                    ·
                      rfl

theorem cell22_1557886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_1557886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557886 prefixEnd_1557886 := by exact prefixLift 1557886
  have htrace : WordTrace (prefixWord ++ tailWord_1557886) baseStart_1557886 baseEnd_1557886 := by
    simpa [prefixWord, tailWord_1557886, baseEnd_1557886] using wordTrace_append hprefix tailTrace_1557886
  have hstable : (prefixWord ++ tailWord_1557886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557886).length < 2 ^ (prefixWord ++ tailWord_1557886).sum := by decide
  have hdescent : baseEnd_1557886 < baseStart_1557886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557923 : List Nat := [1, 1, 1, 4, 1, 3, 5, 1, 5]
def baseStart_1557923 : Nat := 118140960795 + 1557923 * 2 ^ 59
def prefixEnd_1557923 : Nat := 4983230072969 + 3 ^ 40 * 1557923 * 2
def baseEnd_1557923 : Nat := 177769627043247411732833

theorem tailTrace_1557923 : CollatzResearch.WordTrace tailWord_1557923 prefixEnd_1557923 177769627043247411732833 := by
  unfold tailWord_1557923
  simp only [CollatzResearch.WordTrace]
  refine ⟨56822119934918517910430423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37881413289945678606953615 56822119934918517910430423)
  ·
    refine ⟨85233179902377776865645635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56822119934918517910430423 85233179902377776865645635)
    ·
      refine ⟨127849769853566665298468453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85233179902377776865645635 127849769853566665298468453)
      ·
        refine ⟨23971831847543749743462835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127849769853566665298468453 23971831847543749743462835)
        ·
          refine ⟨35957747771315624615194253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23971831847543749743462835 35957747771315624615194253)
          ·
            refine ⟨13484155414243359230697845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35957747771315624615194253 13484155414243359230697845)
            ·
              refine ⟨1264139570085314927877923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13484155414243359230697845 1264139570085314927877923)
              ·
                refine ⟨1896209355127972391816885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1264139570085314927877923 1896209355127972391816885)
                ·
                  refine ⟨177769627043247411732833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1896209355127972391816885 177769627043247411732833)
                  ·
                    rfl

theorem cell22_1557923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 5].length) (baseStart_1557923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1557923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1557923 prefixEnd_1557923 := by exact prefixLift 1557923
  have htrace : WordTrace (prefixWord ++ tailWord_1557923) baseStart_1557923 baseEnd_1557923 := by
    simpa [prefixWord, tailWord_1557923, baseEnd_1557923] using wordTrace_append hprefix tailTrace_1557923
  have hstable : (prefixWord ++ tailWord_1557923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557923).length < 2 ^ (prefixWord ++ tailWord_1557923).sum := by decide
  have hdescent : baseEnd_1557923 < baseStart_1557923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558017 : List Nat := [1, 2, 4, 1, 4, 1, 2, 2, 2, 3]
def baseStart_1558017 : Nat := 118140960795 + 1558017 * 2 ^ 59
def prefixEnd_1558017 : Nat := 4983230072969 + 3 ^ 40 * 1558017 * 2
def baseEnd_1558017 : Nat := 533341059250757323348211

theorem tailTrace_1558017 : CollatzResearch.WordTrace tailWord_1558017 prefixEnd_1558017 533341059250757323348211 := by
  unfold tailWord_1558017
  simp only [CollatzResearch.WordTrace]
  refine ⟨56825548396577971964352305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37883698931051981309568203 56825548396577971964352305)
  ·
    refine ⟨42619161297433478973264229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56825548396577971964352305 42619161297433478973264229)
    ·
      refine ⟨7991092743268777307487043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42619161297433478973264229 7991092743268777307487043)
      ·
        refine ⟨11986639114903165961230565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7991092743268777307487043 11986639114903165961230565)
        ·
          refine ⟨2247494834044343617730731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11986639114903165961230565 2247494834044343617730731)
          ·
            refine ⟨3371242251066515426596097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247494834044343617730731 3371242251066515426596097)
            ·
              refine ⟨2528431688299886569947073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3371242251066515426596097 2528431688299886569947073)
              ·
                refine ⟨1896323766224914927460305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2528431688299886569947073 1896323766224914927460305)
                ·
                  refine ⟨1422242824668686195595229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1896323766224914927460305 1422242824668686195595229)
                  ·
                    refine ⟨533341059250757323348211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1422242824668686195595229 533341059250757323348211)
                    ·
                      rfl

theorem cell22_1558017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_1558017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558017 prefixEnd_1558017 := by exact prefixLift 1558017
  have htrace : WordTrace (prefixWord ++ tailWord_1558017) baseStart_1558017 baseEnd_1558017 := by
    simpa [prefixWord, tailWord_1558017, baseEnd_1558017] using wordTrace_append hprefix tailTrace_1558017
  have hstable : (prefixWord ++ tailWord_1558017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558017).length < 2 ^ (prefixWord ++ tailWord_1558017).sum := by decide
  have hdescent : baseEnd_1558017 < baseStart_1558017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558030 : List Nat := [4, 1, 1, 2, 4, 2, 1, 7]
def baseStart_1558030 : Nat := 118140960795 + 1558030 * 2 ^ 59
def prefixEnd_1558030 : Nat := 4983230072969 + 3 ^ 40 * 1558030 * 2
def baseEnd_1558030 : Nat := 59260612157381069197019

theorem tailTrace_1558030 : CollatzResearch.WordTrace tailWord_1558030 prefixEnd_1558030 59260612157381069197019 := by
  unfold tailWord_1558030
  simp only [CollatzResearch.WordTrace]
  refine ⟨7103252818191359398071943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37884015030353916789717029 7103252818191359398071943)
  ·
    refine ⟨10654879227287039097107915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7103252818191359398071943 10654879227287039097107915)
    ·
      refine ⟨15982318840930558645661873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10654879227287039097107915 15982318840930558645661873)
      ·
        refine ⟨11986739130697918984246405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15982318840930558645661873 11986739130697918984246405)
        ·
          refine ⟨2247513587005859809546201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11986739130697918984246405 2247513587005859809546201)
          ·
            refine ⟨1685635190254394857159651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2247513587005859809546201 1685635190254394857159651)
            ·
              refine ⟨2528452785381592285739477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1685635190254394857159651 2528452785381592285739477)
              ·
                refine ⟨59260612157381069197019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2528452785381592285739477 59260612157381069197019)
                ·
                  rfl

theorem cell22_1558030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_1558030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558030 prefixEnd_1558030 := by exact prefixLift 1558030
  have htrace : WordTrace (prefixWord ++ tailWord_1558030) baseStart_1558030 baseEnd_1558030 := by
    simpa [prefixWord, tailWord_1558030, baseEnd_1558030] using wordTrace_append hprefix tailTrace_1558030
  have hstable : (prefixWord ++ tailWord_1558030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558030).length < 2 ^ (prefixWord ++ tailWord_1558030).sum := by decide
  have hdescent : baseEnd_1558030 < baseStart_1558030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558045 : List Nat := [1, 4, 2, 2, 1, 1, 3, 2, 3, 3]
def baseStart_1558045 : Nat := 118140960795 + 1558045 * 2 ^ 59
def prefixEnd_1558045 : Nat := 4983230072969 + 3 ^ 40 * 1558045 * 2
def baseEnd_1558045 : Nat := 533350644222974583648125

theorem tailTrace_1558045 : CollatzResearch.WordTrace tailWord_1558045 prefixEnd_1558045 533350644222974583648125 := by
  unfold tailWord_1558045
  simp only [CollatzResearch.WordTrace]
  refine ⟨56826569640476532746371589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37884379760317688497581059 56826569640476532746371589)
  ·
    refine ⟨10654981807589349889944673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56826569640476532746371589 10654981807589349889944673)
    ·
      refine ⟨7991236355692012417458505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10654981807589349889944673 7991236355692012417458505)
      ·
        refine ⟨5993427266769009313093879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7991236355692012417458505 5993427266769009313093879)
        ·
          refine ⟨8990140900153513969640819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5993427266769009313093879 8990140900153513969640819)
          ·
            refine ⟨13485211350230270954461229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8990140900153513969640819 13485211350230270954461229)
            ·
              refine ⟨5056954256336351607922961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13485211350230270954461229 5056954256336351607922961)
              ·
                refine ⟨3792715692252263705942221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5056954256336351607922961 3792715692252263705942221)
                ·
                  refine ⟨1422268384594598889728333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3792715692252263705942221 1422268384594598889728333)
                  ·
                    refine ⟨533350644222974583648125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1422268384594598889728333 533350644222974583648125)
                    ·
                      rfl

theorem cell22_1558045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_1558045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558045 prefixEnd_1558045 := by exact prefixLift 1558045
  have htrace : WordTrace (prefixWord ++ tailWord_1558045) baseStart_1558045 baseEnd_1558045 := by
    simpa [prefixWord, tailWord_1558045, baseEnd_1558045] using wordTrace_append hprefix tailTrace_1558045
  have hstable : (prefixWord ++ tailWord_1558045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558045).length < 2 ^ (prefixWord ++ tailWord_1558045).sum := by decide
  have hdescent : baseEnd_1558045 < baseStart_1558045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558058 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 7]
def baseStart_1558058 : Nat := 118140960795 + 1558058 * 2 ^ 59
def prefixEnd_1558058 : Nat := 4983230072969 + 3 ^ 40 * 1558058 * 2
def baseEnd_1558058 : Nat := 177785031462882294357695

theorem tailTrace_1558058 : CollatzResearch.WordTrace tailWord_1558058 prefixEnd_1558058 177785031462882294357695 := by
  unfold tailWord_1558058
  simp only [CollatzResearch.WordTrace]
  refine ⟨14206760947357358991648707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37884695859619623977729885 14206760947357358991648707)
  ·
    refine ⟨21310141421036038487473061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14206760947357358991648707 21310141421036038487473061)
    ·
      refine ⟨3995651516444257216401199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21310141421036038487473061 3995651516444257216401199)
      ·
        refine ⟨5993477274666385824601799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3995651516444257216401199 5993477274666385824601799)
        ·
          refine ⟨8990215911999578736902699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5993477274666385824601799 8990215911999578736902699)
          ·
            refine ⟨13485323867999368105354049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8990215911999578736902699 13485323867999368105354049)
            ·
              refine ⟨10113992900999526079015537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13485323867999368105354049 10113992900999526079015537)
              ·
                refine ⟨7585494675749644559261653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10113992900999526079015537 7585494675749644559261653)
                ·
                  refine ⟨177785031462882294357695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7585494675749644559261653 177785031462882294357695)
                  ·
                    rfl

theorem cell22_1558058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_1558058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558058 prefixEnd_1558058 := by exact prefixLift 1558058
  have htrace : WordTrace (prefixWord ++ tailWord_1558058) baseStart_1558058 baseEnd_1558058 := by
    simpa [prefixWord, tailWord_1558058, baseEnd_1558058] using wordTrace_append hprefix tailTrace_1558058
  have hstable : (prefixWord ++ tailWord_1558058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558058).length < 2 ^ (prefixWord ++ tailWord_1558058).sum := by decide
  have hdescent : baseEnd_1558058 < baseStart_1558058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558073 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 2, 5]
def baseStart_1558073 : Nat := 118140960795 + 1558073 * 2 ^ 59
def prefixEnd_1558073 : Nat := 4983230072969 + 3 ^ 40 * 1558073 * 2
def baseEnd_1558073 : Nat := 533360229195191843948039

theorem tailTrace_1558073 : CollatzResearch.WordTrace tailWord_1558073 prefixEnd_1558073 533360229195191843948039 := by
  unfold tailWord_1558073
  simp only [CollatzResearch.WordTrace]
  refine ⟨56827590884375093528390873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37885060589583395685593915 56827590884375093528390873)
  ·
    refine ⟨42620693163281320146293155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56827590884375093528390873 42620693163281320146293155)
    ·
      refine ⟨63931039744921980219439733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42620693163281320146293155 63931039744921980219439733)
      ·
        refine ⟨5993534976086435645572475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63931039744921980219439733 5993534976086435645572475)
        ·
          refine ⟨8990302464129653468358713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5993534976086435645572475 8990302464129653468358713)
          ·
            refine ⟨6742726848097240101269035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8990302464129653468358713 6742726848097240101269035)
            ·
              refine ⟨10114090272145860151903553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6742726848097240101269035 10114090272145860151903553)
              ·
                refine ⟨7585567704109395113927665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10114090272145860151903553 7585567704109395113927665)
                ·
                  refine ⟨5689175778082046335445749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7585567704109395113927665 5689175778082046335445749)
                  ·
                    refine ⟨533360229195191843948039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5689175778082046335445749 533360229195191843948039)
                    ·
                      rfl

theorem cell22_1558073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_1558073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558073 prefixEnd_1558073 := by exact prefixLift 1558073
  have htrace : WordTrace (prefixWord ++ tailWord_1558073) baseStart_1558073 baseEnd_1558073 := by
    simpa [prefixWord, tailWord_1558073, baseEnd_1558073] using wordTrace_append hprefix tailTrace_1558073
  have hstable : (prefixWord ++ tailWord_1558073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558073).length < 2 ^ (prefixWord ++ tailWord_1558073).sum := by decide
  have hdescent : baseEnd_1558073 < baseStart_1558073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558103 : List Nat := [1, 1, 3, 2, 2, 3, 2, 2, 6]
def baseStart_1558103 : Nat := 118140960795 + 1558103 * 2 ^ 59
def prefixEnd_1558103 : Nat := 4983230072969 + 3 ^ 40 * 1558103 * 2
def baseEnd_1558103 : Nat := 177790166269427255232649

theorem tailTrace_1558103 : CollatzResearch.WordTrace tailWord_1558103 prefixEnd_1558103 177790166269427255232649 := by
  unfold tailWord_1558103
  simp only [CollatzResearch.WordTrace]
  refine ⟨56828685074266408651982963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37885790049510939101321975 56828685074266408651982963)
  ·
    refine ⟨85243027611399612977974445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56828685074266408651982963 85243027611399612977974445)
    ·
      refine ⟨31966135354274854866740417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85243027611399612977974445 31966135354274854866740417)
      ·
        refine ⟨23974601515706141150055313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31966135354274854866740417 23974601515706141150055313)
        ·
          refine ⟨17980951136779605862541485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23974601515706141150055313 17980951136779605862541485)
          ·
            refine ⟨6742856676292352198453057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17980951136779605862541485 6742856676292352198453057)
            ·
              refine ⟨5057142507219264148839793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6742856676292352198453057 5057142507219264148839793)
              ·
                refine ⟨3792856880414448111629845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5057142507219264148839793 3792856880414448111629845)
                ·
                  refine ⟨177790166269427255232649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3792856880414448111629845 177790166269427255232649)
                  ·
                    rfl

theorem cell22_1558103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 6].length) (baseStart_1558103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558103 prefixEnd_1558103 := by exact prefixLift 1558103
  have htrace : WordTrace (prefixWord ++ tailWord_1558103) baseStart_1558103 baseEnd_1558103 := by
    simpa [prefixWord, tailWord_1558103, baseEnd_1558103] using wordTrace_append hprefix tailTrace_1558103
  have hstable : (prefixWord ++ tailWord_1558103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558103).length < 2 ^ (prefixWord ++ tailWord_1558103).sum := by decide
  have hdescent : baseEnd_1558103 < baseStart_1558103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558135 : List Nat := [1, 1, 3, 1, 1, 3, 1, 6, 2, 3]
def baseStart_1558135 : Nat := 118140960795 + 1558135 * 2 ^ 59
def prefixEnd_1558135 : Nat := 4983230072969 + 3 ^ 40 * 1558135 * 2
def baseEnd_1558135 : Nat := 533381453062244348897849

theorem tailTrace_1558135 : CollatzResearch.WordTrace tailWord_1558135 prefixEnd_1558135 533381453062244348897849 := by
  unfold tailWord_1558135
  simp only [CollatzResearch.WordTrace]
  refine ⟨56829852210150478117147859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37886568140100318744765239 56829852210150478117147859)
  ·
    refine ⟨85244778315225717175721789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56829852210150478117147859 85244778315225717175721789)
    ·
      refine ⟨31966791868209643940895671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85244778315225717175721789 31966791868209643940895671)
      ·
        refine ⟨47950187802314465911343507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31966791868209643940895671 47950187802314465911343507)
        ·
          refine ⟨71925281703471698867015261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47950187802314465911343507 71925281703471698867015261)
          ·
            refine ⟨26971980638801887075130723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71925281703471698867015261 26971980638801887075130723)
            ·
              refine ⟨40457970958202830612696085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26971980638801887075130723 40457970958202830612696085)
              ·
                refine ⟨1896467388665757684970129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40457970958202830612696085 1896467388665757684970129)
                ·
                  refine ⟨1422350541499318263727597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1896467388665757684970129 1422350541499318263727597)
                  ·
                    refine ⟨533381453062244348897849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1422350541499318263727597 533381453062244348897849)
                    ·
                      rfl

theorem cell22_1558135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_1558135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558135 prefixEnd_1558135 := by exact prefixLift 1558135
  have htrace : WordTrace (prefixWord ++ tailWord_1558135) baseStart_1558135 baseEnd_1558135 := by
    simpa [prefixWord, tailWord_1558135, baseEnd_1558135] using wordTrace_append hprefix tailTrace_1558135
  have hstable : (prefixWord ++ tailWord_1558135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558135).length < 2 ^ (prefixWord ++ tailWord_1558135).sum := by decide
  have hdescent : baseEnd_1558135 < baseStart_1558135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558137 : List Nat := [1, 2, 1, 3, 3, 1, 5, 2, 4]
def baseStart_1558137 : Nat := 118140960795 + 1558137 * 2 ^ 59
def prefixEnd_1558137 : Nat := 4983230072969 + 3 ^ 40 * 1558137 * 2
def baseEnd_1558137 : Nat := 177794045901039003449281

theorem tailTrace_1558137 : CollatzResearch.WordTrace tailWord_1558137 prefixEnd_1558137 177794045901039003449281 := by
  unfold tailWord_1558137
  simp only [CollatzResearch.WordTrace]
  refine ⟨56829925156143232458720665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37886616770762154972480443 56829925156143232458720665)
  ·
    refine ⟨42622443867107424344040499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56829925156143232458720665 42622443867107424344040499)
    ·
      refine ⟨63933665800661136516060749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42622443867107424344040499 63933665800661136516060749)
      ·
        refine ⟨23975124675247926193522781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63933665800661136516060749 23975124675247926193522781)
        ·
          refine ⟨8990671753217972322571043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23975124675247926193522781 8990671753217972322571043)
          ·
            refine ⟨13486007629826958483856565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8990671753217972322571043 13486007629826958483856565)
            ·
              refine ⟨1264313215296277357861553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13486007629826958483856565 1264313215296277357861553)
              ·
                refine ⟨948234911472208018396165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1264313215296277357861553 948234911472208018396165)
                ·
                  refine ⟨177794045901039003449281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 948234911472208018396165 177794045901039003449281)
                  ·
                    rfl

theorem cell22_1558137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 4].length) (baseStart_1558137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558137 prefixEnd_1558137 := by exact prefixLift 1558137
  have htrace : WordTrace (prefixWord ++ tailWord_1558137) baseStart_1558137 baseEnd_1558137 := by
    simpa [prefixWord, tailWord_1558137, baseEnd_1558137] using wordTrace_append hprefix tailTrace_1558137
  have hstable : (prefixWord ++ tailWord_1558137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558137).length < 2 ^ (prefixWord ++ tailWord_1558137).sum := by decide
  have hdescent : baseEnd_1558137 < baseStart_1558137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558255 : List Nat := [1, 1, 2, 1, 5, 1, 4, 1, 6]
def baseStart_1558255 : Nat := 118140960795 + 1558255 * 2 ^ 59
def prefixEnd_1558255 : Nat := 4983230072969 + 3 ^ 40 * 1558255 * 2
def baseEnd_1558255 : Nat := 177807510504868011965827

theorem tailTrace_1558255 : CollatzResearch.WordTrace tailWord_1558255 prefixEnd_1558255 177807510504868011965827 := by
  unfold tailWord_1558255
  simp only [CollatzResearch.WordTrace]
  refine ⟨56834228969715738611516219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37889485979810492407677479 56834228969715738611516219)
  ·
    refine ⟨85251343454573607917274329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56834228969715738611516219 85251343454573607917274329)
    ·
      refine ⟨63938507590930205937955747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85251343454573607917274329 63938507590930205937955747)
      ·
        refine ⟨95907761386395308906933621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63938507590930205937955747 95907761386395308906933621)
        ·
          refine ⟨8991352629974560210025027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95907761386395308906933621 8991352629974560210025027)
          ·
            refine ⟨13487028944961840315037541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8991352629974560210025027 13487028944961840315037541)
            ·
              refine ⟨2528817927180345059069539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13487028944961840315037541 2528817927180345059069539)
              ·
                refine ⟨3793226890770517588604309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2528817927180345059069539 3793226890770517588604309)
                ·
                  refine ⟨177807510504868011965827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3793226890770517588604309 177807510504868011965827)
                  ·
                    rfl

theorem cell22_1558255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 6].length) (baseStart_1558255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558255 prefixEnd_1558255 := by exact prefixLift 1558255
  have htrace : WordTrace (prefixWord ++ tailWord_1558255) baseStart_1558255 baseEnd_1558255 := by
    simpa [prefixWord, tailWord_1558255, baseEnd_1558255] using wordTrace_append hprefix tailTrace_1558255
  have hstable : (prefixWord ++ tailWord_1558255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558255).length < 2 ^ (prefixWord ++ tailWord_1558255).sum := by decide
  have hdescent : baseEnd_1558255 < baseStart_1558255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558274 : List Nat := [3, 4, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_1558274 : Nat := 118140960795 + 1558274 * 2 ^ 59
def prefixEnd_1558274 : Nat := 4983230072969 + 3 ^ 40 * 1558274 * 2
def baseEnd_1558274 : Nat := 533429035602894319672423

theorem tailTrace_1558274 : CollatzResearch.WordTrace tailWord_1558274 prefixEnd_1558274 533429035602894319672423 := by
  unfold tailWord_1558274
  simp only [CollatzResearch.WordTrace]
  refine ⟨14208730489161726214114469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37889947971097936570971917 14208730489161726214114469)
  ·
    refine ⟨2664136966717823665146463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14208730489161726214114469 2664136966717823665146463)
    ·
      refine ⟨3996205450076735497719695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2664136966717823665146463 3996205450076735497719695)
      ·
        refine ⟨5994308175115103246579543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3996205450076735497719695 5994308175115103246579543)
        ·
          refine ⟨8991462262672654869869315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5994308175115103246579543 8991462262672654869869315)
          ·
            refine ⟨13487193394008982304803973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8991462262672654869869315 13487193394008982304803973)
            ·
              refine ⟨2528848761376684182150745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13487193394008982304803973 2528848761376684182150745)
              ·
                refine ⟨1896636571032513136613059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2528848761376684182150745 1896636571032513136613059)
                ·
                  refine ⟨2844954856548769704919589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1896636571032513136613059 2844954856548769704919589)
                  ·
                    refine ⟨533429035602894319672423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2844954856548769704919589 533429035602894319672423)
                    ·
                      rfl

theorem cell22_1558274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_1558274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558274 prefixEnd_1558274 := by exact prefixLift 1558274
  have htrace : WordTrace (prefixWord ++ tailWord_1558274) baseStart_1558274 baseEnd_1558274 := by
    simpa [prefixWord, tailWord_1558274, baseEnd_1558274] using wordTrace_append hprefix tailTrace_1558274
  have hstable : (prefixWord ++ tailWord_1558274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558274).length < 2 ^ (prefixWord ++ tailWord_1558274).sum := by decide
  have hdescent : baseEnd_1558274 < baseStart_1558274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558321 : List Nat := [1, 2, 2, 3, 2, 4, 2, 1, 2, 3]
def baseStart_1558321 : Nat := 118140960795 + 1558321 * 2 ^ 59
def prefixEnd_1558321 : Nat := 4983230072969 + 3 ^ 40 * 1558321 * 2
def baseEnd_1558321 : Nat := 533445124663401863747279

theorem tailTrace_1558321 : CollatzResearch.WordTrace tailWord_1558321 prefixEnd_1558321 533445124663401863747279 := by
  unfold tailWord_1558321
  simp only [CollatzResearch.WordTrace]
  refine ⟨56836636187476631883418817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37891090791651087922279211 56836636187476631883418817)
  ·
    refine ⟨42627477140607473912564113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56836636187476631883418817 42627477140607473912564113)
    ·
      refine ⟨31970607855455605434423085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42627477140607473912564113 31970607855455605434423085)
      ·
        refine ⟨11988977945795852037908657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31970607855455605434423085 11988977945795852037908657)
        ·
          refine ⟨8991733459346889028431493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11988977945795852037908657 8991733459346889028431493)
          ·
            refine ⟨1685950023627541692830905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8991733459346889028431493 1685950023627541692830905)
            ·
              refine ⟨1264462517720656269623179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1685950023627541692830905 1264462517720656269623179)
              ·
                refine ⟨1896693776580984404434769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1264462517720656269623179 1896693776580984404434769)
                ·
                  refine ⟨1422520332435738303326077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1896693776580984404434769 1422520332435738303326077)
                  ·
                    refine ⟨533445124663401863747279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1422520332435738303326077 533445124663401863747279)
                    ·
                      rfl

theorem cell22_1558321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 2, 3].length) (baseStart_1558321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558321 prefixEnd_1558321 := by exact prefixLift 1558321
  have htrace : WordTrace (prefixWord ++ tailWord_1558321) baseStart_1558321 baseEnd_1558321 := by
    simpa [prefixWord, tailWord_1558321, baseEnd_1558321] using wordTrace_append hprefix tailTrace_1558321
  have hstable : (prefixWord ++ tailWord_1558321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558321).length < 2 ^ (prefixWord ++ tailWord_1558321).sum := by decide
  have hdescent : baseEnd_1558321 < baseStart_1558321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558332 : List Nat := [2, 2, 2, 2, 1, 1, 2, 4, 3, 3]
def baseStart_1558332 : Nat := 118140960795 + 1558332 * 2 ^ 59
def prefixEnd_1558332 : Nat := 4983230072969 + 3 ^ 40 * 1558332 * 2
def baseEnd_1558332 : Nat := 533448890188201501722245

theorem tailTrace_1558332 : CollatzResearch.WordTrace tailWord_1558332 prefixEnd_1558332 533448890188201501722245 := by
  unfold tailWord_1558332
  simp only [CollatzResearch.WordTrace]
  refine ⟨28418518695218390381034625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37891358260291187174712833 28418518695218390381034625)
  ·
    refine ⟨21313889021413792785775969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28418518695218390381034625 21313889021413792785775969)
    ·
      refine ⟨15985416766060344589331977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21313889021413792785775969 15985416766060344589331977)
      ·
        refine ⟨11989062574545258441998983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15985416766060344589331977 11989062574545258441998983)
        ·
          refine ⟨17983593861817887662998475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11989062574545258441998983 17983593861817887662998475)
          ·
            refine ⟨26975390792726831494497713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17983593861817887662998475 26975390792726831494497713)
            ·
              refine ⟨20231543094545123620873285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26975390792726831494497713 20231543094545123620873285)
              ·
                refine ⟨3793414330227210678913741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20231543094545123620873285 3793414330227210678913741)
                ·
                  refine ⟨1422530373835204004592653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3793414330227210678913741 1422530373835204004592653)
                  ·
                    refine ⟨533448890188201501722245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1422530373835204004592653 533448890188201501722245)
                    ·
                      rfl

theorem cell22_1558332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_1558332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558332 prefixEnd_1558332 := by exact prefixLift 1558332
  have htrace : WordTrace (prefixWord ++ tailWord_1558332) baseStart_1558332 baseEnd_1558332 := by
    simpa [prefixWord, tailWord_1558332, baseEnd_1558332] using wordTrace_append hprefix tailTrace_1558332
  have hstable : (prefixWord ++ tailWord_1558332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558332).length < 2 ^ (prefixWord ++ tailWord_1558332).sum := by decide
  have hdescent : baseEnd_1558332 < baseStart_1558332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558362 : List Nat := [3, 1, 1, 2, 1, 3, 4, 2, 5]
def baseStart_1558362 : Nat := 118140960795 + 1558362 * 2 ^ 59
def prefixEnd_1558362 : Nat := 4983230072969 + 3 ^ 40 * 1558362 * 2
def baseEnd_1558362 : Nat := 177819719933763807824051

theorem tailTrace_1558362 : CollatzResearch.WordTrace tailWord_1558362 prefixEnd_1558362 177819719933763807824051 := by
  unfold tailWord_1558362
  simp only [CollatzResearch.WordTrace]
  refine ⟨14209532895082023971415335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37892087720218730590440893 14209532895082023971415335)
  ·
    refine ⟨21314299342623035957123003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14209532895082023971415335 21314299342623035957123003)
    ·
      refine ⟨31971449013934553935684505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21314299342623035957123003 31971449013934553935684505)
      ·
        refine ⟨23978586760450915451763379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31971449013934553935684505 23978586760450915451763379)
        ·
          refine ⟨35967880140676373177645069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23978586760450915451763379 35967880140676373177645069)
          ·
            refine ⟨13487955052753639941616901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35967880140676373177645069 13487955052753639941616901)
            ·
              refine ⟨2528991572391307489053169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13487955052753639941616901 2528991572391307489053169)
              ·
                refine ⟨1896743679293480616789877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2528991572391307489053169 1896743679293480616789877)
                ·
                  refine ⟨177819719933763807824051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1896743679293480616789877 177819719933763807824051)
                  ·
                    rfl

theorem cell22_1558362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_1558362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558362 prefixEnd_1558362 := by exact prefixLift 1558362
  have htrace : WordTrace (prefixWord ++ tailWord_1558362) baseStart_1558362 baseEnd_1558362 := by
    simpa [prefixWord, tailWord_1558362, baseEnd_1558362] using wordTrace_append hprefix tailTrace_1558362
  have hstable : (prefixWord ++ tailWord_1558362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558362).length < 2 ^ (prefixWord ++ tailWord_1558362).sum := by decide
  have hdescent : baseEnd_1558362 < baseStart_1558362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558435 : List Nat := [1, 1, 1, 4, 1, 2, 1, 11]
def baseStart_1558435 : Nat := 118140960795 + 1558435 * 2 ^ 59
def prefixEnd_1558435 : Nat := 4983230072969 + 3 ^ 40 * 1558435 * 2
def baseEnd_1558435 : Nat := 59276016577015951821881

theorem tailTrace_1558435 : CollatzResearch.WordTrace tailWord_1558435 prefixEnd_1558435 59276016577015951821881 := by
  unfold tailWord_1558435
  simp only [CollatzResearch.WordTrace]
  refine ⟨56840794109063629353068759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37893862739375752902045839 56840794109063629353068759)
  ·
    refine ⟨85261191163595444029603139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56840794109063629353068759 85261191163595444029603139)
    ·
      refine ⟨127891786745393166044404709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85261191163595444029603139 127891786745393166044404709)
      ·
        refine ⟨23979710014761218633325883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127891786745393166044404709 23979710014761218633325883)
        ·
          refine ⟨35969565022141827949988825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23979710014761218633325883 35969565022141827949988825)
          ·
            refine ⟨26977173766606370962491619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35969565022141827949988825 26977173766606370962491619)
            ·
              refine ⟨40465760649909556443737429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26977173766606370962491619 40465760649909556443737429)
              ·
                refine ⟨59276016577015951821881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 40465760649909556443737429 59276016577015951821881)
                ·
                  rfl

theorem cell22_1558435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 11].length) (baseStart_1558435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558435 prefixEnd_1558435 := by exact prefixLift 1558435
  have htrace : WordTrace (prefixWord ++ tailWord_1558435) baseStart_1558435 baseEnd_1558435 := by
    simpa [prefixWord, tailWord_1558435, baseEnd_1558435] using wordTrace_append hprefix tailTrace_1558435
  have hstable : (prefixWord ++ tailWord_1558435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558435).length < 2 ^ (prefixWord ++ tailWord_1558435).sum := by decide
  have hdescent : baseEnd_1558435 < baseStart_1558435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558439 : List Nat := [1, 1, 6, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1558439 : Nat := 118140960795 + 1558439 * 2 ^ 59
def prefixEnd_1558439 : Nat := 4983230072969 + 3 ^ 40 * 1558439 * 2
def baseEnd_1558439 : Nat := 533485518474888889296917

theorem tailTrace_1558439 : CollatzResearch.WordTrace tailWord_1558439 prefixEnd_1558439 533485518474888889296917 := by
  unfold tailWord_1558439
  simp only [CollatzResearch.WordTrace]
  refine ⟨56840940001049138036214371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37893960000699425357476247 56840940001049138036214371)
  ·
    refine ⟨85261410001573707054321557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56840940001049138036214371 85261410001573707054321557)
    ·
      refine ⟨3996628593823767518171323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85261410001573707054321557 3996628593823767518171323)
      ·
        refine ⟨5994942890735651277256985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3996628593823767518171323 5994942890735651277256985)
        ·
          refine ⟨4496207168051738457942739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5994942890735651277256985 4496207168051738457942739)
          ·
            refine ⟨6744310752077607686914109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4496207168051738457942739 6744310752077607686914109)
            ·
              refine ⟨2529116532029102882592791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6744310752077607686914109 2529116532029102882592791)
              ·
                refine ⟨3793674798043654323889187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2529116532029102882592791 3793674798043654323889187)
                ·
                  refine ⟨5690512197065481485833781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3793674798043654323889187 5690512197065481485833781)
                  ·
                    refine ⟨533485518474888889296917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5690512197065481485833781 533485518474888889296917)
                    ·
                      rfl

theorem cell22_1558439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1558439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558439 prefixEnd_1558439 := by exact prefixLift 1558439
  have htrace : WordTrace (prefixWord ++ tailWord_1558439) baseStart_1558439 baseEnd_1558439 := by
    simpa [prefixWord, tailWord_1558439, baseEnd_1558439] using wordTrace_append hprefix tailTrace_1558439
  have hstable : (prefixWord ++ tailWord_1558439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558439).length < 2 ^ (prefixWord ++ tailWord_1558439).sum := by decide
  have hdescent : baseEnd_1558439 < baseStart_1558439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558486 : List Nat := [5, 2, 1, 1, 3, 1, 2, 7]
def baseStart_1558486 : Nat := 118140960795 + 1558486 * 2 ^ 59
def prefixEnd_1558486 : Nat := 4983230072969 + 3 ^ 40 * 1558486 * 2
def baseEnd_1558486 : Nat := 59277956392821825930197

theorem tailTrace_1558486 : CollatzResearch.WordTrace tailWord_1558486 prefixEnd_1558486 59277956392821825930197 := by
  unfold tailWord_1558486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3552665889492429066448457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37895102821252576708783541 3552665889492429066448457)
  ·
    refine ⟨2664499417119321799836343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3552665889492429066448457 2664499417119321799836343)
    ·
      refine ⟨3996749125678982699754515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2664499417119321799836343 3996749125678982699754515)
      ·
        refine ⟨5995123688518474049631773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3996749125678982699754515 5995123688518474049631773)
        ·
          refine ⟨2248171383194427768611915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5995123688518474049631773 2248171383194427768611915)
          ·
            refine ⟨3372257074791641652917873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248171383194427768611915 3372257074791641652917873)
            ·
              refine ⟨2529192806093731239688405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3372257074791641652917873 2529192806093731239688405)
              ·
                refine ⟨59277956392821825930197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2529192806093731239688405 59277956392821825930197)
                ·
                  rfl

theorem cell22_1558486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_1558486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558486 prefixEnd_1558486 := by exact prefixLift 1558486
  have htrace : WordTrace (prefixWord ++ tailWord_1558486) baseStart_1558486 baseEnd_1558486 := by
    simpa [prefixWord, tailWord_1558486, baseEnd_1558486] using wordTrace_append hprefix tailTrace_1558486
  have hstable : (prefixWord ++ tailWord_1558486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558486).length < 2 ^ (prefixWord ++ tailWord_1558486).sum := by decide
  have hdescent : baseEnd_1558486 < baseStart_1558486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558490 : List Nat := [3, 1, 1, 2, 6, 1, 2, 1, 2, 3]
def baseStart_1558490 : Nat := 118140960795 + 1558490 * 2 ^ 59
def prefixEnd_1558490 : Nat := 4983230072969 + 3 ^ 40 * 1558490 * 2
def baseEnd_1558490 : Nat := 533502976817141756271761

theorem tailTrace_1558490 : CollatzResearch.WordTrace tailWord_1558490 prefixEnd_1558490 533502976817141756271761 := by
  unfold tailWord_1558490
  simp only [CollatzResearch.WordTrace]
  refine ⟨14210700030966093436580231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37895200082576249164213949 14210700030966093436580231)
  ·
    refine ⟨21316050046449140154870347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14210700030966093436580231 21316050046449140154870347)
    ·
      refine ⟨31974075069673710232305521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21316050046449140154870347 31974075069673710232305521)
      ·
        refine ⟨23980556302255282674229141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31974075069673710232305521 23980556302255282674229141)
        ·
          refine ⟨1124088576668216375354491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23980556302255282674229141 1124088576668216375354491)
          ·
            refine ⟨1686132865002324563031737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124088576668216375354491 1686132865002324563031737)
            ·
              refine ⟨1264599648751743422273803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1686132865002324563031737 1264599648751743422273803)
              ·
                refine ⟨1896899473127615133410705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1264599648751743422273803 1896899473127615133410705)
                ·
                  refine ⟨1422674604845711350058029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1896899473127615133410705 1422674604845711350058029)
                  ·
                    refine ⟨533502976817141756271761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1422674604845711350058029 533502976817141756271761)
                    ·
                      rfl

theorem cell22_1558490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 2, 3].length) (baseStart_1558490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558490 prefixEnd_1558490 := by exact prefixLift 1558490
  have htrace : WordTrace (prefixWord ++ tailWord_1558490) baseStart_1558490 baseEnd_1558490 := by
    simpa [prefixWord, tailWord_1558490, baseEnd_1558490] using wordTrace_append hprefix tailTrace_1558490
  have hstable : (prefixWord ++ tailWord_1558490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558490).length < 2 ^ (prefixWord ++ tailWord_1558490).sum := by decide
  have hdescent : baseEnd_1558490 < baseStart_1558490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558535 : List Nat := [1, 1, 4, 3, 1, 4, 2, 2, 1, 3]
def baseStart_1558535 : Nat := 118140960795 + 1558535 * 2 ^ 59
def prefixEnd_1558535 : Nat := 4983230072969 + 3 ^ 40 * 1558535 * 2
def baseEnd_1558535 : Nat := 533518381236776638896623

theorem tailTrace_1558535 : CollatzResearch.WordTrace tailWord_1558535 prefixEnd_1558535 533518381236776638896623 := by
  unfold tailWord_1558535
  simp only [CollatzResearch.WordTrace]
  refine ⟨56844441408701346431709059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37896294272467564287806039 56844441408701346431709059)
  ·
    refine ⟨85266662113052019647563589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56844441408701346431709059 85266662113052019647563589)
    ·
      refine ⟨15987499146197253683918173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85266662113052019647563589 15987499146197253683918173)
      ·
        refine ⟨5995312179823970131469315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15987499146197253683918173 5995312179823970131469315)
        ·
          refine ⟨8992968269735955197203973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5995312179823970131469315 8992968269735955197203973)
          ·
            refine ⟨1686181550575491599475745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8992968269735955197203973 1686181550575491599475745)
            ·
              refine ⟨1264636162931618699606809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1686181550575491599475745 1264636162931618699606809)
              ·
                refine ⟨948477122198714024705107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1264636162931618699606809 948477122198714024705107)
                ·
                  refine ⟨1422715683298071037057661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 948477122198714024705107 1422715683298071037057661)
                  ·
                    refine ⟨533518381236776638896623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1422715683298071037057661 533518381236776638896623)
                    ·
                      rfl

theorem cell22_1558535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_1558535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558535 prefixEnd_1558535 := by exact prefixLift 1558535
  have htrace : WordTrace (prefixWord ++ tailWord_1558535) baseStart_1558535 baseEnd_1558535 := by
    simpa [prefixWord, tailWord_1558535, baseEnd_1558535] using wordTrace_append hprefix tailTrace_1558535
  have hstable : (prefixWord ++ tailWord_1558535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558535).length < 2 ^ (prefixWord ++ tailWord_1558535).sum := by decide
  have hdescent : baseEnd_1558535 < baseStart_1558535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558576 : List Nat := [2, 1, 1, 1, 2, 6, 2, 3, 4]
def baseStart_1558576 : Nat := 118140960795 + 1558576 * 2 ^ 59
def prefixEnd_1558576 : Nat := 4983230072969 + 3 ^ 40 * 1558576 * 2
def baseEnd_1558576 : Nat := 177844138791555399540499

theorem tailTrace_1558576 : CollatzResearch.WordTrace tailWord_1558576 prefixEnd_1558576 177844138791555399540499 := by
  unfold tailWord_1558576
  simp only [CollatzResearch.WordTrace]
  refine ⟨28422968400776405216975791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37897291201035206955967721 28422968400776405216975791)
  ·
    refine ⟨42634452601164607825463687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28422968400776405216975791 42634452601164607825463687)
    ·
      refine ⟨63951678901746911738195531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42634452601164607825463687 63951678901746911738195531)
      ·
        refine ⟨95927518352620367607293297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63951678901746911738195531 95927518352620367607293297)
        ·
          refine ⟨71945638764465275705469973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95927518352620367607293297 71945638764465275705469973)
          ·
            refine ⟨3372451817084309798693905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71945638764465275705469973 3372451817084309798693905)
            ·
              refine ⟨2529338862813232349020429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3372451817084309798693905 2529338862813232349020429)
              ·
                refine ⟨948502073554962130882661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2529338862813232349020429 948502073554962130882661)
                ·
                  refine ⟨177844138791555399540499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 948502073554962130882661 177844138791555399540499)
                  ·
                    rfl

theorem cell22_1558576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 4].length) (baseStart_1558576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558576 prefixEnd_1558576 := by exact prefixLift 1558576
  have htrace : WordTrace (prefixWord ++ tailWord_1558576) baseStart_1558576 baseEnd_1558576 := by
    simpa [prefixWord, tailWord_1558576, baseEnd_1558576] using wordTrace_append hprefix tailTrace_1558576
  have hstable : (prefixWord ++ tailWord_1558576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558576).length < 2 ^ (prefixWord ++ tailWord_1558576).sum := by decide
  have hdescent : baseEnd_1558576 < baseStart_1558576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558578 : List Nat := [3, 2, 1, 1, 2, 5, 2, 1, 1, 4]
def baseStart_1558578 : Nat := 118140960795 + 1558578 * 2 ^ 59
def prefixEnd_1558578 : Nat := 4983230072969 + 3 ^ 40 * 1558578 * 2
def baseEnd_1558578 : Nat := 533533101015538860071491

theorem tailTrace_1558578 : CollatzResearch.WordTrace tailWord_1558578 prefixEnd_1558578 533533101015538860071491 := by
  unfold tailWord_1558578
  simp only [CollatzResearch.WordTrace]
  refine ⟨14211502436886391193881097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37897339831697043183682925 14211502436886391193881097)
  ·
    refine ⟨10658626827664793395410823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14211502436886391193881097 10658626827664793395410823)
    ·
      refine ⟨15987940241497190093116235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10658626827664793395410823 15987940241497190093116235)
      ·
        refine ⟨23981910362245785139674353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15987940241497190093116235 23981910362245785139674353)
        ·
          refine ⟨17986432771684338854755765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23981910362245785139674353 17986432771684338854755765)
          ·
            refine ⟨1686228072345406767633353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17986432771684338854755765 1686228072345406767633353)
            ·
              refine ⟨1264671054259055075725015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1686228072345406767633353 1264671054259055075725015)
              ·
                refine ⟨1897006581388582613587523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1264671054259055075725015 1897006581388582613587523)
                ·
                  refine ⟨2845509872082873920381285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1897006581388582613587523 2845509872082873920381285)
                  ·
                    refine ⟨533533101015538860071491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2845509872082873920381285 533533101015538860071491)
                    ·
                      rfl

theorem cell22_1558578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_1558578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558578 prefixEnd_1558578 := by exact prefixLift 1558578
  have htrace : WordTrace (prefixWord ++ tailWord_1558578) baseStart_1558578 baseEnd_1558578 := by
    simpa [prefixWord, tailWord_1558578, baseEnd_1558578] using wordTrace_append hprefix tailTrace_1558578
  have hstable : (prefixWord ++ tailWord_1558578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558578).length < 2 ^ (prefixWord ++ tailWord_1558578).sum := by decide
  have hdescent : baseEnd_1558578 < baseStart_1558578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558589 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_1558589 : Nat := 118140960795 + 1558589 * 2 ^ 59
def prefixEnd_1558589 : Nat := 4983230072969 + 3 ^ 40 * 1558589 * 2
def baseEnd_1558589 : Nat := 533536866540338498046457

theorem tailTrace_1558589 : CollatzResearch.WordTrace tailWord_1558589 prefixEnd_1558589 533536866540338498046457 := by
  unfold tailWord_1558589
  simp only [CollatzResearch.WordTrace]
  refine ⟨56846410950505713654174821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37897607300337142436116547 56846410950505713654174821)
  ·
    refine ⟨10658702053219821310157779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56846410950505713654174821 10658702053219821310157779)
    ·
      refine ⟨15988053079829731965236669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10658702053219821310157779 15988053079829731965236669)
      ·
        refine ⟨5995519904936149486963751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15988053079829731965236669 5995519904936149486963751)
        ·
          refine ⟨8993279857404224230445627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5995519904936149486963751 8993279857404224230445627)
          ·
            refine ⟨13489919786106336345668441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8993279857404224230445627 13489919786106336345668441)
            ·
              refine ⟨10117439839579752259251331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13489919786106336345668441 10117439839579752259251331)
              ·
                refine ⟨15176159759369628388876997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10117439839579752259251331 15176159759369628388876997)
                ·
                  refine ⟨2845529954881805322914437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15176159759369628388876997 2845529954881805322914437)
                  ·
                    refine ⟨533536866540338498046457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2845529954881805322914437 533536866540338498046457)
                    ·
                      rfl

theorem cell22_1558589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_1558589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558589 prefixEnd_1558589 := by exact prefixLift 1558589
  have htrace : WordTrace (prefixWord ++ tailWord_1558589) baseStart_1558589 baseEnd_1558589 := by
    simpa [prefixWord, tailWord_1558589, baseEnd_1558589] using wordTrace_append hprefix tailTrace_1558589
  have hstable : (prefixWord ++ tailWord_1558589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558589).length < 2 ^ (prefixWord ++ tailWord_1558589).sum := by decide
  have hdescent : baseEnd_1558589 < baseStart_1558589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558591 : List Nat := [1, 1, 2, 2, 3, 1, 5, 2, 2, 3]
def baseStart_1558591 : Nat := 118140960795 + 1558591 * 2 ^ 59
def prefixEnd_1558591 : Nat := 4983230072969 + 3 ^ 40 * 1558591 * 2
def baseEnd_1558591 : Nat := 533537551181211159496451

theorem tailTrace_1558591 : CollatzResearch.WordTrace tailWord_1558591 prefixEnd_1558591 533537551181211159496451 := by
  unfold tailWord_1558591
  simp only [CollatzResearch.WordTrace]
  refine ⟨56846483896498467995747627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37897655930998978663831751 56846483896498467995747627)
  ·
    refine ⟨85269725844747701993621441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56846483896498467995747627 85269725844747701993621441)
    ·
      refine ⟨63952294383560776495216081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85269725844747701993621441 63952294383560776495216081)
      ·
        refine ⟨47964220787670582371412061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63952294383560776495216081 47964220787670582371412061)
        ·
          refine ⟨17986582795376468389279523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47964220787670582371412061 17986582795376468389279523)
          ·
            refine ⟨26979874193064702583919285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17986582795376468389279523 26979874193064702583919285)
            ·
              refine ⟨2529363205599815867242433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26979874193064702583919285 2529363205599815867242433)
              ·
                refine ⟨1897022404199861900431825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2529363205599815867242433 1897022404199861900431825)
                ·
                  refine ⟨1422766803149896425323869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1897022404199861900431825 1422766803149896425323869)
                  ·
                    refine ⟨533537551181211159496451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1422766803149896425323869 533537551181211159496451)
                    ·
                      rfl

theorem cell22_1558591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 3].length) (baseStart_1558591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558591 prefixEnd_1558591 := by exact prefixLift 1558591
  have htrace : WordTrace (prefixWord ++ tailWord_1558591) baseStart_1558591 baseEnd_1558591 := by
    simpa [prefixWord, tailWord_1558591, baseEnd_1558591] using wordTrace_append hprefix tailTrace_1558591
  have hstable : (prefixWord ++ tailWord_1558591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558591).length < 2 ^ (prefixWord ++ tailWord_1558591).sum := by decide
  have hdescent : baseEnd_1558591 < baseStart_1558591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558621 : List Nat := [1, 4, 4, 1, 1, 2, 1, 8]
def baseStart_1558621 : Nat := 118140960795 + 1558621 * 2 ^ 59
def prefixEnd_1558621 : Nat := 4983230072969 + 3 ^ 40 * 1558621 * 2
def baseEnd_1558621 : Nat := 59283091199366786805151

theorem tailTrace_1558621 : CollatzResearch.WordTrace tailWord_1558621 prefixEnd_1558621 59283091199366786805151 := by
  unfold tailWord_1558621
  simp only [CollatzResearch.WordTrace]
  refine ⟨56847578086389783119339717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37898385390926522079559811 56847578086389783119339717)
  ·
    refine ⟨10658920891198084334876197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56847578086389783119339717 10658920891198084334876197)
    ·
      refine ⟨1998547667099640812789287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10658920891198084334876197 1998547667099640812789287)
      ·
        refine ⟨2997821500649461219183931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1998547667099640812789287 2997821500649461219183931)
        ·
          refine ⟨4496732250974191828775897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2997821500649461219183931 4496732250974191828775897)
          ·
            refine ⟨3372549188230643871581923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4496732250974191828775897 3372549188230643871581923)
            ·
              refine ⟨5058823782345965807372885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3372549188230643871581923 5058823782345965807372885)
              ·
                refine ⟨59283091199366786805151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5058823782345965807372885 59283091199366786805151)
                ·
                  rfl

theorem cell22_1558621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 8].length) (baseStart_1558621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558621 prefixEnd_1558621 := by exact prefixLift 1558621
  have htrace : WordTrace (prefixWord ++ tailWord_1558621) baseStart_1558621 baseEnd_1558621 := by
    simpa [prefixWord, tailWord_1558621, baseEnd_1558621] using wordTrace_append hprefix tailTrace_1558621
  have hstable : (prefixWord ++ tailWord_1558621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558621).length < 2 ^ (prefixWord ++ tailWord_1558621).sum := by decide
  have hdescent : baseEnd_1558621 < baseStart_1558621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558649 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 7]
def baseStart_1558649 : Nat := 118140960795 + 1558649 * 2 ^ 59
def prefixEnd_1558649 : Nat := 4983230072969 + 3 ^ 40 * 1558649 * 2
def baseEnd_1558649 : Nat := 177852468588839447182091

theorem tailTrace_1558649 : CollatzResearch.WordTrace tailWord_1558649 prefixEnd_1558649 177852468588839447182091 := by
  unfold tailWord_1558649
  simp only [CollatzResearch.WordTrace]
  refine ⟨56848599330288343901359001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37899066220192229267572667 56848599330288343901359001)
  ·
    refine ⟨42636449497716257926019251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56848599330288343901359001 42636449497716257926019251)
    ·
      refine ⟨63954674246574386889028877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42636449497716257926019251 63954674246574386889028877)
      ·
        refine ⟨23983002842465395083385829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63954674246574386889028877 23983002842465395083385829)
        ·
          refine ⟨4496813032962261578134843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23983002842465395083385829 4496813032962261578134843)
          ·
            refine ⟨6745219549443392367202265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4496813032962261578134843 6745219549443392367202265)
            ·
              refine ⟨5058914662082544275401699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6745219549443392367202265 5058914662082544275401699)
              ·
                refine ⟨7588371993123816413102549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5058914662082544275401699 7588371993123816413102549)
                ·
                  refine ⟨177852468588839447182091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7588371993123816413102549 177852468588839447182091)
                  ·
                    rfl

theorem cell22_1558649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 7].length) (baseStart_1558649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558649 prefixEnd_1558649 := by exact prefixLift 1558649
  have htrace : WordTrace (prefixWord ++ tailWord_1558649) baseStart_1558649 baseEnd_1558649 := by
    simpa [prefixWord, tailWord_1558649, baseEnd_1558649] using wordTrace_append hprefix tailTrace_1558649
  have hstable : (prefixWord ++ tailWord_1558649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558649).length < 2 ^ (prefixWord ++ tailWord_1558649).sum := by decide
  have hdescent : baseEnd_1558649 < baseStart_1558649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558653 : List Nat := [1, 4, 1, 1, 3, 4, 1, 1, 3, 3]
def baseStart_1558653 : Nat := 118140960795 + 1558653 * 2 ^ 59
def prefixEnd_1558653 : Nat := 4983230072969 + 3 ^ 40 * 1558653 * 2
def baseEnd_1558653 : Nat := 533558775048263664446261

theorem tailTrace_1558653 : CollatzResearch.WordTrace tailWord_1558653 prefixEnd_1558653 533558775048263664446261 := by
  unfold tailWord_1558653
  simp only [CollatzResearch.WordTrace]
  refine ⟨56848745222273852584504613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37899163481515901723003075 56848745222273852584504613)
  ·
    refine ⟨10659139729176347359594615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56848745222273852584504613 10659139729176347359594615)
    ·
      refine ⟨15988709593764521039391923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10659139729176347359594615 15988709593764521039391923)
      ·
        refine ⟨23983064390646781559087885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15988709593764521039391923 23983064390646781559087885)
        ·
          refine ⟨8993649146492543084657957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23983064390646781559087885 8993649146492543084657957)
          ·
            refine ⟨1686309214967351828373367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8993649146492543084657957 1686309214967351828373367)
            ·
              refine ⟨2529463822451027742560051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1686309214967351828373367 2529463822451027742560051)
              ·
                refine ⟨3794195733676541613840077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2529463822451027742560051 3794195733676541613840077)
                ·
                  refine ⟨1422823400128703105190029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3794195733676541613840077 1422823400128703105190029)
                  ·
                    refine ⟨533558775048263664446261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1422823400128703105190029 533558775048263664446261)
                    ·
                      rfl

theorem cell22_1558653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_1558653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558653 prefixEnd_1558653 := by exact prefixLift 1558653
  have htrace : WordTrace (prefixWord ++ tailWord_1558653) baseStart_1558653 baseEnd_1558653 := by
    simpa [prefixWord, tailWord_1558653, baseEnd_1558653] using wordTrace_append hprefix tailTrace_1558653
  have hstable : (prefixWord ++ tailWord_1558653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558653).length < 2 ^ (prefixWord ++ tailWord_1558653).sum := by decide
  have hdescent : baseEnd_1558653 < baseStart_1558653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558666 : List Nat := [3, 1, 2, 3, 1, 3, 1, 3, 5]
def baseStart_1558666 : Nat := 118140960795 + 1558666 * 2 ^ 59
def prefixEnd_1558666 : Nat := 4983230072969 + 3 ^ 40 * 1558666 * 2
def baseEnd_1558666 : Nat := 177854408404645321290407

theorem tailTrace_1558666 : CollatzResearch.WordTrace tailWord_1558666 prefixEnd_1558666 177854408404645321290407 := by
  unfold tailWord_1558666
  simp only [CollatzResearch.WordTrace]
  refine ⟨14212304842806688951181963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37899479580817837203151901 14212304842806688951181963)
  ·
    refine ⟨21318457264210033426772945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14212304842806688951181963 21318457264210033426772945)
    ·
      refine ⟨15988842948157525070079709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21318457264210033426772945 15988842948157525070079709)
      ·
        refine ⟨5995816105559071901279891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15988842948157525070079709 5995816105559071901279891)
        ·
          refine ⟨8993724158338607851919837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5995816105559071901279891 8993724158338607851919837)
          ·
            refine ⟨3372646559376977944469939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8993724158338607851919837 3372646559376977944469939)
            ·
              refine ⟨5058969839065466916704909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3372646559376977944469939 5058969839065466916704909)
              ·
                refine ⟨1897113689649550093764341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5058969839065466916704909 1897113689649550093764341)
                ·
                  refine ⟨177854408404645321290407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1897113689649550093764341 177854408404645321290407)
                  ·
                    rfl

theorem cell22_1558666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_1558666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558666 prefixEnd_1558666 := by exact prefixLift 1558666
  have htrace : WordTrace (prefixWord ++ tailWord_1558666) baseStart_1558666 baseEnd_1558666 := by
    simpa [prefixWord, tailWord_1558666, baseEnd_1558666] using wordTrace_append hprefix tailTrace_1558666
  have hstable : (prefixWord ++ tailWord_1558666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558666).length < 2 ^ (prefixWord ++ tailWord_1558666).sum := by decide
  have hdescent : baseEnd_1558666 < baseStart_1558666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558760 : List Nat := [2, 1, 4, 1, 2, 4, 1, 2, 2, 3]
def baseStart_1558760 : Nat := 118140960795 + 1558760 * 2 ^ 59
def prefixEnd_1558760 : Nat := 4983230072969 + 3 ^ 40 * 1558760 * 2
def baseEnd_1558760 : Nat := 533595403334951052020933

theorem tailTrace_1558760 : CollatzResearch.WordTrace tailWord_1558760 prefixEnd_1558760 533595403334951052020933 := by
  unfold tailWord_1558760
  simp only [CollatzResearch.WordTrace]
  refine ⟨28426323916443104929324867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37901765221924139905766489 28426323916443104929324867)
  ·
    refine ⟨42639485874664657393987301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28426323916443104929324867 42639485874664657393987301)
    ·
      refine ⟨7994903601499623261372619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42639485874664657393987301 7994903601499623261372619)
      ·
        refine ⟨11992355402249434892058929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7994903601499623261372619 11992355402249434892058929)
        ·
          refine ⟨8994266551687076169044197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11992355402249434892058929 8994266551687076169044197)
          ·
            refine ⟨1686424978441326781695787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8994266551687076169044197 1686424978441326781695787)
            ·
              refine ⟨2529637467661990172543681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1686424978441326781695787 2529637467661990172543681)
              ·
                refine ⟨1897228100746492629407761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2529637467661990172543681 1897228100746492629407761)
                ·
                  refine ⟨1422921075559869472055821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1897228100746492629407761 1422921075559869472055821)
                  ·
                    refine ⟨533595403334951052020933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1422921075559869472055821 533595403334951052020933)
                    ·
                      rfl

theorem cell22_1558760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_1558760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558760 prefixEnd_1558760 := by exact prefixLift 1558760
  have htrace : WordTrace (prefixWord ++ tailWord_1558760) baseStart_1558760 baseEnd_1558760 := by
    simpa [prefixWord, tailWord_1558760, baseEnd_1558760] using wordTrace_append hprefix tailTrace_1558760
  have hstable : (prefixWord ++ tailWord_1558760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558760).length < 2 ^ (prefixWord ++ tailWord_1558760).sum := by decide
  have hdescent : baseEnd_1558760 < baseStart_1558760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558769 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 1, 8]
def baseStart_1558769 : Nat := 118140960795 + 1558769 * 2 ^ 59
def prefixEnd_1558769 : Nat := 4983230072969 + 3 ^ 40 * 1558769 * 2
def baseEnd_1558769 : Nat := 533598484218878028545905

theorem tailTrace_1558769 : CollatzResearch.WordTrace tailWord_1558769 prefixEnd_1558769 533598484218878028545905 := by
  unfold tailWord_1558769
  simp only [CollatzResearch.WordTrace]
  refine ⟨56852976089853604395727361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37901984059902402930484907 56852976089853604395727361)
  ·
    refine ⟨42639732067390203296795521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56852976089853604395727361 42639732067390203296795521)
    ·
      refine ⟨31979799050542652472596641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42639732067390203296795521 31979799050542652472596641)
      ·
        refine ⟨23984849287906989354447481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31979799050542652472596641 23984849287906989354447481)
        ·
          refine ⟨17988636965930242015835611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23984849287906989354447481 17988636965930242015835611)
          ·
            refine ⟨26982955448895363023753417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17988636965930242015835611 26982955448895363023753417)
            ·
              refine ⟨20237216586671522267815063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26982955448895363023753417 20237216586671522267815063)
              ·
                refine ⟨30355824880007283401722595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20237216586671522267815063 30355824880007283401722595)
                ·
                  refine ⟨45533737320010925102583893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30355824880007283401722595 45533737320010925102583893)
                  ·
                    refine ⟨533598484218878028545905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45533737320010925102583893 533598484218878028545905)
                    ·
                      rfl

theorem cell22_1558769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_1558769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558769 prefixEnd_1558769 := by exact prefixLift 1558769
  have htrace : WordTrace (prefixWord ++ tailWord_1558769) baseStart_1558769 baseEnd_1558769 := by
    simpa [prefixWord, tailWord_1558769, baseEnd_1558769] using wordTrace_append hprefix tailTrace_1558769
  have hstable : (prefixWord ++ tailWord_1558769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558769).length < 2 ^ (prefixWord ++ tailWord_1558769).sum := by decide
  have hdescent : baseEnd_1558769 < baseStart_1558769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558799 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 1, 7]
def baseStart_1558799 : Nat := 118140960795 + 1558799 * 2 ^ 59
def prefixEnd_1558799 : Nat := 4983230072969 + 3 ^ 40 * 1558799 * 2
def baseEnd_1558799 : Nat := 533608753831967950295813

theorem tailTrace_1558799 : CollatzResearch.WordTrace tailWord_1558799 prefixEnd_1558799 533608753831967950295813 := by
  unfold tailWord_1558799
  simp only [CollatzResearch.WordTrace]
  refine ⟨56854070279744919519319451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37902713519829946346212967 56854070279744919519319451)
  ·
    refine ⟨85281105419617379278979177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56854070279744919519319451 85281105419617379278979177)
    ·
      refine ⟨63960829064713034459234383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85281105419617379278979177 63960829064713034459234383)
      ·
        refine ⟨95941243597069551688851575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63960829064713034459234383 95941243597069551688851575)
        ·
          refine ⟨143911865395604327533277363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95941243597069551688851575 143911865395604327533277363)
          ·
            refine ⟨215867798093406491299916045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143911865395604327533277363 215867798093406491299916045)
            ·
              refine ⟨80950424285027434237468517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215867798093406491299916045 80950424285027434237468517)
              ·
                refine ⟨15178204553442643919525347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80950424285027434237468517 15178204553442643919525347)
                ·
                  refine ⟨22767306830163965879288021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15178204553442643919525347 22767306830163965879288021)
                  ·
                    refine ⟨533608753831967950295813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22767306830163965879288021 533608753831967950295813)
                    ·
                      rfl

theorem cell22_1558799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_1558799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558799 prefixEnd_1558799 := by exact prefixLift 1558799
  have htrace : WordTrace (prefixWord ++ tailWord_1558799) baseStart_1558799 baseEnd_1558799 := by
    simpa [prefixWord, tailWord_1558799, baseEnd_1558799] using wordTrace_append hprefix tailTrace_1558799
  have hstable : (prefixWord ++ tailWord_1558799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558799).length < 2 ^ (prefixWord ++ tailWord_1558799).sum := by decide
  have hdescent : baseEnd_1558799 < baseStart_1558799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558805 : List Nat := [1, 3, 2, 1, 2, 1, 5, 3, 1, 3]
def baseStart_1558805 : Nat := 118140960795 + 1558805 * 2 ^ 59
def prefixEnd_1558805 : Nat := 4983230072969 + 3 ^ 40 * 1558805 * 2
def baseEnd_1558805 : Nat := 533610807754585934645795

theorem tailTrace_1558805 : CollatzResearch.WordTrace tailWord_1558805 prefixEnd_1558805 533610807754585934645795 := by
  unfold tailWord_1558805
  simp only [CollatzResearch.WordTrace]
  refine ⟨56854289117723182544037869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37902859411815455029358579 56854289117723182544037869)
  ·
    refine ⟨21320358419146193454014201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56854289117723182544037869 21320358419146193454014201)
    ·
      refine ⟨15990268814359645090510651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21320358419146193454014201 15990268814359645090510651)
      ·
        refine ⟨23985403221539467635765977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15990268814359645090510651 23985403221539467635765977)
        ·
          refine ⟨17989052416154600726824483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23985403221539467635765977 17989052416154600726824483)
          ·
            refine ⟨26983578624231901090236725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17989052416154600726824483 26983578624231901090236725)
            ·
              refine ⟨2529710496021740727209693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26983578624231901090236725 2529710496021740727209693)
              ·
                refine ⟨948641436008152772703635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2529710496021740727209693 948641436008152772703635)
                ·
                  refine ⟨1422962154012229159055453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 948641436008152772703635 1422962154012229159055453)
                  ·
                    refine ⟨533610807754585934645795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1422962154012229159055453 533610807754585934645795)
                    ·
                      rfl

theorem cell22_1558805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_1558805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558805 prefixEnd_1558805 := by exact prefixLift 1558805
  have htrace : WordTrace (prefixWord ++ tailWord_1558805) baseStart_1558805 baseEnd_1558805 := by
    simpa [prefixWord, tailWord_1558805, baseEnd_1558805] using wordTrace_append hprefix tailTrace_1558805
  have hstable : (prefixWord ++ tailWord_1558805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558805).length < 2 ^ (prefixWord ++ tailWord_1558805).sum := by decide
  have hdescent : baseEnd_1558805 < baseStart_1558805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558865 : List Nat := [1, 2, 2, 1, 4, 3, 3, 1, 1, 4]
def baseStart_1558865 : Nat := 118140960795 + 1558865 * 2 ^ 59
def prefixEnd_1558865 : Nat := 4983230072969 + 3 ^ 40 * 1558865 * 2
def baseEnd_1558865 : Nat := 533631346980765778145611

theorem tailTrace_1558865 : CollatzResearch.WordTrace tailWord_1558865 prefixEnd_1558865 533631346980765778145611 := by
  unfold tailWord_1558865
  simp only [CollatzResearch.WordTrace]
  refine ⟨56856477497505812791222049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37904318331670541860814699 56856477497505812791222049)
  ·
    refine ⟨42642358123129359593416537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56856477497505812791222049 42642358123129359593416537)
    ·
      refine ⟨31981768592347019695062403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42642358123129359593416537 31981768592347019695062403)
      ·
        refine ⟨47972652888520529542593605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31981768592347019695062403 47972652888520529542593605)
        ·
          refine ⟨8994872416597599289236301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47972652888520529542593605 8994872416597599289236301)
          ·
            refine ⟨3373077156224099733463613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8994872416597599289236301 3373077156224099733463613)
            ·
              refine ⟨1264903933584037400048855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3373077156224099733463613 1264903933584037400048855)
              ·
                refine ⟨1897355900376056100073283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1264903933584037400048855 1897355900376056100073283)
                ·
                  refine ⟨2846033850564084150109925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1897355900376056100073283 2846033850564084150109925)
                  ·
                    refine ⟨533631346980765778145611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2846033850564084150109925 533631346980765778145611)
                    ·
                      rfl

theorem cell22_1558865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 1, 4].length) (baseStart_1558865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558865 prefixEnd_1558865 := by exact prefixLift 1558865
  have htrace : WordTrace (prefixWord ++ tailWord_1558865) baseStart_1558865 baseEnd_1558865 := by
    simpa [prefixWord, tailWord_1558865, baseEnd_1558865] using wordTrace_append hprefix tailTrace_1558865
  have hstable : (prefixWord ++ tailWord_1558865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558865).length < 2 ^ (prefixWord ++ tailWord_1558865).sum := by decide
  have hdescent : baseEnd_1558865 < baseStart_1558865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558880 : List Nat := [2, 1, 1, 3, 5, 1, 1, 4, 4]
def baseStart_1558880 : Nat := 118140960795 + 1558880 * 2 ^ 59
def prefixEnd_1558880 : Nat := 4983230072969 + 3 ^ 40 * 1558880 * 2
def baseEnd_1558880 : Nat := 177878827262436913006855

theorem tailTrace_1558880 : CollatzResearch.WordTrace tailWord_1558880 prefixEnd_1558880 177878827262436913006855 := by
  unfold tailWord_1558880
  simp only [CollatzResearch.WordTrace]
  refine ⟨28428512296225735176509047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37904683061634313568678729 28428512296225735176509047)
  ·
    refine ⟨42642768444338602764763571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28428512296225735176509047 42642768444338602764763571)
    ·
      refine ⟨63964152666507904147145357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42642768444338602764763571 63964152666507904147145357)
      ·
        refine ⟨23986557249940464055179509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63964152666507904147145357 23986557249940464055179509)
        ·
          refine ⟨2248739742181918505173079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23986557249940464055179509 2248739742181918505173079)
          ·
            refine ⟨3373109613272877757759619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248739742181918505173079 3373109613272877757759619)
            ·
              refine ⟨5059664419909316636639429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3373109613272877757759619 5059664419909316636639429)
              ·
                refine ⟨948687078732996869369893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5059664419909316636639429 948687078732996869369893)
                ·
                  refine ⟨177878827262436913006855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 948687078732996869369893 177878827262436913006855)
                  ·
                    rfl

theorem cell22_1558880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 4].length) (baseStart_1558880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558880 prefixEnd_1558880 := by exact prefixLift 1558880
  have htrace : WordTrace (prefixWord ++ tailWord_1558880) baseStart_1558880 baseEnd_1558880 := by
    simpa [prefixWord, tailWord_1558880, baseEnd_1558880] using wordTrace_append hprefix tailTrace_1558880
  have hstable : (prefixWord ++ tailWord_1558880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558880).length < 2 ^ (prefixWord ++ tailWord_1558880).sum := by decide
  have hdescent : baseEnd_1558880 < baseStart_1558880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558914 : List Nat := [3, 4, 2, 1, 2, 1, 2, 3, 4]
def baseStart_1558914 : Nat := 118140960795 + 1558914 * 2 ^ 59
def prefixEnd_1558914 : Nat := 4983230072969 + 3 ^ 40 * 1558914 * 2
def baseEnd_1558914 : Nat := 177882706894048661223487

theorem tailTrace_1558914 : CollatzResearch.WordTrace tailWord_1558914 prefixEnd_1558914 177882706894048661223487 := by
  unfold tailWord_1558914
  simp only [CollatzResearch.WordTrace]
  refine ⟨14214566168582073539938949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37905509782885529439837197 14214566168582073539938949)
  ·
    refine ⟨2665231156609138788738553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14214566168582073539938949 2665231156609138788738553)
    ·
      refine ⟨1998923367456854091553915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2665231156609138788738553 1998923367456854091553915)
      ·
        refine ⟨2998385051185281137330873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1998923367456854091553915 2998385051185281137330873)
        ·
          refine ⟨2248788788388960852998155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2998385051185281137330873 2248788788388960852998155)
          ·
            refine ⟨3373183182583441279497233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248788788388960852998155 3373183182583441279497233)
            ·
              refine ⟨2529887386937580959622925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3373183182583441279497233 2529887386937580959622925)
              ·
                refine ⟨948707770101592859858597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2529887386937580959622925 948707770101592859858597)
                ·
                  refine ⟨177882706894048661223487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 948707770101592859858597 177882706894048661223487)
                  ·
                    rfl

theorem cell22_1558914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_1558914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1558914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1558914 prefixEnd_1558914 := by exact prefixLift 1558914
  have htrace : WordTrace (prefixWord ++ tailWord_1558914) baseStart_1558914 baseEnd_1558914 := by
    simpa [prefixWord, tailWord_1558914, baseEnd_1558914] using wordTrace_append hprefix tailTrace_1558914
  have hstable : (prefixWord ++ tailWord_1558914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558914).length < 2 ^ (prefixWord ++ tailWord_1558914).sum := by decide
  have hdescent : baseEnd_1558914 < baseStart_1558914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559030 : List Nat := [5, 1, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_1559030 : Nat := 118140960795 + 1559030 * 2 ^ 59
def prefixEnd_1559030 : Nat := 4983230072969 + 3 ^ 40 * 1559030 * 2
def baseEnd_1559030 : Nat := 533687829852760347770105

theorem tailTrace_1559030 : CollatzResearch.WordTrace tailWord_1559030 prefixEnd_1559030 533687829852760347770105 := by
  unfold tailWord_1559030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3553905971369252873186159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37908330361272030647319029 3553905971369252873186159)
  ·
    refine ⟨5330858957053879309779239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3553905971369252873186159 5330858957053879309779239)
    ·
      refine ⟨7996288435580818964668859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5330858957053879309779239 7996288435580818964668859)
      ·
        refine ⟨11994432653371228447003289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7996288435580818964668859 11994432653371228447003289)
        ·
          refine ⟨8995824490028421335252467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11994432653371228447003289 8995824490028421335252467)
          ·
            refine ⟨13493736735042632002878701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8995824490028421335252467 13493736735042632002878701)
            ·
              refine ⟨5060151275640987001079513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13493736735042632002878701 5060151275640987001079513)
              ·
                refine ⟨3795113456730740250809635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5060151275640987001079513 3795113456730740250809635)
                ·
                  refine ⟨5692670185096110376214453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3795113456730740250809635 5692670185096110376214453)
                  ·
                    refine ⟨533687829852760347770105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5692670185096110376214453 533687829852760347770105)
                    ·
                      rfl

theorem cell22_1559030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_1559030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559030 prefixEnd_1559030 := by exact prefixLift 1559030
  have htrace : WordTrace (prefixWord ++ tailWord_1559030) baseStart_1559030 baseEnd_1559030 := by
    simpa [prefixWord, tailWord_1559030, baseEnd_1559030] using wordTrace_append hprefix tailTrace_1559030
  have hstable : (prefixWord ++ tailWord_1559030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559030).length < 2 ^ (prefixWord ++ tailWord_1559030).sum := by decide
  have hdescent : baseEnd_1559030 < baseStart_1559030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559073 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 2, 6]
def baseStart_1559073 : Nat := 118140960795 + 1559073 * 2 ^ 59
def prefixEnd_1559073 : Nat := 4983230072969 + 3 ^ 40 * 1559073 * 2
def baseEnd_1559073 : Nat := 533702549631522568944973

theorem tailTrace_1559073 : CollatzResearch.WordTrace tailWord_1559073 prefixEnd_1559073 533702549631522568944973 := by
  unfold tailWord_1559073
  simp only [CollatzResearch.WordTrace]
  refine ⟨56864063880752264314793873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37909375920501509543195915 56864063880752264314793873)
  ·
    refine ⟨42648047910564198236095405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56864063880752264314793873 42648047910564198236095405)
    ·
      refine ⟨15993017966461574338535777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42648047910564198236095405 15993017966461574338535777)
      ·
        refine ⟨11994763474846180753901833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15993017966461574338535777 11994763474846180753901833)
        ·
          refine ⟨8996072606134635565426375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11994763474846180753901833 8996072606134635565426375)
          ·
            refine ⟨13494108909201953348139563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8996072606134635565426375 13494108909201953348139563)
            ·
              refine ⟨20241163363802930022209345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13494108909201953348139563 20241163363802930022209345)
              ·
                refine ⟨15180872522852197516657009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20241163363802930022209345 15180872522852197516657009)
                ·
                  refine ⟨11385654392139148137492757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15180872522852197516657009 11385654392139148137492757)
                  ·
                    refine ⟨533702549631522568944973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11385654392139148137492757 533702549631522568944973)
                    ·
                      rfl

theorem cell22_1559073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_1559073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559073 prefixEnd_1559073 := by exact prefixLift 1559073
  have htrace : WordTrace (prefixWord ++ tailWord_1559073) baseStart_1559073 baseEnd_1559073 := by
    simpa [prefixWord, tailWord_1559073, baseEnd_1559073] using wordTrace_append hprefix tailTrace_1559073
  have hstable : (prefixWord ++ tailWord_1559073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559073).length < 2 ^ (prefixWord ++ tailWord_1559073).sum := by decide
  have hdescent : baseEnd_1559073 < baseStart_1559073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559075 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 5, 3]
def baseStart_1559075 : Nat := 118140960795 + 1559075 * 2 ^ 59
def prefixEnd_1559075 : Nat := 4983230072969 + 3 ^ 40 * 1559075 * 2
def baseEnd_1559075 : Nat := 533703234272395230394967

theorem tailTrace_1559075 : CollatzResearch.WordTrace tailWord_1559075 prefixEnd_1559075 533703234272395230394967 := by
  unfold tailWord_1559075
  simp only [CollatzResearch.WordTrace]
  refine ⟨56864136826745018656366679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37909424551163345770911119 56864136826745018656366679)
  ·
    refine ⟨85296205240117527984550019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56864136826745018656366679 85296205240117527984550019)
    ·
      refine ⟨127944307860176291976825029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85296205240117527984550019 127944307860176291976825029)
      ·
        refine ⟨23989557723783054745654693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127944307860176291976825029 23989557723783054745654693)
        ·
          refine ⟨4498042073209322764810255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23989557723783054745654693 4498042073209322764810255)
          ·
            refine ⟨6747063109813984147215383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4498042073209322764810255 6747063109813984147215383)
            ·
              refine ⟨10120594664720976220823075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6747063109813984147215383 10120594664720976220823075)
              ·
                refine ⟨15180891997081464331234613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10120594664720976220823075 15180891997081464331234613)
                ·
                  refine ⟨1423208624726387281053245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15180891997081464331234613 1423208624726387281053245)
                  ·
                    refine ⟨533703234272395230394967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1423208624726387281053245 533703234272395230394967)
                    ·
                      rfl

theorem cell22_1559075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 3].length) (baseStart_1559075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559075 prefixEnd_1559075 := by exact prefixLift 1559075
  have htrace : WordTrace (prefixWord ++ tailWord_1559075) baseStart_1559075 baseEnd_1559075 := by
    simpa [prefixWord, tailWord_1559075, baseEnd_1559075] using wordTrace_append hprefix tailTrace_1559075
  have hstable : (prefixWord ++ tailWord_1559075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559075).length < 2 ^ (prefixWord ++ tailWord_1559075).sum := by decide
  have hdescent : baseEnd_1559075 < baseStart_1559075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559085 : List Nat := [1, 5, 4, 1, 2, 1, 2, 1, 1, 4]
def baseStart_1559085 : Nat := 118140960795 + 1559085 * 2 ^ 59
def prefixEnd_1559085 : Nat := 4983230072969 + 3 ^ 40 * 1559085 * 2
def baseEnd_1559085 : Nat := 533706657476758537644937

theorem tailTrace_1559085 : CollatzResearch.WordTrace tailWord_1559085 prefixEnd_1559085 533706657476758537644937 := by
  unfold tailWord_1559085
  simp only [CollatzResearch.WordTrace]
  refine ⟨56864501556708790364230709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37909667704472526909487139 56864501556708790364230709)
  ·
    refine ⟨5331047020941449096646629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56864501556708790364230709 5331047020941449096646629)
    ·
      refine ⟨999571316426521705621243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5331047020941449096646629 999571316426521705621243)
      ·
        refine ⟨1499356974639782558431865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 999571316426521705621243 1499356974639782558431865)
        ·
          refine ⟨1124517730979836918823899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1499356974639782558431865 1124517730979836918823899)
          ·
            refine ⟨1686776596469755378235849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124517730979836918823899 1686776596469755378235849)
            ·
              refine ⟨1265082447352316533676887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1686776596469755378235849 1265082447352316533676887)
              ·
                refine ⟨1897623671028474800515331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1265082447352316533676887 1897623671028474800515331)
                ·
                  refine ⟨2846435506542712200772997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1897623671028474800515331 2846435506542712200772997)
                  ·
                    refine ⟨533706657476758537644937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2846435506542712200772997 533706657476758537644937)
                    ·
                      rfl

theorem cell22_1559085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_1559085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559085 prefixEnd_1559085 := by exact prefixLift 1559085
  have htrace : WordTrace (prefixWord ++ tailWord_1559085) baseStart_1559085 baseEnd_1559085 := by
    simpa [prefixWord, tailWord_1559085, baseEnd_1559085] using wordTrace_append hprefix tailTrace_1559085
  have hstable : (prefixWord ++ tailWord_1559085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559085).length < 2 ^ (prefixWord ++ tailWord_1559085).sum := by decide
  have hdescent : baseEnd_1559085 < baseStart_1559085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559103 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 4, 5]
def baseStart_1559103 : Nat := 118140960795 + 1559103 * 2 ^ 59
def prefixEnd_1559103 : Nat := 4983230072969 + 3 ^ 40 * 1559103 * 2
def baseEnd_1559103 : Nat := 533712819244612490694881

theorem tailTrace_1559103 : CollatzResearch.WordTrace tailWord_1559103 prefixEnd_1559103 533712819244612490694881 := by
  unfold tailWord_1559103
  simp only [CollatzResearch.WordTrace]
  refine ⟨56865158070643579438385963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37910105380429052958923975 56865158070643579438385963)
  ·
    refine ⟨85297737105965369157578945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56865158070643579438385963 85297737105965369157578945)
    ·
      refine ⟨63973302829474026868184209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85297737105965369157578945 63973302829474026868184209)
      ·
        refine ⟨47979977122105520151138157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63973302829474026868184209 47979977122105520151138157)
        ·
          refine ⟨17992491420789570056676809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47979977122105520151138157 17992491420789570056676809)
          ·
            refine ⟨13494368565592177542507607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17992491420789570056676809 13494368565592177542507607)
            ·
              refine ⟨20241552848388266313761411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13494368565592177542507607 20241552848388266313761411)
              ·
                refine ⟨30362329272582399470642117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20241552848388266313761411 30362329272582399470642117)
                ·
                  refine ⟨5692936738609199900745397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30362329272582399470642117 5692936738609199900745397)
                  ·
                    refine ⟨533712819244612490694881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5692936738609199900745397 533712819244612490694881)
                    ·
                      rfl

theorem cell22_1559103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_1559103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559103 prefixEnd_1559103 := by exact prefixLift 1559103
  have htrace : WordTrace (prefixWord ++ tailWord_1559103) baseStart_1559103 baseEnd_1559103 := by
    simpa [prefixWord, tailWord_1559103, baseEnd_1559103] using wordTrace_append hprefix tailTrace_1559103
  have hstable : (prefixWord ++ tailWord_1559103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559103).length < 2 ^ (prefixWord ++ tailWord_1559103).sum := by decide
  have hdescent : baseEnd_1559103 < baseStart_1559103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559105 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 7]
def baseStart_1559105 : Nat := 118140960795 + 1559105 * 2 ^ 59
def prefixEnd_1559105 : Nat := 4983230072969 + 3 ^ 40 * 1559105 * 2
def baseEnd_1559105 : Nat := 177904501295161717381625

theorem tailTrace_1559105 : CollatzResearch.WordTrace tailWord_1559105 prefixEnd_1559105 177904501295161717381625 := by
  unfold tailWord_1559105
  simp only [CollatzResearch.WordTrace]
  refine ⟨56865231016636333779958769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37910154011090889186639179 56865231016636333779958769)
  ·
    refine ⟨42648923262477250334969077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56865231016636333779958769 42648923262477250334969077)
    ·
      refine ⟨3998336555857242218903351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42648923262477250334969077 3998336555857242218903351)
      ·
        refine ⟨5997504833785863328355027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3998336555857242218903351 5997504833785863328355027)
        ·
          refine ⟨8996257250678794992532541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5997504833785863328355027 8996257250678794992532541)
          ·
            refine ⟨3373596469004548122199703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8996257250678794992532541 3373596469004548122199703)
            ·
              refine ⟨5060394703506822183299555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3373596469004548122199703 5060394703506822183299555)
              ·
                refine ⟨7590592055260233274949333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5060394703506822183299555 7590592055260233274949333)
                ·
                  refine ⟨177904501295161717381625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7590592055260233274949333 177904501295161717381625)
                  ·
                    rfl

theorem cell22_1559105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 7].length) (baseStart_1559105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559105 prefixEnd_1559105 := by exact prefixLift 1559105
  have htrace : WordTrace (prefixWord ++ tailWord_1559105) baseStart_1559105 baseEnd_1559105 := by
    simpa [prefixWord, tailWord_1559105, baseEnd_1559105] using wordTrace_append hprefix tailTrace_1559105
  have hstable : (prefixWord ++ tailWord_1559105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559105).length < 2 ^ (prefixWord ++ tailWord_1559105).sum := by decide
  have hdescent : baseEnd_1559105 < baseStart_1559105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559122 : List Nat := [3, 2, 2, 1, 2, 1, 5, 1, 5]
def baseStart_1559122 : Nat := 118140960795 + 1559122 * 2 ^ 59
def prefixEnd_1559122 : Nat := 4983230072969 + 3 ^ 40 * 1559122 * 2
def baseEnd_1559122 : Nat := 177906441110967591489941

theorem tailTrace_1559122 : CollatzResearch.WordTrace tailWord_1559122 prefixEnd_1559122 177906441110967591489941 := by
  unfold tailWord_1559122
  simp only [CollatzResearch.WordTrace]
  refine ⟨14216462764393686420831905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37910567371716497122218413 14216462764393686420831905)
  ·
    refine ⟨10662347073295264815623929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14216462764393686420831905 10662347073295264815623929)
    ·
      refine ⟨7996760304971448611717947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10662347073295264815623929 7996760304971448611717947)
      ·
        refine ⟨11995140457457172917576921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7996760304971448611717947 11995140457457172917576921)
        ·
          refine ⟨8996355343092879688182691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11995140457457172917576921 8996355343092879688182691)
          ·
            refine ⟨13494533014639319532274037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8996355343092879688182691 13494533014639319532274037)
            ·
              refine ⟨1265112470122436206150691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13494533014639319532274037 1265112470122436206150691)
              ·
                refine ⟨1897668705183654309226037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1265112470122436206150691 1897668705183654309226037)
                ·
                  refine ⟨177906441110967591489941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1897668705183654309226037 177906441110967591489941)
                  ·
                    rfl

theorem cell22_1559122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_1559122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559122 prefixEnd_1559122 := by exact prefixLift 1559122
  have htrace : WordTrace (prefixWord ++ tailWord_1559122) baseStart_1559122 baseEnd_1559122 := by
    simpa [prefixWord, tailWord_1559122, baseEnd_1559122] using wordTrace_append hprefix tailTrace_1559122
  have hstable : (prefixWord ++ tailWord_1559122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559122).length < 2 ^ (prefixWord ++ tailWord_1559122).sum := by decide
  have hdescent : baseEnd_1559122 < baseStart_1559122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559163 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 3, 6]
def baseStart_1559163 : Nat := 118140960795 + 1559163 * 2 ^ 59
def prefixEnd_1559163 : Nat := 4983230072969 + 3 ^ 40 * 1559163 * 2
def baseEnd_1559163 : Nat := 533733358470792334194697

theorem tailTrace_1559163 : CollatzResearch.WordTrace tailWord_1559163 prefixEnd_1559163 533733358470792334194697 := by
  unfold tailWord_1559163
  simp only [CollatzResearch.WordTrace]
  refine ⟨56867346450426209685570143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37911564300284139790380095 56867346450426209685570143)
  ·
    refine ⟨85301019675639314528355215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56867346450426209685570143 85301019675639314528355215)
    ·
      refine ⟨127951529513458971792532823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85301019675639314528355215 127951529513458971792532823)
      ·
        refine ⟨191927294270188457688799235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127951529513458971792532823 191927294270188457688799235)
        ·
          refine ⟨287890941405282686533198853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191927294270188457688799235 287890941405282686533198853)
          ·
            refine ⟨53979551513490503724974785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 287890941405282686533198853 53979551513490503724974785)
            ·
              refine ⟨40484663635117877793731089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53979551513490503724974785 40484663635117877793731089)
              ·
                refine ⟨30363497726338408345298317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40484663635117877793731089 30363497726338408345298317)
                ·
                  refine ⟨11386311647376903129486869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30363497726338408345298317 11386311647376903129486869)
                  ·
                    refine ⟨533733358470792334194697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11386311647376903129486869 533733358470792334194697)
                    ·
                      rfl

theorem cell22_1559163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 6].length) (baseStart_1559163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559163 prefixEnd_1559163 := by exact prefixLift 1559163
  have htrace : WordTrace (prefixWord ++ tailWord_1559163) baseStart_1559163 baseEnd_1559163 := by
    simpa [prefixWord, tailWord_1559163, baseEnd_1559163] using wordTrace_append hprefix tailTrace_1559163
  have hstable : (prefixWord ++ tailWord_1559163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559163).length < 2 ^ (prefixWord ++ tailWord_1559163).sum := by decide
  have hdescent : baseEnd_1559163 < baseStart_1559163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559214 : List Nat := [4, 1, 4, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1559214 : Nat := 118140960795 + 1559214 * 2 ^ 59
def prefixEnd_1559214 : Nat := 4983230072969 + 3 ^ 40 * 1559214 * 2
def baseEnd_1559214 : Nat := 533750816813045201169541

theorem tailTrace_1559214 : CollatzResearch.WordTrace tailWord_1559214 prefixEnd_1559214 533750816813045201169541 := by
  unfold tailWord_1559214
  simp only [CollatzResearch.WordTrace]
  refine ⟨7108650821655180674459587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37912804382160963597117797 7108650821655180674459587)
  ·
    refine ⟨10662976232482771011689381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7108650821655180674459587 10662976232482771011689381)
    ·
      refine ⟨1999308043590519564691759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10662976232482771011689381 1999308043590519564691759)
      ·
        refine ⟨2998962065385779347037639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1999308043590519564691759 2998962065385779347037639)
        ·
          refine ⟨4498443098078669020556459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2998962065385779347037639 4498443098078669020556459)
          ·
            refine ⟨6747664647118003530834689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4498443098078669020556459 6747664647118003530834689)
            ·
              refine ⟨5060748485338502648126017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6747664647118003530834689 5060748485338502648126017)
              ·
                refine ⟨3795561364003876986094513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5060748485338502648126017 3795561364003876986094513)
                ·
                  refine ⟨2846671023002907739570885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3795561364003876986094513 2846671023002907739570885)
                  ·
                    refine ⟨533750816813045201169541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2846671023002907739570885 533750816813045201169541)
                    ·
                      rfl

theorem cell22_1559214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1559214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559214 prefixEnd_1559214 := by exact prefixLift 1559214
  have htrace : WordTrace (prefixWord ++ tailWord_1559214) baseStart_1559214 baseEnd_1559214 := by
    simpa [prefixWord, tailWord_1559214, baseEnd_1559214] using wordTrace_append hprefix tailTrace_1559214
  have hstable : (prefixWord ++ tailWord_1559214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559214).length < 2 ^ (prefixWord ++ tailWord_1559214).sum := by decide
  have hdescent : baseEnd_1559214 < baseStart_1559214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559244 : List Nat := [2, 2, 1, 5, 1, 2, 1, 2, 3, 3]
def baseStart_1559244 : Nat := 118140960795 + 1559244 * 2 ^ 59
def prefixEnd_1559244 : Nat := 4983230072969 + 3 ^ 40 * 1559244 * 2
def baseEnd_1559244 : Nat := 533761086426135122919449

theorem tailTrace_1559244 : CollatzResearch.WordTrace tailWord_1559244 prefixEnd_1559244 533761086426135122919449 := by
  unfold tailWord_1559244
  simp only [CollatzResearch.WordTrace]
  refine ⟨28435150381566380259634393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37913533842088507012845857 28435150381566380259634393)
  ·
    refine ⟨21326362786174785194725795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28435150381566380259634393 21326362786174785194725795)
    ·
      refine ⟨31989544179262177792088693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21326362786174785194725795 31989544179262177792088693)
      ·
        refine ⟨2999019766805829168008315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31989544179262177792088693 2999019766805829168008315)
        ·
          refine ⟨4498529650208743752012473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2999019766805829168008315 4498529650208743752012473)
          ·
            refine ⟨3373897237656557814009355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4498529650208743752012473 3373897237656557814009355)
            ·
              refine ⟨5060845856484836721014033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3373897237656557814009355 5060845856484836721014033)
              ·
                refine ⟨3795634392363627540760525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5060845856484836721014033 3795634392363627540760525)
                ·
                  refine ⟨1423362897136360327785197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3795634392363627540760525 1423362897136360327785197)
                  ·
                    refine ⟨533761086426135122919449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1423362897136360327785197 533761086426135122919449)
                    ·
                      rfl

theorem cell22_1559244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_1559244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559244 prefixEnd_1559244 := by exact prefixLift 1559244
  have htrace : WordTrace (prefixWord ++ tailWord_1559244) baseStart_1559244 baseEnd_1559244 := by
    simpa [prefixWord, tailWord_1559244, baseEnd_1559244] using wordTrace_append hprefix tailTrace_1559244
  have hstable : (prefixWord ++ tailWord_1559244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559244).length < 2 ^ (prefixWord ++ tailWord_1559244).sum := by decide
  have hdescent : baseEnd_1559244 < baseStart_1559244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559304 : List Nat := [2, 1, 3, 2, 2, 3, 2, 2, 1, 4]
def baseStart_1559304 : Nat := 118140960795 + 1559304 * 2 ^ 59
def prefixEnd_1559304 : Nat := 4983230072969 + 3 ^ 40 * 1559304 * 2
def baseEnd_1559304 : Nat := 533781625652314966419265

theorem tailTrace_1559304 : CollatzResearch.WordTrace tailWord_1559304 prefixEnd_1559304 533781625652314966419265 := by
  unfold tailWord_1559304
  simp only [CollatzResearch.WordTrace]
  refine ⟨28436244571457695383226483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37914992761943593844301977 28436244571457695383226483)
  ·
    refine ⟨42654366857186543074839725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28436244571457695383226483 42654366857186543074839725)
    ·
      refine ⟨15995387571444953653064897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42654366857186543074839725 15995387571444953653064897)
      ·
        refine ⟨11996540678583715239798673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15995387571444953653064897 11996540678583715239798673)
        ·
          refine ⟨8997405508937786429849005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11996540678583715239798673 8997405508937786429849005)
          ·
            refine ⟨3374027065851669911193377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8997405508937786429849005 3374027065851669911193377)
            ·
              refine ⟨2530520299388752433395033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3374027065851669911193377 2530520299388752433395033)
              ·
                refine ⟨1897890224541564325046275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2530520299388752433395033 1897890224541564325046275)
                ·
                  refine ⟨2846835336812346487569413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1897890224541564325046275 2846835336812346487569413)
                  ·
                    refine ⟨533781625652314966419265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2846835336812346487569413 533781625652314966419265)
                    ·
                      rfl

theorem cell22_1559304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_1559304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559304 prefixEnd_1559304 := by exact prefixLift 1559304
  have htrace : WordTrace (prefixWord ++ tailWord_1559304) baseStart_1559304 baseEnd_1559304 := by
    simpa [prefixWord, tailWord_1559304, baseEnd_1559304] using wordTrace_append hprefix tailTrace_1559304
  have hstable : (prefixWord ++ tailWord_1559304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559304).length < 2 ^ (prefixWord ++ tailWord_1559304).sum := by decide
  have hdescent : baseEnd_1559304 < baseStart_1559304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559315 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 1, 6]
def baseStart_1559315 : Nat := 118140960795 + 1559315 * 2 ^ 59
def prefixEnd_1559315 : Nat := 4983230072969 + 3 ^ 40 * 1559315 * 2
def baseEnd_1559315 : Nat := 533785391177114604394231

theorem tailTrace_1559315 : CollatzResearch.WordTrace tailWord_1559315 prefixEnd_1559315 533785391177114604394231 := by
  unfold tailWord_1559315
  simp only [CollatzResearch.WordTrace]
  refine ⟨56872890345875539645103399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37915260230583693096735599 56872890345875539645103399)
  ·
    refine ⟨85309335518813309467655099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56872890345875539645103399 85309335518813309467655099)
    ·
      refine ⟨127964003278219964201482649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85309335518813309467655099 127964003278219964201482649)
      ·
        refine ⟨95973002458664973151111987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127964003278219964201482649 95973002458664973151111987)
        ·
          refine ⟨143959503687997459726667981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95973002458664973151111987 143959503687997459726667981)
          ·
            refine ⟨53984813882999047397500493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143959503687997459726667981 53984813882999047397500493)
            ·
              refine ⟨20244305206124642774062685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53984813882999047397500493 20244305206124642774062685)
              ·
                refine ⟨7591614452296741040273507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20244305206124642774062685 7591614452296741040273507)
                ·
                  refine ⟨11387421678445111560410261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7591614452296741040273507 11387421678445111560410261)
                  ·
                    refine ⟨533785391177114604394231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11387421678445111560410261 533785391177114604394231)
                    ·
                      rfl

theorem cell22_1559315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 6].length) (baseStart_1559315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559315 prefixEnd_1559315 := by exact prefixLift 1559315
  have htrace : WordTrace (prefixWord ++ tailWord_1559315) baseStart_1559315 baseEnd_1559315 := by
    simpa [prefixWord, tailWord_1559315, baseEnd_1559315] using wordTrace_append hprefix tailTrace_1559315
  have hstable : (prefixWord ++ tailWord_1559315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559315).length < 2 ^ (prefixWord ++ tailWord_1559315).sum := by decide
  have hdescent : baseEnd_1559315 < baseStart_1559315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559317 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 6, 3]
def baseStart_1559317 : Nat := 118140960795 + 1559317 * 2 ^ 59
def prefixEnd_1559317 : Nat := 4983230072969 + 3 ^ 40 * 1559317 * 2
def baseEnd_1559317 : Nat := 533786075817987265844225

theorem tailTrace_1559317 : CollatzResearch.WordTrace tailWord_1559317 prefixEnd_1559317 533786075817987265844225 := by
  unfold tailWord_1559317
  simp only [CollatzResearch.WordTrace]
  refine ⟨56872963291868293986676205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37915308861245529324450803 56872963291868293986676205)
  ·
    refine ⟨21327361234450610245003577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56872963291868293986676205 21327361234450610245003577)
    ·
      refine ⟨15995520925837957683752683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21327361234450610245003577 15995520925837957683752683)
      ·
        refine ⟨23993281388756936525629025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15995520925837957683752683 23993281388756936525629025)
        ·
          refine ⟨17994961041567702394221769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23993281388756936525629025 17994961041567702394221769)
          ·
            refine ⟨13496220781175776795666327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17994961041567702394221769 13496220781175776795666327)
            ·
              refine ⟨20244331171763665193499491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13496220781175776795666327 20244331171763665193499491)
              ·
                refine ⟨30366496757645497790249237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20244331171763665193499491 30366496757645497790249237)
                ·
                  refine ⟨1423429535514632708917933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30366496757645497790249237 1423429535514632708917933)
                  ·
                    refine ⟨533786075817987265844225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1423429535514632708917933 533786075817987265844225)
                    ·
                      rfl

theorem cell22_1559317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_1559317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559317 prefixEnd_1559317 := by exact prefixLift 1559317
  have htrace : WordTrace (prefixWord ++ tailWord_1559317) baseStart_1559317 baseEnd_1559317 := by
    simpa [prefixWord, tailWord_1559317, baseEnd_1559317] using wordTrace_append hprefix tailTrace_1559317
  have hstable : (prefixWord ++ tailWord_1559317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559317).length < 2 ^ (prefixWord ++ tailWord_1559317).sum := by decide
  have hdescent : baseEnd_1559317 < baseStart_1559317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559336 : List Nat := [2, 1, 5, 1, 1, 1, 5, 2, 4]
def baseStart_1559336 : Nat := 118140960795 + 1559336 * 2 ^ 59
def prefixEnd_1559336 : Nat := 4983230072969 + 3 ^ 40 * 1559336 * 2
def baseEnd_1559336 : Nat := 177930859968759183206389

theorem tailTrace_1559336 : CollatzResearch.WordTrace tailWord_1559336 prefixEnd_1559336 177930859968759183206389 := by
  unfold tailWord_1559336
  simp only [CollatzResearch.WordTrace]
  refine ⟨28436828139399730115808931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37915770852532973487745241 28436828139399730115808931)
  ·
    refine ⟨42655242209099595173713397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28436828139399730115808931 42655242209099595173713397)
    ·
      refine ⟨3998928957103087047535631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42655242209099595173713397 3998928957103087047535631)
      ·
        refine ⟨5998393435654630571303447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3998928957103087047535631 5998393435654630571303447)
        ·
          refine ⟨8997590153481945856955171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5998393435654630571303447 8997590153481945856955171)
          ·
            refine ⟨13496385230222918785432757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8997590153481945856955171 13496385230222918785432757)
            ·
              refine ⟨1265286115333398636134321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13496385230222918785432757 1265286115333398636134321)
              ·
                refine ⟨948964586500048977100741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1265286115333398636134321 948964586500048977100741)
                ·
                  refine ⟨177930859968759183206389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 948964586500048977100741 177930859968759183206389)
                  ·
                    rfl

theorem cell22_1559336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 4].length) (baseStart_1559336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559336 prefixEnd_1559336 := by exact prefixLift 1559336
  have htrace : WordTrace (prefixWord ++ tailWord_1559336) baseStart_1559336 baseEnd_1559336 := by
    simpa [prefixWord, tailWord_1559336, baseEnd_1559336] using wordTrace_append hprefix tailTrace_1559336
  have hstable : (prefixWord ++ tailWord_1559336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559336).length < 2 ^ (prefixWord ++ tailWord_1559336).sum := by decide
  have hdescent : baseEnd_1559336 < baseStart_1559336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559347 : List Nat := [1, 1, 1, 2, 6, 2, 2, 7]
def baseStart_1559347 : Nat := 118140960795 + 1559347 * 2 ^ 59
def prefixEnd_1559347 : Nat := 4983230072969 + 3 ^ 40 * 1559347 * 2
def baseEnd_1559347 : Nat := 59310705047897465288237

theorem tailTrace_1559347 : CollatzResearch.WordTrace tailWord_1559347 prefixEnd_1559347 59310705047897465288237 := by
  unfold tailWord_1559347
  simp only [CollatzResearch.WordTrace]
  refine ⟨56874057481759609110268295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37916038321173072740178863 56874057481759609110268295)
  ·
    refine ⟨85311086222639413665402443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56874057481759609110268295 85311086222639413665402443)
    ·
      refine ⟨127966629333959120498103665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85311086222639413665402443 127966629333959120498103665)
      ·
        refine ⟨95974972000469340373577749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127966629333959120498103665 95974972000469340373577749)
        ·
          refine ⟨4498826812522000330011457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95974972000469340373577749 4498826812522000330011457)
          ·
            refine ⟨3374120109391500247508593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4498826812522000330011457 3374120109391500247508593)
            ·
              refine ⟨2530590082043625185631445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3374120109391500247508593 2530590082043625185631445)
              ·
                refine ⟨59310705047897465288237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2530590082043625185631445 59310705047897465288237)
                ·
                  rfl

theorem cell22_1559347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 7].length) (baseStart_1559347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559347 prefixEnd_1559347 := by exact prefixLift 1559347
  have htrace : WordTrace (prefixWord ++ tailWord_1559347) baseStart_1559347 baseEnd_1559347 := by
    simpa [prefixWord, tailWord_1559347, baseEnd_1559347] using wordTrace_append hprefix tailTrace_1559347
  have hstable : (prefixWord ++ tailWord_1559347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559347).length < 2 ^ (prefixWord ++ tailWord_1559347).sum := by decide
  have hdescent : baseEnd_1559347 < baseStart_1559347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559467 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 4, 4]
def baseStart_1559467 : Nat := 118140960795 + 1559467 * 2 ^ 59
def prefixEnd_1559467 : Nat := 4983230072969 + 3 ^ 40 * 1559467 * 2
def baseEnd_1559467 : Nat := 533837423883436874593765

theorem tailTrace_1559467 : CollatzResearch.WordTrace tailWord_1559467 prefixEnd_1559467 533837423883436874593765 := by
  unfold tailWord_1559467
  simp only [CollatzResearch.WordTrace]
  refine ⟨56878434241324869604636655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37918956160883246403091103 56878434241324869604636655)
  ·
    refine ⟨85317651361987304406954983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56878434241324869604636655 85317651361987304406954983)
    ·
      refine ⟨127976477042980956610432475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85317651361987304406954983 127976477042980956610432475)
      ·
        refine ⟨191964715564471434915648713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127976477042980956610432475 191964715564471434915648713)
        ·
          refine ⟨143973536673353576186736535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191964715564471434915648713 143973536673353576186736535)
          ·
            refine ⟨215960305010030364280104803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143973536673353576186736535 215960305010030364280104803)
            ·
              refine ⟨323940457515045546420157205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215960305010030364280104803 323940457515045546420157205)
              ·
                refine ⟨15184708946017759988444869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 323940457515045546420157205 15184708946017759988444869)
                ·
                  refine ⟨2847132927378329997833413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15184708946017759988444869 2847132927378329997833413)
                  ·
                    refine ⟨533837423883436874593765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2847132927378329997833413 533837423883436874593765)
                    ·
                      rfl

theorem cell22_1559467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 4].length) (baseStart_1559467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559467 prefixEnd_1559467 := by exact prefixLift 1559467
  have htrace : WordTrace (prefixWord ++ tailWord_1559467) baseStart_1559467 baseEnd_1559467 := by
    simpa [prefixWord, tailWord_1559467, baseEnd_1559467] using wordTrace_append hprefix tailTrace_1559467
  have hstable : (prefixWord ++ tailWord_1559467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559467).length < 2 ^ (prefixWord ++ tailWord_1559467).sum := by decide
  have hdescent : baseEnd_1559467 < baseStart_1559467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559482 : List Nat := [3, 1, 1, 1, 2, 1, 5, 8]
def baseStart_1559482 : Nat := 118140960795 + 1559482 * 2 ^ 59
def prefixEnd_1559482 : Nat := 4983230072969 + 3 ^ 40 * 1559482 * 2
def baseEnd_1559482 : Nat := 59315839854442426163191

theorem tailTrace_1559482 : CollatzResearch.WordTrace tailWord_1559482 prefixEnd_1559482 59315839854442426163191 := by
  unfold tailWord_1559482
  simp only [CollatzResearch.WordTrace]
  refine ⟨14219745334067631791608175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37919320890847018110955133 14219745334067631791608175)
  ·
    refine ⟨21329618001101447687412263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14219745334067631791608175 21329618001101447687412263)
    ·
      refine ⟨31994427001652171531118395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21329618001101447687412263 31994427001652171531118395)
      ·
        refine ⟨47991640502478257296677593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31994427001652171531118395 47991640502478257296677593)
        ·
          refine ⟨35993730376858692972508195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47991640502478257296677593 35993730376858692972508195)
          ·
            refine ⟨53990595565288039458762293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35993730376858692972508195 53990595565288039458762293)
            ·
              refine ⟨5061618334245753699258965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53990595565288039458762293 5061618334245753699258965)
              ·
                refine ⟨59315839854442426163191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5061618334245753699258965 59315839854442426163191)
                ·
                  rfl

theorem cell22_1559482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 8].length) (baseStart_1559482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559482 prefixEnd_1559482 := by exact prefixLift 1559482
  have htrace : WordTrace (prefixWord ++ tailWord_1559482) baseStart_1559482 baseEnd_1559482 := by
    simpa [prefixWord, tailWord_1559482, baseEnd_1559482] using wordTrace_append hprefix tailTrace_1559482
  have hstable : (prefixWord ++ tailWord_1559482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559482).length < 2 ^ (prefixWord ++ tailWord_1559482).sum := by decide
  have hdescent : baseEnd_1559482 < baseStart_1559482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559559 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 2, 5]
def baseStart_1559559 : Nat := 118140960795 + 1559559 * 2 ^ 59
def prefixEnd_1559559 : Nat := 4983230072969 + 3 ^ 40 * 1559559 * 2
def baseEnd_1559559 : Nat := 533868917363579301293483

theorem tailTrace_1559559 : CollatzResearch.WordTrace tailWord_1559559 prefixEnd_1559559 533868917363579301293483 := by
  unfold tailWord_1559559
  simp only [CollatzResearch.WordTrace]
  refine ⟨56881789756991569316985731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37921193171327712877990487 56881789756991569316985731)
  ·
    refine ⟨85322684635487353975478597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56881789756991569316985731 85322684635487353975478597)
    ·
      refine ⟨15998003369153878870402237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85322684635487353975478597 15998003369153878870402237)
      ·
        refine ⟨5999251263432704576400839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15998003369153878870402237 5999251263432704576400839)
        ·
          refine ⟨8998876895149056864601259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5999251263432704576400839 8998876895149056864601259)
          ·
            refine ⟨13498315342723585296901889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8998876895149056864601259 13498315342723585296901889)
            ·
              refine ⟨10123736507042688972676417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13498315342723585296901889 10123736507042688972676417)
              ·
                refine ⟨7592802380282016729507313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10123736507042688972676417 7592802380282016729507313)
                ·
                  refine ⟨5694601785211512547130485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7592802380282016729507313 5694601785211512547130485)
                  ·
                    refine ⟨533868917363579301293483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5694601785211512547130485 533868917363579301293483)
                    ·
                      rfl

theorem cell22_1559559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_1559559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559559 prefixEnd_1559559 := by exact prefixLift 1559559
  have htrace : WordTrace (prefixWord ++ tailWord_1559559) baseStart_1559559 baseEnd_1559559 := by
    simpa [prefixWord, tailWord_1559559, baseEnd_1559559] using wordTrace_append hprefix tailTrace_1559559
  have hstable : (prefixWord ++ tailWord_1559559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559559).length < 2 ^ (prefixWord ++ tailWord_1559559).sum := by decide
  have hdescent : baseEnd_1559559 < baseStart_1559559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559589 : List Nat := [1, 3, 1, 2, 2, 2, 3, 2, 6]
def baseStart_1559589 : Nat := 118140960795 + 1559589 * 2 ^ 59
def prefixEnd_1559589 : Nat := 4983230072969 + 3 ^ 40 * 1559589 * 2
def baseEnd_1559589 : Nat := 177959728992223074347797

theorem tailTrace_1559589 : CollatzResearch.WordTrace tailWord_1559589 prefixEnd_1559589 177959728992223074347797 := by
  unfold tailWord_1559589
  simp only [CollatzResearch.WordTrace]
  refine ⟨56882883946882884440577821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37921922631255256293718547 56882883946882884440577821)
  ·
    refine ⟨21331081480081081665216683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56882883946882884440577821 21331081480081081665216683)
    ·
      refine ⟨31996622220121622497825025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21331081480081081665216683 31996622220121622497825025)
      ·
        refine ⟨23997466665091216873368769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31996622220121622497825025 23997466665091216873368769)
        ·
          refine ⟨17998099998818412655026577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23997466665091216873368769 17998099998818412655026577)
          ·
            refine ⟨13498574999113809491269933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17998099998818412655026577 13498574999113809491269933)
            ·
              refine ⟨5061965624667678559226225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13498574999113809491269933 5061965624667678559226225)
              ·
                refine ⟨3796474218500758919419669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5061965624667678559226225 3796474218500758919419669)
                ·
                  refine ⟨177959728992223074347797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3796474218500758919419669 177959728992223074347797)
                  ·
                    rfl

theorem cell22_1559589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_1559589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559589 prefixEnd_1559589 := by exact prefixLift 1559589
  have htrace : WordTrace (prefixWord ++ tailWord_1559589) baseStart_1559589 baseEnd_1559589 := by
    simpa [prefixWord, tailWord_1559589, baseEnd_1559589] using wordTrace_append hprefix tailTrace_1559589
  have hstable : (prefixWord ++ tailWord_1559589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559589).length < 2 ^ (prefixWord ++ tailWord_1559589).sum := by decide
  have hdescent : baseEnd_1559589 < baseStart_1559589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559608 : List Nat := [2, 1, 2, 1, 5, 1, 4, 1, 1, 4]
def baseStart_1559608 : Nat := 118140960795 + 1559608 * 2 ^ 59
def prefixEnd_1559608 : Nat := 4983230072969 + 3 ^ 40 * 1559608 * 2
def baseEnd_1559608 : Nat := 533885691064959506818333

theorem tailTrace_1559608 : CollatzResearch.WordTrace tailWord_1559608 prefixEnd_1559608 533885691064959506818333 := by
  unfold tailWord_1559608
  simp only [CollatzResearch.WordTrace]
  refine ⟨28441788466907025342759739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37922384622542700457012985 28441788466907025342759739)
  ·
    refine ⟨42662682700360538014139609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28441788466907025342759739 42662682700360538014139609)
    ·
      refine ⟨31997012025270403510604707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42662682700360538014139609 31997012025270403510604707)
      ·
        refine ⟨47995518037905605265907061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31997012025270403510604707 47995518037905605265907061)
        ·
          refine ⟨4499579816053650493678787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47995518037905605265907061 4499579816053650493678787)
          ·
            refine ⟨6749369724080475740518181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4499579816053650493678787 6749369724080475740518181)
            ·
              refine ⟨1265506823265089201347159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6749369724080475740518181 1265506823265089201347159)
              ·
                refine ⟨1898260234897633802020739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1265506823265089201347159 1898260234897633802020739)
                ·
                  refine ⟨2847390352346450703031109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1898260234897633802020739 2847390352346450703031109)
                  ·
                    refine ⟨533885691064959506818333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2847390352346450703031109 533885691064959506818333)
                    ·
                      rfl

theorem cell22_1559608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 1, 4].length) (baseStart_1559608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559608 prefixEnd_1559608 := by exact prefixLift 1559608
  have htrace : WordTrace (prefixWord ++ tailWord_1559608) baseStart_1559608 baseEnd_1559608 := by
    simpa [prefixWord, tailWord_1559608, baseEnd_1559608] using wordTrace_append hprefix tailTrace_1559608
  have hstable : (prefixWord ++ tailWord_1559608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559608).length < 2 ^ (prefixWord ++ tailWord_1559608).sum := by decide
  have hdescent : baseEnd_1559608 < baseStart_1559608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559619 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 4, 4]
def baseStart_1559619 : Nat := 118140960795 + 1559619 * 2 ^ 59
def prefixEnd_1559619 : Nat := 4983230072969 + 3 ^ 40 * 1559619 * 2
def baseEnd_1559619 : Nat := 533889456589759144793299

theorem tailTrace_1559619 : CollatzResearch.WordTrace tailWord_1559619 prefixEnd_1559619 533889456589759144793299 := by
  unfold tailWord_1559619
  simp only [CollatzResearch.WordTrace]
  refine ⟨56883978136774199564169911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37922652091182799709446607 56883978136774199564169911)
  ·
    refine ⟨85325967205161299346254867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56883978136774199564169911 85325967205161299346254867)
    ·
      refine ⟨127988950807741949019382301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85325967205161299346254867 127988950807741949019382301)
      ·
        refine ⟨47995856552903230882268363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127988950807741949019382301 47995856552903230882268363)
        ·
          refine ⟨71993784829354846323402545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47995856552903230882268363 71993784829354846323402545)
          ·
            refine ⟨53995338622016134742551909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71993784829354846323402545 53995338622016134742551909)
            ·
              refine ⟨10124125991628025264228483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53995338622016134742551909 10124125991628025264228483)
              ·
                refine ⟨15186188987442037896342725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10124125991628025264228483 15186188987442037896342725)
                ·
                  refine ⟨2847410435145382105564261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15186188987442037896342725 2847410435145382105564261)
                  ·
                    refine ⟨533889456589759144793299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2847410435145382105564261 533889456589759144793299)
                    ·
                      rfl

theorem cell22_1559619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 4].length) (baseStart_1559619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559619 prefixEnd_1559619 := by exact prefixLift 1559619
  have htrace : WordTrace (prefixWord ++ tailWord_1559619) baseStart_1559619 baseEnd_1559619 := by
    simpa [prefixWord, tailWord_1559619, baseEnd_1559619] using wordTrace_append hprefix tailTrace_1559619
  have hstable : (prefixWord ++ tailWord_1559619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559619).length < 2 ^ (prefixWord ++ tailWord_1559619).sum := by decide
  have hdescent : baseEnd_1559619 < baseStart_1559619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559724 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 10]
def baseStart_1559724 : Nat := 118140960795 + 1559724 * 2 ^ 59
def prefixEnd_1559724 : Nat := 4983230072969 + 3 ^ 40 * 1559724 * 2
def baseEnd_1559724 : Nat := 177975133411857956972659

theorem tailTrace_1559724 : CollatzResearch.WordTrace tailWord_1559724 prefixEnd_1559724 177975133411857956972659 := by
  unfold tailWord_1559724
  simp only [CollatzResearch.WordTrace]
  refine ⟨28443903900696901248371113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37925205200929201664494817 28443903900696901248371113)
  ·
    refine ⟨21332927925522675936278335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28443903900696901248371113 21332927925522675936278335)
    ·
      refine ⟨31999391888284013904417503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21332927925522675936278335 31999391888284013904417503)
      ·
        refine ⟨47999087832426020856626255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31999391888284013904417503 47999087832426020856626255)
        ·
          refine ⟨71998631748639031284939383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47999087832426020856626255 71998631748639031284939383)
          ·
            refine ⟨107997947622958546927409075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71998631748639031284939383 107997947622958546927409075)
            ·
              refine ⟨161996921434437820391113613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107997947622958546927409075 161996921434437820391113613)
              ·
                refine ⟨60748845537914182646667605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161996921434437820391113613 60748845537914182646667605)
                ·
                  refine ⟨177975133411857956972659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 60748845537914182646667605 177975133411857956972659)
                  ·
                    rfl

theorem cell22_1559724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_1559724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559724 prefixEnd_1559724 := by exact prefixLift 1559724
  have htrace : WordTrace (prefixWord ++ tailWord_1559724) baseStart_1559724 baseEnd_1559724 := by
    simpa [prefixWord, tailWord_1559724, baseEnd_1559724] using wordTrace_append hprefix tailTrace_1559724
  have hstable : (prefixWord ++ tailWord_1559724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559724).length < 2 ^ (prefixWord ++ tailWord_1559724).sum := by decide
  have hdescent : baseEnd_1559724 < baseStart_1559724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559758 : List Nat := [4, 1, 1, 1, 5, 1, 1, 2, 6]
def baseStart_1559758 : Nat := 118140960795 + 1559758 * 2 ^ 59
def prefixEnd_1559758 : Nat := 4983230072969 + 3 ^ 40 * 1559758 * 2
def baseEnd_1559758 : Nat := 177979013043469705189291

theorem tailTrace_1559758 : CollatzResearch.WordTrace tailWord_1559758 prefixEnd_1559758 177979013043469705189291 := by
  unfold tailWord_1559758
  simp only [CollatzResearch.WordTrace]
  refine ⟨7111130985408828287934991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37926031922180417535653285 7111130985408828287934991)
  ·
    refine ⟨10666696478113242431902487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7111130985408828287934991 10666696478113242431902487)
    ·
      refine ⟨16000044717169863647853731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10666696478113242431902487 16000044717169863647853731)
      ·
        refine ⟨24000067075754795471780597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16000044717169863647853731 24000067075754795471780597)
        ·
          refine ⟨2250006288352012075479431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24000067075754795471780597 2250006288352012075479431)
          ·
            refine ⟨3375009432528018113219147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2250006288352012075479431 3375009432528018113219147)
            ·
              refine ⟨5062514148792027169828721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3375009432528018113219147 5062514148792027169828721)
              ·
                refine ⟨3796885611594020377371541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5062514148792027169828721 3796885611594020377371541)
                ·
                  refine ⟨177979013043469705189291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3796885611594020377371541 177979013043469705189291)
                  ·
                    rfl

theorem cell22_1559758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_1559758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559758 prefixEnd_1559758 := by exact prefixLift 1559758
  have htrace : WordTrace (prefixWord ++ tailWord_1559758) baseStart_1559758 baseEnd_1559758 := by
    simpa [prefixWord, tailWord_1559758, baseEnd_1559758] using wordTrace_append hprefix tailTrace_1559758
  have hstable : (prefixWord ++ tailWord_1559758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559758).length < 2 ^ (prefixWord ++ tailWord_1559758).sum := by decide
  have hdescent : baseEnd_1559758 < baseStart_1559758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559786 : List Nat := [3, 1, 3, 1, 1, 4, 9]
def baseStart_1559786 : Nat := 118140960795 + 1559786 * 2 ^ 59
def prefixEnd_1559786 : Nat := 4983230072969 + 3 ^ 40 * 1559786 * 2
def baseEnd_1559786 : Nat := 19775800892689865772881

theorem tailTrace_1559786 : CollatzResearch.WordTrace tailWord_1559786 prefixEnd_1559786 19775800892689865772881 := by
  unfold tailWord_1559786
  simp only [CollatzResearch.WordTrace]
  refine ⟨14222517281792296771374803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37926712751446124723666141 14222517281792296771374803)
  ·
    refine ⟨21333775922688445157062205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14222517281792296771374803 21333775922688445157062205)
    ·
      refine ⟨8000165971008166933898327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21333775922688445157062205 8000165971008166933898327)
      ·
        refine ⟨12000248956512250400847491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8000165971008166933898327 12000248956512250400847491)
        ·
          refine ⟨18000373434768375601271237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12000248956512250400847491 18000373434768375601271237)
          ·
            refine ⟨3375070019019070425238357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18000373434768375601271237 3375070019019070425238357)
            ·
              refine ⟨19775800892689865772881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3375070019019070425238357 19775800892689865772881)
              ·
                rfl

theorem cell22_1559786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 9].length) (baseStart_1559786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559786 prefixEnd_1559786 := by exact prefixLift 1559786
  have htrace : WordTrace (prefixWord ++ tailWord_1559786) baseStart_1559786 baseEnd_1559786 := by
    simpa [prefixWord, tailWord_1559786, baseEnd_1559786] using wordTrace_append hprefix tailTrace_1559786
  have hstable : (prefixWord ++ tailWord_1559786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559786).length < 2 ^ (prefixWord ++ tailWord_1559786).sum := by decide
  have hdescent : baseEnd_1559786 < baseStart_1559786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559790 : List Nat := [4, 1, 2, 1, 1, 1, 5, 2, 2, 3]
def baseStart_1559790 : Nat := 118140960795 + 1559790 * 2 ^ 59
def prefixEnd_1559790 : Nat := 4983230072969 + 3 ^ 40 * 1559790 * 2
def baseEnd_1559790 : Nat := 533947993384371698767775

theorem tailTrace_1559790 : CollatzResearch.WordTrace tailWord_1559790 prefixEnd_1559790 533947993384371698767775 := by
  unfold tailWord_1559790
  simp only [CollatzResearch.WordTrace]
  refine ⟨7111276877394336971080603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37926810012769797179096549 7111276877394336971080603)
  ·
    refine ⟨10666915316091505456620905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7111276877394336971080603 10666915316091505456620905)
    ·
      refine ⟨8000186487068629092465679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10666915316091505456620905 8000186487068629092465679)
      ·
        refine ⟨12000279730602943638698519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8000186487068629092465679 12000279730602943638698519)
        ·
          refine ⟨18000419595904415458047779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12000279730602943638698519 18000419595904415458047779)
          ·
            refine ⟨27000629393856623187071669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18000419595904415458047779 27000629393856623187071669)
            ·
              refine ⟨2531309005674058423787969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27000629393856623187071669 2531309005674058423787969)
              ·
                refine ⟨1898481754255543817840977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2531309005674058423787969 1898481754255543817840977)
                ·
                  refine ⟨1423861315691657863380733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1898481754255543817840977 1423861315691657863380733)
                  ·
                    refine ⟨533947993384371698767775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1423861315691657863380733 533947993384371698767775)
                    ·
                      rfl

theorem cell22_1559790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_1559790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559790 prefixEnd_1559790 := by exact prefixLift 1559790
  have htrace : WordTrace (prefixWord ++ tailWord_1559790) baseStart_1559790 baseEnd_1559790 := by
    simpa [prefixWord, tailWord_1559790, baseEnd_1559790] using wordTrace_append hprefix tailTrace_1559790
  have hstable : (prefixWord ++ tailWord_1559790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559790).length < 2 ^ (prefixWord ++ tailWord_1559790).sum := by decide
  have hdescent : baseEnd_1559790 < baseStart_1559790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559826 : List Nat := [3, 2, 4, 2, 2, 1, 1, 3, 4]
def baseStart_1559826 : Nat := 118140960795 + 1559826 * 2 ^ 59
def prefixEnd_1559826 : Nat := 4983230072969 + 3 ^ 40 * 1559826 * 2
def baseEnd_1559826 : Nat := 177986772306693201622555

theorem tailTrace_1559826 : CollatzResearch.WordTrace tailWord_1559826 prefixEnd_1559826 177986772306693201622555 := by
  unfold tailWord_1559826
  simp only [CollatzResearch.WordTrace]
  refine ⟨14222882011756068479238833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37927685364682849277970221 14222882011756068479238833)
  ·
    refine ⟨10667161508817051359429125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14222882011756068479238833 10667161508817051359429125)
    ·
      refine ⟨2000092782903197129892961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10667161508817051359429125 2000092782903197129892961)
      ·
        refine ⟨1500069587177397847419721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2000092782903197129892961 1500069587177397847419721)
        ·
          refine ⟨1125052190383048385564791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1500069587177397847419721 1125052190383048385564791)
          ·
            refine ⟨1687578285574572578347187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125052190383048385564791 1687578285574572578347187)
            ·
              refine ⟨2531367428361858867520781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1687578285574572578347187 2531367428361858867520781)
              ·
                refine ⟨949262785635697075320293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2531367428361858867520781 949262785635697075320293)
                ·
                  refine ⟨177986772306693201622555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 949262785635697075320293 177986772306693201622555)
                  ·
                    rfl

theorem cell22_1559826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_1559826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559826 prefixEnd_1559826 := by exact prefixLift 1559826
  have htrace : WordTrace (prefixWord ++ tailWord_1559826) baseStart_1559826 baseEnd_1559826 := by
    simpa [prefixWord, tailWord_1559826, baseEnd_1559826] using wordTrace_append hprefix tailTrace_1559826
  have hstable : (prefixWord ++ tailWord_1559826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559826).length < 2 ^ (prefixWord ++ tailWord_1559826).sum := by decide
  have hdescent : baseEnd_1559826 < baseStart_1559826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559831 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 9]
def baseStart_1559831 : Nat := 118140960795 + 1559831 * 2 ^ 59
def prefixEnd_1559831 : Nat := 4983230072969 + 3 ^ 40 * 1559831 * 2
def baseEnd_1559831 : Nat := 177987342840753752830883

theorem tailTrace_1559831 : CollatzResearch.WordTrace tailWord_1559831 prefixEnd_1559831 177987342840753752830883 := by
  unfold tailWord_1559831
  simp only [CollatzResearch.WordTrace]
  refine ⟨56891710412006159770887347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37927806941337439847258231 56891710412006159770887347)
  ·
    refine ⟨85337565618009239656331021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56891710412006159770887347 85337565618009239656331021)
    ·
      refine ⟨32001587106753464871124133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85337565618009239656331021 32001587106753464871124133)
      ·
        refine ⟨6000297582516274663335775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32001587106753464871124133 6000297582516274663335775)
        ·
          refine ⟨9000446373774411995003663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6000297582516274663335775 9000446373774411995003663)
          ·
            refine ⟨13500669560661617992505495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9000446373774411995003663 13500669560661617992505495)
            ·
              refine ⟨20251004340992426988758243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13500669560661617992505495 20251004340992426988758243)
              ·
                refine ⟨30376506511488640483137365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20251004340992426988758243 30376506511488640483137365)
                ·
                  refine ⟨177987342840753752830883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30376506511488640483137365 177987342840753752830883)
                  ·
                    rfl

theorem cell22_1559831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 9].length) (baseStart_1559831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559831 prefixEnd_1559831 := by exact prefixLift 1559831
  have htrace : WordTrace (prefixWord ++ tailWord_1559831) baseStart_1559831 baseEnd_1559831 := by
    simpa [prefixWord, tailWord_1559831, baseEnd_1559831] using wordTrace_append hprefix tailTrace_1559831
  have hstable : (prefixWord ++ tailWord_1559831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559831).length < 2 ^ (prefixWord ++ tailWord_1559831).sum := by decide
  have hdescent : baseEnd_1559831 < baseStart_1559831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559848 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 7]
def baseStart_1559848 : Nat := 118140960795 + 1559848 * 2 ^ 59
def prefixEnd_1559848 : Nat := 4983230072969 + 3 ^ 40 * 1559848 * 2
def baseEnd_1559848 : Nat := 177989282656559626939199

theorem tailTrace_1559848 : CollatzResearch.WordTrace tailWord_1559848 prefixEnd_1559848 177989282656559626939199 := by
  unfold tailWord_1559848
  simp only [CollatzResearch.WordTrace]
  refine ⟨28446165226472285837128099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37928220301963047782837465 28446165226472285837128099)
  ·
    refine ⟨42669247839708428755692149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28446165226472285837128099 42669247839708428755692149)
    ·
      refine ⟨4000241984972665195846139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42669247839708428755692149 4000241984972665195846139)
      ·
        refine ⟨6000362977458997793769209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4000241984972665195846139 6000362977458997793769209)
        ·
          refine ⟨4500272233094248345326907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6000362977458997793769209 4500272233094248345326907)
          ·
            refine ⟨6750408349641372517990361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4500272233094248345326907 6750408349641372517990361)
            ·
              refine ⟨5062806262231029388492771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6750408349641372517990361 5062806262231029388492771)
              ·
                refine ⟨7594209393346544082739157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5062806262231029388492771 7594209393346544082739157)
                ·
                  refine ⟨177989282656559626939199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7594209393346544082739157 177989282656559626939199)
                  ·
                    rfl

theorem cell22_1559848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 7].length) (baseStart_1559848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559848 prefixEnd_1559848 := by exact prefixLift 1559848
  have htrace : WordTrace (prefixWord ++ tailWord_1559848) baseStart_1559848 baseEnd_1559848 := by
    simpa [prefixWord, tailWord_1559848, baseEnd_1559848] using wordTrace_append hprefix tailTrace_1559848
  have hstable : (prefixWord ++ tailWord_1559848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559848).length < 2 ^ (prefixWord ++ tailWord_1559848).sum := by decide
  have hdescent : baseEnd_1559848 < baseStart_1559848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559865 : List Nat := [1, 2, 1, 6, 2, 1, 1, 3, 5]
def baseStart_1559865 : Nat := 118140960795 + 1559865 * 2 ^ 59
def prefixEnd_1559865 : Nat := 4983230072969 + 3 ^ 40 * 1559865 * 2
def baseEnd_1559865 : Nat := 177991222472365501047515

theorem tailTrace_1559865 : CollatzResearch.WordTrace tailWord_1559865 prefixEnd_1559865 177991222472365501047515 := by
  unfold tailWord_1559865
  simp only [CollatzResearch.WordTrace]
  refine ⟨56892950493882983577625049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37928633662588655718416699 56892950493882983577625049)
  ·
    refine ⟨42669712870412237683218787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56892950493882983577625049 42669712870412237683218787)
    ·
      refine ⟨64004569305618356524828181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42669712870412237683218787 64004569305618356524828181)
      ·
        refine ⟨3000214186200860462101321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64004569305618356524828181 3000214186200860462101321)
        ·
          refine ⟨2250160639650645346575991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3000214186200860462101321 2250160639650645346575991)
          ·
            refine ⟨3375240959475968019863987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2250160639650645346575991 3375240959475968019863987)
            ·
              refine ⟨5062861439213952029795981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3375240959475968019863987 5062861439213952029795981)
              ·
                refine ⟨1898573039705232011173493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5062861439213952029795981 1898573039705232011173493)
                ·
                  refine ⟨177991222472365501047515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1898573039705232011173493 177991222472365501047515)
                  ·
                    rfl

theorem cell22_1559865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 5].length) (baseStart_1559865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559865 prefixEnd_1559865 := by exact prefixLift 1559865
  have htrace : WordTrace (prefixWord ++ tailWord_1559865) baseStart_1559865 baseEnd_1559865 := by
    simpa [prefixWord, tailWord_1559865, baseEnd_1559865] using wordTrace_append hprefix tailTrace_1559865
  have hstable : (prefixWord ++ tailWord_1559865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559865).length < 2 ^ (prefixWord ++ tailWord_1559865).sum := by decide
  have hdescent : baseEnd_1559865 < baseStart_1559865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559940 : List Nat := [2, 3, 2, 1, 1, 3, 3, 1, 2, 4]
def baseStart_1559940 : Nat := 118140960795 + 1559940 * 2 ^ 59
def prefixEnd_1559940 : Nat := 4983230072969 + 3 ^ 40 * 1559940 * 2
def baseEnd_1559940 : Nat := 533999341449821307517315

theorem tailTrace_1559940 : CollatzResearch.WordTrace tailWord_1559940 prefixEnd_1559940 533999341449821307517315 := by
  unfold tailWord_1559940
  simp only [CollatzResearch.WordTrace]
  refine ⟨28447842984305635693302637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37930457312407514257736849 28447842984305635693302637)
  ·
    refine ⟨10667941119114613384988489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28447842984305635693302637 10667941119114613384988489)
    ·
      refine ⟨8000955839335960038741367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10667941119114613384988489 8000955839335960038741367)
      ·
        refine ⟨12001433759003940058112051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8000955839335960038741367 12001433759003940058112051)
        ·
          refine ⟨18002150638505910087168077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12001433759003940058112051 18002150638505910087168077)
          ·
            refine ⟨6750806489439716282688029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18002150638505910087168077 6750806489439716282688029)
            ·
              refine ⟨2531552433539893606008011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6750806489439716282688029 2531552433539893606008011)
              ·
                refine ⟨3797328650309840409012017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2531552433539893606008011 3797328650309840409012017)
                ·
                  refine ⟨2847996487732380306759013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3797328650309840409012017 2847996487732380306759013)
                  ·
                    refine ⟨533999341449821307517315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2847996487732380306759013 533999341449821307517315)
                    ·
                      rfl

theorem cell22_1559940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_1559940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559940 prefixEnd_1559940 := by exact prefixLift 1559940
  have htrace : WordTrace (prefixWord ++ tailWord_1559940) baseStart_1559940 baseEnd_1559940 := by
    simpa [prefixWord, tailWord_1559940, baseEnd_1559940] using wordTrace_append hprefix tailTrace_1559940
  have hstable : (prefixWord ++ tailWord_1559940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559940).length < 2 ^ (prefixWord ++ tailWord_1559940).sum := by decide
  have hdescent : baseEnd_1559940 < baseStart_1559940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559976 : List Nat := [2, 1, 6, 1, 2, 1, 3, 1, 2, 3]
def baseStart_1559976 : Nat := 118140960795 + 1559976 * 2 ^ 59
def prefixEnd_1559976 : Nat := 4983230072969 + 3 ^ 40 * 1559976 * 2
def baseEnd_1559976 : Nat := 534011664985529213617205

theorem tailTrace_1559976 : CollatzResearch.WordTrace tailWord_1559976 prefixEnd_1559976 534011664985529213617205 := by
  unfold tailWord_1559976
  simp only [CollatzResearch.WordTrace]
  refine ⟨28448499498240424767457891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37931332664320566356610521 28448499498240424767457891)
  ·
    refine ⟨42672749247360637151186837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28448499498240424767457891 42672749247360637151186837)
    ·
      refine ⟨2000285120970029866461883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42672749247360637151186837 2000285120970029866461883)
      ·
        refine ⟨3000427681455044799692825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2000285120970029866461883 3000427681455044799692825)
        ·
          refine ⟨2250320761091283599769619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3000427681455044799692825 2250320761091283599769619)
          ·
            refine ⟨3375481141636925399654429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2250320761091283599769619 3375481141636925399654429)
            ·
              refine ⟨1265805428113847024870411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3375481141636925399654429 1265805428113847024870411)
              ·
                refine ⟨1898708142170770537305617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1265805428113847024870411 1898708142170770537305617)
                ·
                  refine ⟨1424031106628077902979213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1898708142170770537305617 1424031106628077902979213)
                  ·
                    refine ⟨534011664985529213617205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1424031106628077902979213 534011664985529213617205)
                    ·
                      rfl

theorem cell22_1559976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_1559976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559976 prefixEnd_1559976 := by exact prefixLift 1559976
  have htrace : WordTrace (prefixWord ++ tailWord_1559976) baseStart_1559976 baseEnd_1559976 := by
    simpa [prefixWord, tailWord_1559976, baseEnd_1559976] using wordTrace_append hprefix tailTrace_1559976
  have hstable : (prefixWord ++ tailWord_1559976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559976).length < 2 ^ (prefixWord ++ tailWord_1559976).sum := by decide
  have hdescent : baseEnd_1559976 < baseStart_1559976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559983 : List Nat := [1, 1, 2, 1, 2, 2, 1, 7, 5]
def baseStart_1559983 : Nat := 118140960795 + 1559983 * 2 ^ 59
def prefixEnd_1559983 : Nat := 4983230072969 + 3 ^ 40 * 1559983 * 2
def baseEnd_1559983 : Nat := 178004687076194509564061

theorem tailTrace_1559983 : CollatzResearch.WordTrace tailWord_1559983 prefixEnd_1559983 178004687076194509564061 := by
  unfold tailWord_1559983
  simp only [CollatzResearch.WordTrace]
  refine ⟨56897254307455489730420603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37931502871636993153613735 56897254307455489730420603)
  ·
    refine ⟨85345881461183234595630905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56897254307455489730420603 85345881461183234595630905)
    ·
      refine ⟨64009411095887425946723179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85345881461183234595630905 64009411095887425946723179)
      ·
        refine ⟨96014116643831138920084769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64009411095887425946723179 96014116643831138920084769)
        ·
          refine ⟨72010587482873354190063577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96014116643831138920084769 72010587482873354190063577)
          ·
            refine ⟨54007940612155015642547683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72010587482873354190063577 54007940612155015642547683)
            ·
              refine ⟨81011910918232523463821525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54007940612155015642547683 81011910918232523463821525)
              ·
                refine ⟨1898716662146074768683317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 81011910918232523463821525 1898716662146074768683317)
                ·
                  refine ⟨178004687076194509564061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1898716662146074768683317 178004687076194509564061)
                  ·
                    rfl

theorem cell22_1559983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 5].length) (baseStart_1559983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1559983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1559983 prefixEnd_1559983 := by exact prefixLift 1559983
  have htrace : WordTrace (prefixWord ++ tailWord_1559983) baseStart_1559983 baseEnd_1559983 := by
    simpa [prefixWord, tailWord_1559983, baseEnd_1559983] using wordTrace_append hprefix tailTrace_1559983
  have hstable : (prefixWord ++ tailWord_1559983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559983).length < 2 ^ (prefixWord ++ tailWord_1559983).sum := by decide
  have hdescent : baseEnd_1559983 < baseStart_1559983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560060 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 6, 3]
def baseStart_1560060 : Nat := 118140960795 + 1560060 * 2 ^ 59
def prefixEnd_1560060 : Nat := 4983230072969 + 3 ^ 40 * 1560060 * 2
def baseEnd_1560060 : Nat := 534040419902180994516947

theorem tailTrace_1560060 : CollatzResearch.WordTrace tailWord_1560060 prefixEnd_1560060 534040419902180994516947 := by
  unfold tailWord_1560060
  simp only [CollatzResearch.WordTrace]
  refine ⟨28450031364088265940486817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37933375152117687920649089 28450031364088265940486817)
  ·
    refine ⟨21337523523066199455365113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28450031364088265940486817 21337523523066199455365113)
    ·
      refine ⟨16003142642299649591523835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21337523523066199455365113 16003142642299649591523835)
      ·
        refine ⟨24004713963449474387285753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16003142642299649591523835 24004713963449474387285753)
        ·
          refine ⟨18003535472587105790464315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24004713963449474387285753 18003535472587105790464315)
          ·
            refine ⟨27005303208880658685696473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18003535472587105790464315 27005303208880658685696473)
            ·
              refine ⟨20253977406660494014272355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27005303208880658685696473 20253977406660494014272355)
              ·
                refine ⟨30380966109990741021408533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20253977406660494014272355 30380966109990741021408533)
                ·
                  refine ⟨1424107786405815985378525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30380966109990741021408533 1424107786405815985378525)
                  ·
                    refine ⟨534040419902180994516947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1424107786405815985378525 534040419902180994516947)
                    ·
                      rfl

theorem cell22_1560060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_1560060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560060 prefixEnd_1560060 := by exact prefixLift 1560060
  have htrace : WordTrace (prefixWord ++ tailWord_1560060) baseStart_1560060 baseEnd_1560060 := by
    simpa [prefixWord, tailWord_1560060, baseEnd_1560060] using wordTrace_append hprefix tailTrace_1560060
  have hstable : (prefixWord ++ tailWord_1560060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560060).length < 2 ^ (prefixWord ++ tailWord_1560060).sum := by decide
  have hdescent : baseEnd_1560060 < baseStart_1560060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560173 : List Nat := [1, 5, 1, 1, 4, 2, 1, 3, 1, 3]
def baseStart_1560173 : Nat := 118140960795 + 1560173 * 2 ^ 59
def prefixEnd_1560173 : Nat := 4983230072969 + 3 ^ 40 * 1560173 * 2
def baseEnd_1560173 : Nat := 534079102111486366441601

theorem tailTrace_1560173 : CollatzResearch.WordTrace tailWord_1560173 prefixEnd_1560173 534079102111486366441601 := by
  unfold tailWord_1560173
  simp only [CollatzResearch.WordTrace]
  refine ⟨56904184176767152179837173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37936122784511434786558115 56904184176767152179837173)
  ·
    refine ⟨5334767266571920516859735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56904184176767152179837173 5334767266571920516859735)
    ·
      refine ⟨8002150899857880775289603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5334767266571920516859735 8002150899857880775289603)
      ·
        refine ⟨12003226349786821162934405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8002150899857880775289603 12003226349786821162934405)
        ·
          refine ⟨2250604940585028968050201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12003226349786821162934405 2250604940585028968050201)
          ·
            refine ⟨1687953705438771726037651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2250604940585028968050201 1687953705438771726037651)
            ·
              refine ⟨2531930558158157589056477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1687953705438771726037651 2531930558158157589056477)
              ·
                refine ⟨949473959309309095896179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2531930558158157589056477 949473959309309095896179)
                ·
                  refine ⟨1424210938963963643844269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 949473959309309095896179 1424210938963963643844269)
                  ·
                    refine ⟨534079102111486366441601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1424210938963963643844269 534079102111486366441601)
                    ·
                      rfl

theorem cell22_1560173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_1560173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560173 prefixEnd_1560173 := by exact prefixLift 1560173
  have htrace : WordTrace (prefixWord ++ tailWord_1560173) baseStart_1560173 baseEnd_1560173 := by
    simpa [prefixWord, tailWord_1560173, baseEnd_1560173] using wordTrace_append hprefix tailTrace_1560173
  have hstable : (prefixWord ++ tailWord_1560173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560173).length < 2 ^ (prefixWord ++ tailWord_1560173).sum := by decide
  have hdescent : baseEnd_1560173 < baseStart_1560173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560227 : List Nat := [1, 1, 1, 4, 1, 1, 6, 1, 2, 4]
def baseStart_1560227 : Nat := 118140960795 + 1560227 * 2 ^ 59
def prefixEnd_1560227 : Nat := 4983230072969 + 3 ^ 40 * 1560227 * 2
def baseEnd_1560227 : Nat := 534097587415048225591435

theorem tailTrace_1560227 : CollatzResearch.WordTrace tailWord_1560227 prefixEnd_1560227 534097587415048225591435 := by
  unfold tailWord_1560227
  simp only [CollatzResearch.WordTrace]
  refine ⟨56906153718571519402302935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37937435812381012934868623 56906153718571519402302935)
  ·
    refine ⟨85359230577857279103454403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56906153718571519402302935 85359230577857279103454403)
    ·
      refine ⟨128038845866785918655181605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85359230577857279103454403 128038845866785918655181605)
      ·
        refine ⟨24007283600022359747846551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128038845866785918655181605 24007283600022359747846551)
        ·
          refine ⟨36010925400033539621769827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24007283600022359747846551 36010925400033539621769827)
          ·
            refine ⟨54016388100050309432654741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36010925400033539621769827 54016388100050309432654741)
            ·
              refine ⟨2532018192189858254655691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54016388100050309432654741 2532018192189858254655691)
              ·
                refine ⟨3798027288284787381983537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2532018192189858254655691 3798027288284787381983537)
                ·
                  refine ⟨2848520466213590536487653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3798027288284787381983537 2848520466213590536487653)
                  ·
                    refine ⟨534097587415048225591435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2848520466213590536487653 534097587415048225591435)
                    ·
                      rfl

theorem cell22_1560227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 4].length) (baseStart_1560227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560227 prefixEnd_1560227 := by exact prefixLift 1560227
  have htrace : WordTrace (prefixWord ++ tailWord_1560227) baseStart_1560227 baseEnd_1560227 := by
    simpa [prefixWord, tailWord_1560227, baseEnd_1560227] using wordTrace_append hprefix tailTrace_1560227
  have hstable : (prefixWord ++ tailWord_1560227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560227).length < 2 ^ (prefixWord ++ tailWord_1560227).sum := by decide
  have hdescent : baseEnd_1560227 < baseStart_1560227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560255 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 1, 8]
def baseStart_1560255 : Nat := 118140960795 + 1560255 * 2 ^ 59
def prefixEnd_1560255 : Nat := 4983230072969 + 3 ^ 40 * 1560255 * 2
def baseEnd_1560255 : Nat := 534107172387265485891349

theorem tailTrace_1560255 : CollatzResearch.WordTrace tailWord_1560255 prefixEnd_1560255 534107172387265485891349 := by
  unfold tailWord_1560255
  simp only [CollatzResearch.WordTrace]
  refine ⟨56907174962470080184322219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37938116641646720122881479 56907174962470080184322219)
  ·
    refine ⟨85360762443705120276483329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56907174962470080184322219 85360762443705120276483329)
    ·
      refine ⟨64020571832778840207362497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85360762443705120276483329 64020571832778840207362497)
      ·
        refine ⟨48015428874584130155521873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64020571832778840207362497 48015428874584130155521873)
        ·
          refine ⟨36011571655938097616641405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48015428874584130155521873 36011571655938097616641405)
          ·
            refine ⟨13504339370976786606240527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36011571655938097616641405 13504339370976786606240527)
            ·
              refine ⟨20256509056465179909360791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13504339370976786606240527 20256509056465179909360791)
              ·
                refine ⟨30384763584697769864041187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20256509056465179909360791 30384763584697769864041187)
                ·
                  refine ⟨45577145377046654796061781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30384763584697769864041187 45577145377046654796061781)
                  ·
                    refine ⟨534107172387265485891349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45577145377046654796061781 534107172387265485891349)
                    ·
                      rfl

theorem cell22_1560255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_1560255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560255 prefixEnd_1560255 := by exact prefixLift 1560255
  have htrace : WordTrace (prefixWord ++ tailWord_1560255) baseStart_1560255 baseEnd_1560255 := by
    simpa [prefixWord, tailWord_1560255, baseEnd_1560255] using wordTrace_append hprefix tailTrace_1560255
  have hstable : (prefixWord ++ tailWord_1560255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560255).length < 2 ^ (prefixWord ++ tailWord_1560255).sum := by decide
  have hdescent : baseEnd_1560255 < baseStart_1560255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560274 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 5, 3]
def baseStart_1560274 : Nat := 118140960795 + 1560274 * 2 ^ 59
def prefixEnd_1560274 : Nat := 4983230072969 + 3 ^ 40 * 1560274 * 2
def baseEnd_1560274 : Nat := 534113676475555769666291

theorem tailTrace_1560274 : CollatzResearch.WordTrace tailWord_1560274 prefixEnd_1560274 534113676475555769666291 := by
  unfold tailWord_1560274
  simp only [CollatzResearch.WordTrace]
  refine ⟨14226966987350311607315969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37938578632934164286175917 14226966987350311607315969)
  ·
    refine ⟨10670225240512733705486977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14226966987350311607315969 10670225240512733705486977)
    ·
      refine ⟨8002668930384550279115233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10670225240512733705486977 8002668930384550279115233)
      ·
        refine ⟨6002001697788412709336425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8002668930384550279115233 6002001697788412709336425)
        ·
          refine ⟨4501501273341309532002319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6002001697788412709336425 4501501273341309532002319)
          ·
            refine ⟨6752251910011964298003479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4501501273341309532002319 6752251910011964298003479)
            ·
              refine ⟨10128377865017946447005219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6752251910011964298003479 10128377865017946447005219)
              ·
                refine ⟨15192566797526919670507829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10128377865017946447005219 15192566797526919670507829)
                ·
                  refine ⟨1424303137268148719110109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15192566797526919670507829 1424303137268148719110109)
                  ·
                    refine ⟨534113676475555769666291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1424303137268148719110109 534113676475555769666291)
                    ·
                      rfl

theorem cell22_1560274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_1560274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560274 prefixEnd_1560274 := by exact prefixLift 1560274
  have htrace : WordTrace (prefixWord ++ tailWord_1560274) baseStart_1560274 baseEnd_1560274 := by
    simpa [prefixWord, tailWord_1560274, baseEnd_1560274] using wordTrace_append hprefix tailTrace_1560274
  have hstable : (prefixWord ++ tailWord_1560274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560274).length < 2 ^ (prefixWord ++ tailWord_1560274).sum := by decide
  have hdescent : baseEnd_1560274 < baseStart_1560274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560302 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_1560302 : Nat := 118140960795 + 1560302 * 2 ^ 59
def prefixEnd_1560302 : Nat := 4983230072969 + 3 ^ 40 * 1560302 * 2
def baseEnd_1560302 : Nat := 534123261447773029966205

theorem tailTrace_1560302 : CollatzResearch.WordTrace tailWord_1560302 prefixEnd_1560302 534123261447773029966205 := by
  unfold tailWord_1560302
  simp only [CollatzResearch.WordTrace]
  refine ⟨7113611149162475901410395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37939259462199871474188773 7113611149162475901410395)
  ·
    refine ⟨10670416723743713852115593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7113611149162475901410395 10670416723743713852115593)
    ·
      refine ⟨8002812542807785389086695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10670416723743713852115593 8002812542807785389086695)
      ·
        refine ⟨12004218814211678083630043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8002812542807785389086695 12004218814211678083630043)
        ·
          refine ⟨18006328221317517125445065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12004218814211678083630043 18006328221317517125445065)
          ·
            refine ⟨13504746165988137844083799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18006328221317517125445065 13504746165988137844083799)
            ·
              refine ⟨20257119248982206766125699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13504746165988137844083799 20257119248982206766125699)
              ·
                refine ⟨30385678873473310149188549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20257119248982206766125699 30385678873473310149188549)
                ·
                  refine ⟨5697314788776245652972853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30385678873473310149188549 5697314788776245652972853)
                  ·
                    refine ⟨534123261447773029966205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5697314788776245652972853 534123261447773029966205)
                    ·
                      rfl

theorem cell22_1560302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_1560302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560302 prefixEnd_1560302 := by exact prefixLift 1560302
  have htrace : WordTrace (prefixWord ++ tailWord_1560302) baseStart_1560302 baseEnd_1560302 := by
    simpa [prefixWord, tailWord_1560302, baseEnd_1560302] using wordTrace_append hprefix tailTrace_1560302
  have hstable : (prefixWord ++ tailWord_1560302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560302).length < 2 ^ (prefixWord ++ tailWord_1560302).sum := by decide
  have hdescent : baseEnd_1560302 < baseStart_1560302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560308 : List Nat := [2, 6, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_1560308 : Nat := 118140960795 + 1560308 * 2 ^ 59
def prefixEnd_1560308 : Nat := 4983230072969 + 3 ^ 40 * 1560308 * 2
def baseEnd_1560308 : Nat := 534125315370391014316187

theorem tailTrace_1560308 : CollatzResearch.WordTrace tailWord_1560308 prefixEnd_1560308 534125315370391014316187 := by
  unfold tailWord_1560308
  simp only [CollatzResearch.WordTrace]
  refine ⟨28454554015639035118000789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37939405354185380157334385 28454554015639035118000789)
  ·
    refine ⟨1333807219483079771156287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28454554015639035118000789 1333807219483079771156287)
    ·
      refine ⟨2000710829224619656734431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1333807219483079771156287 2000710829224619656734431)
      ·
        refine ⟨3001066243836929485101647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2000710829224619656734431 3001066243836929485101647)
        ·
          refine ⟨4501599365755394227652471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3001066243836929485101647 4501599365755394227652471)
          ·
            refine ⟨6752399048633091341478707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4501599365755394227652471 6752399048633091341478707)
            ·
              refine ⟨10128598572949637012218061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6752399048633091341478707 10128598572949637012218061)
              ·
                refine ⟨3798224464856113879581773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10128598572949637012218061 3798224464856113879581773)
                ·
                  refine ⟨1424334174321042704843165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3798224464856113879581773 1424334174321042704843165)
                  ·
                    refine ⟨534125315370391014316187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1424334174321042704843165 534125315370391014316187)
                    ·
                      rfl

theorem cell22_1560308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_1560308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560308 prefixEnd_1560308 := by exact prefixLift 1560308
  have htrace : WordTrace (prefixWord ++ tailWord_1560308) baseStart_1560308 baseEnd_1560308 := by
    simpa [prefixWord, tailWord_1560308, baseEnd_1560308] using wordTrace_append hprefix tailTrace_1560308
  have hstable : (prefixWord ++ tailWord_1560308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560308).length < 2 ^ (prefixWord ++ tailWord_1560308).sum := by decide
  have hdescent : baseEnd_1560308 < baseStart_1560308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560317 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_1560317 : Nat := 118140960795 + 1560317 * 2 ^ 59
def prefixEnd_1560317 : Nat := 4983230072969 + 3 ^ 40 * 1560317 * 2
def baseEnd_1560317 : Nat := 534128396254317990841159

theorem tailTrace_1560317 : CollatzResearch.WordTrace tailWord_1560317 prefixEnd_1560317 534128396254317990841159 := by
  unfold tailWord_1560317
  simp only [CollatzResearch.WordTrace]
  refine ⟨56909436288245464773079205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37939624192163643182052803 56909436288245464773079205)
  ·
    refine ⟨10670519304046024644952351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56909436288245464773079205 10670519304046024644952351)
    ·
      refine ⟨16005778956069036967428527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10670519304046024644952351 16005778956069036967428527)
      ·
        refine ⟨24008668434103555451142791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16005778956069036967428527 24008668434103555451142791)
        ·
          refine ⟨36013002651155333176714187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24008668434103555451142791 36013002651155333176714187)
          ·
            refine ⟨54019503976732999765071281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36013002651155333176714187 54019503976732999765071281)
            ·
              refine ⟨40514627982549749823803461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54019503976732999765071281 40514627982549749823803461)
              ·
                refine ⟨7596492746728078091963149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40514627982549749823803461 7596492746728078091963149)
                ·
                  refine ⟨2848684780023029284486181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7596492746728078091963149 2848684780023029284486181)
                  ·
                    refine ⟨534128396254317990841159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2848684780023029284486181 534128396254317990841159)
                    ·
                      rfl

theorem cell22_1560317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_1560317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560317 prefixEnd_1560317 := by exact prefixLift 1560317
  have htrace : WordTrace (prefixWord ++ tailWord_1560317) baseStart_1560317 baseEnd_1560317 := by
    simpa [prefixWord, tailWord_1560317, baseEnd_1560317] using wordTrace_append hprefix tailTrace_1560317
  have hstable : (prefixWord ++ tailWord_1560317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560317).length < 2 ^ (prefixWord ++ tailWord_1560317).sum := by decide
  have hdescent : baseEnd_1560317 < baseStart_1560317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560332 : List Nat := [2, 2, 1, 2, 2, 1, 4, 2, 6]
def baseStart_1560332 : Nat := 118140960795 + 1560332 * 2 ^ 59
def prefixEnd_1560332 : Nat := 4983230072969 + 3 ^ 40 * 1560332 * 2
def baseEnd_1560332 : Nat := 178044510353620983905371

theorem tailTrace_1560332 : CollatzResearch.WordTrace tailWord_1560332 prefixEnd_1560332 178044510353620983905371 := by
  unfold tailWord_1560332
  simp only [CollatzResearch.WordTrace]
  refine ⟨28454991691595561167437625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37939988922127414889916833 28454991691595561167437625)
  ·
    refine ⟨21341243768696670875578219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28454991691595561167437625 21341243768696670875578219)
    ·
      refine ⟨32011865653045006313367329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21341243768696670875578219 32011865653045006313367329)
      ·
        refine ⟨24008899239783754735025497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32011865653045006313367329 24008899239783754735025497)
        ·
          refine ⟨18006674429837816051269123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24008899239783754735025497 18006674429837816051269123)
          ·
            refine ⟨27010011644756724076903685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18006674429837816051269123 27010011644756724076903685)
            ·
              refine ⟨5064377183391885764419441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27010011644756724076903685 5064377183391885764419441)
              ·
                refine ⟨3798282887543914323314581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5064377183391885764419441 3798282887543914323314581)
                ·
                  refine ⟨178044510353620983905371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3798282887543914323314581 178044510353620983905371)
                  ·
                    rfl

theorem cell22_1560332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_1560332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560332 prefixEnd_1560332 := by exact prefixLift 1560332
  have htrace : WordTrace (prefixWord ++ tailWord_1560332) baseStart_1560332 baseEnd_1560332 := by
    simpa [prefixWord, tailWord_1560332, baseEnd_1560332] using wordTrace_append hprefix tailTrace_1560332
  have hstable : (prefixWord ++ tailWord_1560332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560332).length < 2 ^ (prefixWord ++ tailWord_1560332).sum := by decide
  have hdescent : baseEnd_1560332 < baseStart_1560332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560334 : List Nat := [4, 1, 1, 2, 1, 1, 3, 4, 1, 4]
def baseStart_1560334 : Nat := 118140960795 + 1560334 * 2 ^ 59
def prefixEnd_1560334 : Nat := 4983230072969 + 3 ^ 40 * 1560334 * 2
def baseEnd_1560334 : Nat := 534134215701735613166107

theorem tailTrace_1560334 : CollatzResearch.WordTrace tailWord_1560334 prefixEnd_1560334 534134215701735613166107 := by
  unfold tailWord_1560334
  simp only [CollatzResearch.WordTrace]
  refine ⟨7113757041147984584556007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37940037552789251117632037 7113757041147984584556007)
  ·
    refine ⟨10670635561721976876834011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7113757041147984584556007 10670635561721976876834011)
    ·
      refine ⟨16005953342582965315251017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10670635561721976876834011 16005953342582965315251017)
      ·
        refine ⟨12004465006937223986438263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16005953342582965315251017 12004465006937223986438263)
        ·
          refine ⟨18006697510405835979657395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12004465006937223986438263 18006697510405835979657395)
          ·
            refine ⟨27010046265608753969486093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18006697510405835979657395 27010046265608753969486093)
            ·
              refine ⟨10128767349603282738557285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27010046265608753969486093 10128767349603282738557285)
              ·
                refine ⟨1899143878050615513479491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10128767349603282738557285 1899143878050615513479491)
                ·
                  refine ⟨2848715817075923270219237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1899143878050615513479491 2848715817075923270219237)
                  ·
                    refine ⟨534134215701735613166107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2848715817075923270219237 534134215701735613166107)
                    ·
                      rfl

theorem cell22_1560334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_1560334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560334 prefixEnd_1560334 := by exact prefixLift 1560334
  have htrace : WordTrace (prefixWord ++ tailWord_1560334) baseStart_1560334 baseEnd_1560334 := by
    simpa [prefixWord, tailWord_1560334, baseEnd_1560334] using wordTrace_append hprefix tailTrace_1560334
  have hstable : (prefixWord ++ tailWord_1560334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560334).length < 2 ^ (prefixWord ++ tailWord_1560334).sum := by decide
  have hdescent : baseEnd_1560334 < baseStart_1560334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560364 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 4, 3]
def baseStart_1560364 : Nat := 118140960795 + 1560364 * 2 ^ 59
def prefixEnd_1560364 : Nat := 4983230072969 + 3 ^ 40 * 1560364 * 2
def baseEnd_1560364 : Nat := 534144485314825534916015

theorem tailTrace_1560364 : CollatzResearch.WordTrace tailWord_1560364 prefixEnd_1560364 534144485314825534916015 := by
  unfold tailWord_1560364
  simp only [CollatzResearch.WordTrace]
  refine ⟨28455575259537595900020073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37940767012716794533360097 28455575259537595900020073)
  ·
    refine ⟨21341681444653196925015055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28455575259537595900020073 21341681444653196925015055)
    ·
      refine ⟨32012522166979795387522583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21341681444653196925015055 32012522166979795387522583)
      ·
        refine ⟨48018783250469693081283875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32012522166979795387522583 48018783250469693081283875)
        ·
          refine ⟨72028174875704539621925813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48018783250469693081283875 72028174875704539621925813)
          ·
            refine ⟨6752641394597300589555545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72028174875704539621925813 6752641394597300589555545)
            ·
              refine ⟨5064481045947975442166659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6752641394597300589555545 5064481045947975442166659)
              ·
                refine ⟨7596721568921963163249989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5064481045947975442166659 7596721568921963163249989)
                ·
                  refine ⟨1424385294172868093109373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7596721568921963163249989 1424385294172868093109373)
                  ·
                    refine ⟨534144485314825534916015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1424385294172868093109373 534144485314825534916015)
                    ·
                      rfl

theorem cell22_1560364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_1560364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560364 prefixEnd_1560364 := by exact prefixLift 1560364
  have htrace : WordTrace (prefixWord ++ tailWord_1560364) baseStart_1560364 baseEnd_1560364 := by
    simpa [prefixWord, tailWord_1560364, baseEnd_1560364] using wordTrace_append hprefix tailTrace_1560364
  have hstable : (prefixWord ++ tailWord_1560364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560364).length < 2 ^ (prefixWord ++ tailWord_1560364).sum := by decide
  have hdescent : baseEnd_1560364 < baseStart_1560364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560396 : List Nat := [2, 2, 1, 3, 4, 1, 2, 1, 2, 4]
def baseStart_1560396 : Nat := 118140960795 + 1560396 * 2 ^ 59
def prefixEnd_1560396 : Nat := 4983230072969 + 3 ^ 40 * 1560396 * 2
def baseEnd_1560396 : Nat := 534155439568788118115917

theorem tailTrace_1560396 : CollatzResearch.WordTrace tailWord_1560396 prefixEnd_1560396 534155439568788118115917 := by
  unfold tailWord_1560396
  simp only [CollatzResearch.WordTrace]
  refine ⟨28456158827479630632602521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37941545103306174176803361 28456158827479630632602521)
  ·
    refine ⟨21342119120609722974451891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28456158827479630632602521 21342119120609722974451891)
    ·
      refine ⟨32013178680914584461677837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21342119120609722974451891 32013178680914584461677837)
      ·
        refine ⟨12004942005342969173129189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32013178680914584461677837 12004942005342969173129189)
        ·
          refine ⟨2250926626001806719961723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12004942005342969173129189 2250926626001806719961723)
          ·
            refine ⟨3376389939002710079942585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2250926626001806719961723 3376389939002710079942585)
            ·
              refine ⟨2532292454252032559956939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3376389939002710079942585 2532292454252032559956939)
              ·
                refine ⟨3798438681378048839935409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2532292454252032559956939 3798438681378048839935409)
                ·
                  refine ⟨2848829011033536629951557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3798438681378048839935409 2848829011033536629951557)
                  ·
                    refine ⟨534155439568788118115917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2848829011033536629951557 534155439568788118115917)
                    ·
                      rfl

theorem cell22_1560396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_1560396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560396 prefixEnd_1560396 := by exact prefixLift 1560396
  have htrace : WordTrace (prefixWord ++ tailWord_1560396) baseStart_1560396 baseEnd_1560396 := by
    simpa [prefixWord, tailWord_1560396, baseEnd_1560396] using wordTrace_append hprefix tailTrace_1560396
  have hstable : (prefixWord ++ tailWord_1560396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560396).length < 2 ^ (prefixWord ++ tailWord_1560396).sum := by decide
  have hdescent : baseEnd_1560396 < baseStart_1560396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560484 : List Nat := [2, 3, 1, 2, 1, 3, 1, 3, 6]
def baseStart_1560484 : Nat := 118140960795 + 1560484 * 2 ^ 59
def prefixEnd_1560484 : Nat := 4983230072969 + 3 ^ 40 * 1560484 * 2
def baseEnd_1560484 : Nat := 178061854589061740638549

theorem tailTrace_1560484 : CollatzResearch.WordTrace tailWord_1560484 prefixEnd_1560484 178061854589061740638549 := by
  unfold tailWord_1560484
  simp only [CollatzResearch.WordTrace]
  refine ⟨28457763639320226147204253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37943684852426968196272337 28457763639320226147204253)
  ·
    refine ⟨10671661364745084805201595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28457763639320226147204253 10671661364745084805201595)
    ·
      refine ⟨16007492047117627207802393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10671661364745084805201595 16007492047117627207802393)
      ·
        refine ⟨12005619035338220405851795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16007492047117627207802393 12005619035338220405851795)
        ·
          refine ⟨18008428553007330608777693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12005619035338220405851795 18008428553007330608777693)
          ·
            refine ⟨6753160707377748978291635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18008428553007330608777693 6753160707377748978291635)
            ·
              refine ⟨10129741061066623467437453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6753160707377748978291635 10129741061066623467437453)
              ·
                refine ⟨3798652897899983800289045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10129741061066623467437453 3798652897899983800289045)
                ·
                  refine ⟨178061854589061740638549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3798652897899983800289045 178061854589061740638549)
                  ·
                    rfl

theorem cell22_1560484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_1560484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560484 prefixEnd_1560484 := by exact prefixLift 1560484
  have htrace : WordTrace (prefixWord ++ tailWord_1560484) baseStart_1560484 baseEnd_1560484 := by
    simpa [prefixWord, tailWord_1560484, baseEnd_1560484] using wordTrace_append hprefix tailTrace_1560484
  have hstable : (prefixWord ++ tailWord_1560484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560484).length < 2 ^ (prefixWord ++ tailWord_1560484).sum := by decide
  have hdescent : baseEnd_1560484 < baseStart_1560484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560595 : List Nat := [1, 1, 1, 2, 1, 4, 6, 2, 1, 3]
def baseStart_1560595 : Nat := 118140960795 + 1560595 * 2 ^ 59
def prefixEnd_1560595 : Nat := 4983230072969 + 3 ^ 40 * 1560595 * 2
def baseEnd_1560595 : Nat := 534223561335617932390307

theorem tailTrace_1560595 : CollatzResearch.WordTrace tailWord_1560595 prefixEnd_1560595 534223561335617932390307 := by
  unfold tailWord_1560595
  simp only [CollatzResearch.WordTrace]
  refine ⟨56919575781238318251699239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37946383854158878834466159 56919575781238318251699239)
  ·
    refine ⟨85379363671857477377548859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56919575781238318251699239 85379363671857477377548859)
    ·
      refine ⟨128069045507786216066323289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85379363671857477377548859 128069045507786216066323289)
      ·
        refine ⟨96051784130839662049742467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128069045507786216066323289 96051784130839662049742467)
        ·
          refine ⟨144077676196259493074613701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96051784130839662049742467 144077676196259493074613701)
          ·
            refine ⟨27014564286798654951490069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144077676196259493074613701 27014564286798654951490069)
            ·
              refine ⟨1266307700943686950851097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27014564286798654951490069 1266307700943686950851097)
              ·
                refine ⟨949730775707765213138323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1266307700943686950851097 949730775707765213138323)
                ·
                  refine ⟨1424596163561647819707485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 949730775707765213138323 1424596163561647819707485)
                  ·
                    refine ⟨534223561335617932390307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1424596163561647819707485 534223561335617932390307)
                    ·
                      rfl

theorem cell22_1560595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 1, 3].length) (baseStart_1560595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560595 prefixEnd_1560595 := by exact prefixLift 1560595
  have htrace : WordTrace (prefixWord ++ tailWord_1560595) baseStart_1560595 baseEnd_1560595 := by
    simpa [prefixWord, tailWord_1560595, baseEnd_1560595] using wordTrace_append hprefix tailTrace_1560595
  have hstable : (prefixWord ++ tailWord_1560595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560595).length < 2 ^ (prefixWord ++ tailWord_1560595).sum := by decide
  have hdescent : baseEnd_1560595 < baseStart_1560595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560651 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 4, 3]
def baseStart_1560651 : Nat := 118140960795 + 1560651 * 2 ^ 59
def prefixEnd_1560651 : Nat := 4983230072969 + 3 ^ 40 * 1560651 * 2
def baseEnd_1560651 : Nat := 534242731280052452990135

theorem tailTrace_1560651 : CollatzResearch.WordTrace tailWord_1560651 prefixEnd_1560651 534242731280052452990135 := by
  unfold tailWord_1560651
  simp only [CollatzResearch.WordTrace]
  refine ⟨56921618269035439815737807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37947745512690293210491871 56921618269035439815737807)
  ·
    refine ⟨85382427403553159723606711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56921618269035439815737807 85382427403553159723606711)
    ·
      refine ⟨128073641105329739585410067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85382427403553159723606711 128073641105329739585410067)
      ·
        refine ⟨192110461657994609378115101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128073641105329739585410067 192110461657994609378115101)
        ·
          refine ⟨72041423121747978516793163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192110461657994609378115101 72041423121747978516793163)
          ·
            refine ⟨108062134682621967775189745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72041423121747978516793163 108062134682621967775189745)
            ·
              refine ⟨81046601011966475831392309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108062134682621967775189745 81046601011966475831392309)
              ·
                refine ⟨7598118844871857109193029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81046601011966475831392309 7598118844871857109193029)
                ·
                  refine ⟨1424647283413473207973693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7598118844871857109193029 1424647283413473207973693)
                  ·
                    refine ⟨534242731280052452990135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1424647283413473207973693 534242731280052452990135)
                    ·
                      rfl

theorem cell22_1560651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 3].length) (baseStart_1560651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560651 prefixEnd_1560651 := by exact prefixLift 1560651
  have htrace : WordTrace (prefixWord ++ tailWord_1560651) baseStart_1560651 baseEnd_1560651 := by
    simpa [prefixWord, tailWord_1560651, baseEnd_1560651] using wordTrace_append hprefix tailTrace_1560651
  have hstable : (prefixWord ++ tailWord_1560651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560651).length < 2 ^ (prefixWord ++ tailWord_1560651).sum := by decide
  have hdescent : baseEnd_1560651 < baseStart_1560651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560653 : List Nat := [1, 6, 1, 1, 1, 1, 4, 1, 6]
def baseStart_1560653 : Nat := 118140960795 + 1560653 * 2 ^ 59
def prefixEnd_1560653 : Nat := 4983230072969 + 3 ^ 40 * 1560653 * 2
def baseEnd_1560653 : Nat := 178081138640308371480043

theorem tailTrace_1560653 : CollatzResearch.WordTrace tailWord_1560653 prefixEnd_1560653 178081138640308371480043 := by
  unfold tailWord_1560653
  simp only [CollatzResearch.WordTrace]
  refine ⟨56921691215028194157310613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37947794143352129438207075 56921691215028194157310613)
  ·
    refine ⟨2668204275704446601123935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56921691215028194157310613 2668204275704446601123935)
    ·
      refine ⟨4002306413556669901685903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2668204275704446601123935 4002306413556669901685903)
      ·
        refine ⟨6003459620335004852528855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4002306413556669901685903 6003459620335004852528855)
        ·
          refine ⟨9005189430502507278793283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6003459620335004852528855 9005189430502507278793283)
          ·
            refine ⟨13507784145753760918189925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9005189430502507278793283 13507784145753760918189925)
            ·
              refine ⟨2532709527328830172160611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13507784145753760918189925 2532709527328830172160611)
              ·
                refine ⟨3799064290993245258240917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2532709527328830172160611 3799064290993245258240917)
                ·
                  refine ⟨178081138640308371480043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3799064290993245258240917 178081138640308371480043)
                  ·
                    rfl

theorem cell22_1560653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_1560653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560653 prefixEnd_1560653 := by exact prefixLift 1560653
  have htrace : WordTrace (prefixWord ++ tailWord_1560653) baseStart_1560653 baseEnd_1560653 := by
    simpa [prefixWord, tailWord_1560653, baseEnd_1560653] using wordTrace_append hprefix tailTrace_1560653
  have hstable : (prefixWord ++ tailWord_1560653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560653).length < 2 ^ (prefixWord ++ tailWord_1560653).sum := by decide
  have hdescent : baseEnd_1560653 < baseStart_1560653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560668 : List Nat := [2, 2, 4, 1, 1, 2, 3, 1, 1, 5]
def baseStart_1560668 : Nat := 118140960795 + 1560668 * 2 ^ 59
def prefixEnd_1560668 : Nat := 4983230072969 + 3 ^ 40 * 1560668 * 2
def baseEnd_1560668 : Nat := 534248550727470075315083

theorem tailTrace_1560668 : CollatzResearch.WordTrace tailWord_1560668 prefixEnd_1560668 534248550727470075315083 := by
  unfold tailWord_1560668
  simp only [CollatzResearch.WordTrace]
  refine ⟨28461119154986925859553329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37948158873315901146071105 28461119154986925859553329)
  ·
    refine ⟨21345839366240194394664997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28461119154986925859553329 21345839366240194394664997)
    ·
      refine ⟨4002344881170036448999687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21345839366240194394664997 4002344881170036448999687)
      ·
        refine ⟨6003517321755054673499531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4002344881170036448999687 6003517321755054673499531)
        ·
          refine ⟨9005275982632582010249297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6003517321755054673499531 9005275982632582010249297)
          ·
            refine ⟨6753956986974436507686973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9005275982632582010249297 6753956986974436507686973)
            ·
              refine ⟨2532733870115413690382615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6753956986974436507686973 2532733870115413690382615)
              ·
                refine ⟨3799100805173120535573923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2532733870115413690382615 3799100805173120535573923)
                ·
                  refine ⟨5698651207759680803360885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3799100805173120535573923 5698651207759680803360885)
                  ·
                    refine ⟨534248550727470075315083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5698651207759680803360885 534248550727470075315083)
                    ·
                      rfl

theorem cell22_1560668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_1560668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560668 prefixEnd_1560668 := by exact prefixLift 1560668
  have htrace : WordTrace (prefixWord ++ tailWord_1560668) baseStart_1560668 baseEnd_1560668 := by
    simpa [prefixWord, tailWord_1560668, baseEnd_1560668] using wordTrace_append hprefix tailTrace_1560668
  have hstable : (prefixWord ++ tailWord_1560668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560668).length < 2 ^ (prefixWord ++ tailWord_1560668).sum := by decide
  have hdescent : baseEnd_1560668 < baseStart_1560668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560805 : List Nat := [1, 3, 1, 4, 2, 1, 1, 5, 4]
def baseStart_1560805 : Nat := 118140960795 + 1560805 * 2 ^ 59
def prefixEnd_1560805 : Nat := 4983230072969 + 3 ^ 40 * 1560805 * 2
def baseEnd_1560805 : Nat := 178098482875749128213221

theorem tailTrace_1560805 : CollatzResearch.WordTrace tailWord_1560805 prefixEnd_1560805 178098482875749128213221 := by
  unfold tailWord_1560805
  simp only [CollatzResearch.WordTrace]
  refine ⟨56927235110477524116843869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37951490073651682744562579 56927235110477524116843869)
  ·
    refine ⟨21347713166429071543816451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56927235110477524116843869 21347713166429071543816451)
    ·
      refine ⟨32021569749643607315724677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21347713166429071543816451 32021569749643607315724677)
      ·
        refine ⟨6004044328058176371698377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32021569749643607315724677 6004044328058176371698377)
        ·
          refine ⟨4503033246043632278773783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6004044328058176371698377 4503033246043632278773783)
          ·
            refine ⟨6754549869065448418160675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4503033246043632278773783 6754549869065448418160675)
            ·
              refine ⟨10131824803598172627241013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6754549869065448418160675 10131824803598172627241013)
              ·
                refine ⟨949858575337328683803845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10131824803598172627241013 949858575337328683803845)
                ·
                  refine ⟨178098482875749128213221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 949858575337328683803845 178098482875749128213221)
                  ·
                    rfl

theorem cell22_1560805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 4].length) (baseStart_1560805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560805 prefixEnd_1560805 := by exact prefixLift 1560805
  have htrace : WordTrace (prefixWord ++ tailWord_1560805) baseStart_1560805 baseEnd_1560805 := by
    simpa [prefixWord, tailWord_1560805, baseEnd_1560805] using wordTrace_append hprefix tailTrace_1560805
  have hstable : (prefixWord ++ tailWord_1560805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560805).length < 2 ^ (prefixWord ++ tailWord_1560805).sum := by decide
  have hdescent : baseEnd_1560805 < baseStart_1560805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560807 : List Nat := [1, 1, 5, 3, 1, 1, 4, 1, 1, 4]
def baseStart_1560807 : Nat := 118140960795 + 1560807 * 2 ^ 59
def prefixEnd_1560807 : Nat := 4983230072969 + 3 ^ 40 * 1560807 * 2
def baseEnd_1560807 : Nat := 534296133268120046089657

theorem tailTrace_1560807 : CollatzResearch.WordTrace tailWord_1560807 prefixEnd_1560807 534296133268120046089657 := by
  unfold tailWord_1560807
  simp only [CollatzResearch.WordTrace]
  refine ⟨56927308056470278458416675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37951538704313518972277783 56927308056470278458416675)
  ·
    refine ⟨85390962084705417687625013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56927308056470278458416675 85390962084705417687625013)
    ·
      refine ⟨8005402695441132908214845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85390962084705417687625013 8005402695441132908214845)
      ·
        refine ⟨3002026010790424840580567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8005402695441132908214845 3002026010790424840580567)
        ·
          refine ⟨4503039016185637260870851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3002026010790424840580567 4503039016185637260870851)
          ·
            refine ⟨6754558524278455891306277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4503039016185637260870851 6754558524278455891306277)
            ·
              refine ⟨1266479723302210479619927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6754558524278455891306277 1266479723302210479619927)
              ·
                refine ⟨1899719584953315719429891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1266479723302210479619927 1899719584953315719429891)
                ·
                  refine ⟨2849579377429973579144837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1899719584953315719429891 2849579377429973579144837)
                  ·
                    refine ⟨534296133268120046089657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2849579377429973579144837 534296133268120046089657)
                    ·
                      rfl

theorem cell22_1560807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_1560807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560807 prefixEnd_1560807 := by exact prefixLift 1560807
  have htrace : WordTrace (prefixWord ++ tailWord_1560807) baseStart_1560807 baseEnd_1560807 := by
    simpa [prefixWord, tailWord_1560807, baseEnd_1560807] using wordTrace_append hprefix tailTrace_1560807
  have hstable : (prefixWord ++ tailWord_1560807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560807).length < 2 ^ (prefixWord ++ tailWord_1560807).sum := by decide
  have hdescent : baseEnd_1560807 < baseStart_1560807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560953 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 1, 6]
def baseStart_1560953 : Nat := 118140960795 + 1560953 * 2 ^ 59
def prefixEnd_1560953 : Nat := 4983230072969 + 3 ^ 40 * 1560953 * 2
def baseEnd_1560953 : Nat := 534346112051824331939209

theorem tailTrace_1560953 : CollatzResearch.WordTrace tailWord_1560953 prefixEnd_1560953 534346112051824331939209 := by
  unfold tailWord_1560953
  simp only [CollatzResearch.WordTrace]
  refine ⟨56932633113941345393231513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37955088742627563595487675 56932633113941345393231513)
  ·
    refine ⟨42699474835456009044923635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56932633113941345393231513 42699474835456009044923635)
    ·
      refine ⟨64049212253184013567385453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42699474835456009044923635 64049212253184013567385453)
      ·
        refine ⟨24018454594944005087769545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64049212253184013567385453 24018454594944005087769545)
        ·
          refine ⟨18013840946208003815827159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24018454594944005087769545 18013840946208003815827159)
          ·
            refine ⟨27020761419312005723740739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18013840946208003815827159 27020761419312005723740739)
            ·
              refine ⟨40531142128968008585611109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27020761419312005723740739 40531142128968008585611109)
              ·
                refine ⟨7599589149181501609802083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40531142128968008585611109 7599589149181501609802083)
                ·
                  refine ⟨11399383723772252414703125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7599589149181501609802083 11399383723772252414703125)
                  ·
                    refine ⟨534346112051824331939209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11399383723772252414703125 534346112051824331939209)
                    ·
                      rfl

theorem cell22_1560953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_1560953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560953 prefixEnd_1560953 := by exact prefixLift 1560953
  have htrace : WordTrace (prefixWord ++ tailWord_1560953) baseStart_1560953 baseEnd_1560953 := by
    simpa [prefixWord, tailWord_1560953, baseEnd_1560953] using wordTrace_append hprefix tailTrace_1560953
  have hstable : (prefixWord ++ tailWord_1560953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560953).length < 2 ^ (prefixWord ++ tailWord_1560953).sum := by decide
  have hdescent : baseEnd_1560953 < baseStart_1560953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560955 : List Nat := [1, 1, 1, 1, 1, 8, 2, 1, 1, 5]
def baseStart_1560955 : Nat := 118140960795 + 1560955 * 2 ^ 59
def prefixEnd_1560955 : Nat := 4983230072969 + 3 ^ 40 * 1560955 * 2
def baseEnd_1560955 : Nat := 534346796692696993389203

theorem tailTrace_1560955 : CollatzResearch.WordTrace tailWord_1560955 prefixEnd_1560955 534346796692696993389203 := by
  unfold tailWord_1560955
  simp only [CollatzResearch.WordTrace]
  refine ⟨56932706059934099734804319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37955137373289399823202879 56932706059934099734804319)
  ·
    refine ⟨85399059089901149602206479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56932706059934099734804319 85399059089901149602206479)
    ·
      refine ⟨128098588634851724403309719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85399059089901149602206479 128098588634851724403309719)
      ·
        refine ⟨192147882952277586604964579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128098588634851724403309719 192147882952277586604964579)
        ·
          refine ⟨288221824428416379907446869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192147882952277586604964579 288221824428416379907446869)
          ·
            refine ⟨3377599505020504452040393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 288221824428416379907446869 3377599505020504452040393)
            ·
              refine ⟨2533199628765378339030295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3377599505020504452040393 2533199628765378339030295)
              ·
                refine ⟨3799799443148067508545443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533199628765378339030295 3799799443148067508545443)
                ·
                  refine ⟨5699699164722101262818165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3799799443148067508545443 5699699164722101262818165)
                  ·
                    refine ⟨534346796692696993389203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5699699164722101262818165 534346796692696993389203)
                    ·
                      rfl

theorem cell22_1560955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 5].length) (baseStart_1560955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560955 prefixEnd_1560955 := by exact prefixLift 1560955
  have htrace : WordTrace (prefixWord ++ tailWord_1560955) baseStart_1560955 baseEnd_1560955 := by
    simpa [prefixWord, tailWord_1560955, baseEnd_1560955] using wordTrace_append hprefix tailTrace_1560955
  have hstable : (prefixWord ++ tailWord_1560955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560955).length < 2 ^ (prefixWord ++ tailWord_1560955).sum := by decide
  have hdescent : baseEnd_1560955 < baseStart_1560955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560974 : List Nat := [4, 1, 1, 4, 1, 2, 2, 3, 4]
def baseStart_1560974 : Nat := 118140960795 + 1560974 * 2 ^ 59
def prefixEnd_1560974 : Nat := 4983230072969 + 3 ^ 40 * 1560974 * 2
def baseEnd_1560974 : Nat := 178117766926995759054715

theorem tailTrace_1560974 : CollatzResearch.WordTrace tailWord_1560974 prefixEnd_1560974 178117766926995759054715 := by
  unfold tailWord_1560974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7116674880858158247468247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37955599364576843986497317 7116674880858158247468247)
  ·
    refine ⟨10675012321287237371202371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7116674880858158247468247 10675012321287237371202371)
    ·
      refine ⟨16012518481930856056803557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10675012321287237371202371 16012518481930856056803557)
      ·
        refine ⟨3002347215362035510650667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16012518481930856056803557 3002347215362035510650667)
        ·
          refine ⟨4503520823043053265976001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3002347215362035510650667 4503520823043053265976001)
          ·
            refine ⟨3377640617282289949482001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4503520823043053265976001 3377640617282289949482001)
            ·
              refine ⟨2533230462961717462111501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3377640617282289949482001 2533230462961717462111501)
              ·
                refine ⟨949961423610644048291813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2533230462961717462111501 949961423610644048291813)
                ·
                  refine ⟨178117766926995759054715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 949961423610644048291813 178117766926995759054715)
                  ·
                    rfl

theorem cell22_1560974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_1560974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1560974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1560974 prefixEnd_1560974 := by exact prefixLift 1560974
  have htrace : WordTrace (prefixWord ++ tailWord_1560974) baseStart_1560974 baseEnd_1560974 := by
    simpa [prefixWord, tailWord_1560974, baseEnd_1560974] using wordTrace_append hprefix tailTrace_1560974
  have hstable : (prefixWord ++ tailWord_1560974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560974).length < 2 ^ (prefixWord ++ tailWord_1560974).sum := by decide
  have hdescent : baseEnd_1560974 < baseStart_1560974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561017 : List Nat := [1, 2, 1, 4, 3, 1, 2, 2, 3, 3]
def baseStart_1561017 : Nat := 118140960795 + 1561017 * 2 ^ 59
def prefixEnd_1561017 : Nat := 4983230072969 + 3 ^ 40 * 1561017 * 2
def baseEnd_1561017 : Nat := 534368020559749498339013

theorem tailTrace_1561017 : CollatzResearch.WordTrace tailWord_1561017 prefixEnd_1561017 534368020559749498339013 := by
  unfold tailWord_1561017
  simp only [CollatzResearch.WordTrace]
  refine ⟨56934967385709484323561305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37956644923806322882374203 56934967385709484323561305)
  ·
    refine ⟨42701225539282113242670979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56934967385709484323561305 42701225539282113242670979)
    ·
      refine ⟨64051838308923169864006469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42701225539282113242670979 64051838308923169864006469)
      ·
        refine ⟨12009719682923094349501213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64051838308923169864006469 12009719682923094349501213)
        ·
          refine ⟨4503644881096160381062955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12009719682923094349501213 4503644881096160381062955)
          ·
            refine ⟨6755467321644240571594433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4503644881096160381062955 6755467321644240571594433)
            ·
              refine ⟨5066600491233180428695825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6755467321644240571594433 5066600491233180428695825)
              ·
                refine ⟨3799950368424885321521869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5066600491233180428695825 3799950368424885321521869)
                ·
                  refine ⟨1424981388159331995570701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3799950368424885321521869 1424981388159331995570701)
                  ·
                    refine ⟨534368020559749498339013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1424981388159331995570701 534368020559749498339013)
                    ·
                      rfl

theorem cell22_1561017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 3].length) (baseStart_1561017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561017 prefixEnd_1561017 := by exact prefixLift 1561017
  have htrace : WordTrace (prefixWord ++ tailWord_1561017) baseStart_1561017 baseEnd_1561017 := by
    simpa [prefixWord, tailWord_1561017, baseEnd_1561017] using wordTrace_append hprefix tailTrace_1561017
  have hstable : (prefixWord ++ tailWord_1561017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561017).length < 2 ^ (prefixWord ++ tailWord_1561017).sum := by decide
  have hdescent : baseEnd_1561017 < baseStart_1561017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561025 : List Nat := [1, 2, 7, 1, 2, 1, 1, 3, 4]
def baseStart_1561025 : Nat := 118140960795 + 1561025 * 2 ^ 59
def prefixEnd_1561025 : Nat := 4983230072969 + 3 ^ 40 * 1561025 * 2
def baseEnd_1561025 : Nat := 178123586374413381379663

theorem tailTrace_1561025 : CollatzResearch.WordTrace tailWord_1561025 prefixEnd_1561025 178123586374413381379663 := by
  unfold tailWord_1561025
  simp only [CollatzResearch.WordTrace]
  refine ⟨56935259169680501689852529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37956839446453667793235019 56935259169680501689852529)
  ·
    refine ⟨42701444377260376267389397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56935259169680501689852529 42701444377260376267389397)
    ·
      refine ⟨1000815102592040068766939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 42701444377260376267389397 1000815102592040068766939)
      ·
        refine ⟨1501222653888060103150409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1000815102592040068766939 1501222653888060103150409)
        ·
          refine ⟨1125916990416045077362807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1501222653888060103150409 1125916990416045077362807)
          ·
            refine ⟨1688875485624067616044211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125916990416045077362807 1688875485624067616044211)
            ·
              refine ⟨2533313228436101424066317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1688875485624067616044211 2533313228436101424066317)
              ·
                refine ⟨949992460663538034024869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2533313228436101424066317 949992460663538034024869)
                ·
                  refine ⟨178123586374413381379663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 949992460663538034024869 178123586374413381379663)
                  ·
                    rfl

theorem cell22_1561025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 4].length) (baseStart_1561025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561025 prefixEnd_1561025 := by exact prefixLift 1561025
  have htrace : WordTrace (prefixWord ++ tailWord_1561025) baseStart_1561025 baseEnd_1561025 := by
    simpa [prefixWord, tailWord_1561025, baseEnd_1561025] using wordTrace_append hprefix tailTrace_1561025
  have hstable : (prefixWord ++ tailWord_1561025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561025).length < 2 ^ (prefixWord ++ tailWord_1561025).sum := by decide
  have hdescent : baseEnd_1561025 < baseStart_1561025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561043 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 3, 10]
def baseStart_1561043 : Nat := 118140960795 + 1561043 * 2 ^ 59
def prefixEnd_1561043 : Nat := 4983230072969 + 3 ^ 40 * 1561043 * 2
def baseEnd_1561043 : Nat := 534376920891094097188933

theorem tailTrace_1561043 : CollatzResearch.WordTrace tailWord_1561043 prefixEnd_1561043 534376920891094097188933 := by
  unfold tailWord_1561043
  simp only [CollatzResearch.WordTrace]
  refine ⟨56935915683615290764007783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37957277122410193842671855 56935915683615290764007783)
  ·
    refine ⟨85403873525422936146011675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56935915683615290764007783 85403873525422936146011675)
    ·
      refine ⟨128105810288134404219017513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85403873525422936146011675 128105810288134404219017513)
      ·
        refine ⟨96079357716100803164263135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128105810288134404219017513 96079357716100803164263135)
        ·
          refine ⟨144119036574151204746394703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96079357716100803164263135 144119036574151204746394703)
          ·
            refine ⟨216178554861226807119592055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144119036574151204746394703 216178554861226807119592055)
            ·
              refine ⟨324267832291840210679388083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216178554861226807119592055 324267832291840210679388083)
              ·
                refine ⟨486401748437760316019082125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324267832291840210679388083 486401748437760316019082125)
                ·
                  refine ⟨182400655664160118507155797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 486401748437760316019082125 182400655664160118507155797)
                  ·
                    refine ⟨534376920891094097188933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 182400655664160118507155797 534376920891094097188933)
                    ·
                      rfl

theorem cell22_1561043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 10].length) (baseStart_1561043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561043 prefixEnd_1561043 := by exact prefixLift 1561043
  have htrace : WordTrace (prefixWord ++ tailWord_1561043) baseStart_1561043 baseEnd_1561043 := by
    simpa [prefixWord, tailWord_1561043, baseEnd_1561043] using wordTrace_append hprefix tailTrace_1561043
  have hstable : (prefixWord ++ tailWord_1561043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561043).length < 2 ^ (prefixWord ++ tailWord_1561043).sum := by decide
  have hdescent : baseEnd_1561043 < baseStart_1561043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561064 : List Nat := [2, 1, 4, 1, 1, 5, 2, 1, 5]
def baseStart_1561064 : Nat := 118140960795 + 1561064 * 2 ^ 59
def prefixEnd_1561064 : Nat := 4983230072969 + 3 ^ 40 * 1561064 * 2
def baseEnd_1561064 : Nat := 178128036540085680804623

theorem tailTrace_1561064 : CollatzResearch.WordTrace tailWord_1561064 prefixEnd_1561064 178128036540085680804623 := by
  unfold tailWord_1561064
  simp only [CollatzResearch.WordTrace]
  refine ⟨28468340808269605675261123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37957787744359474233681497 28468340808269605675261123)
  ·
    refine ⟨42702511212404408512891685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28468340808269605675261123 42702511212404408512891685)
    ·
      refine ⟨8006720852325826596167191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42702511212404408512891685 8006720852325826596167191)
      ·
        refine ⟨12010081278488739894250787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8006720852325826596167191 12010081278488739894250787)
        ·
          refine ⟨18015121917733109841376181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12010081278488739894250787 18015121917733109841376181)
          ·
            refine ⟨1688917679787479047629017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18015121917733109841376181 1688917679787479047629017)
            ·
              refine ⟨1266688259840609285721763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1688917679787479047629017 1266688259840609285721763)
              ·
                refine ⟨1900032389760913928582645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1266688259840609285721763 1900032389760913928582645)
                ·
                  refine ⟨178128036540085680804623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1900032389760913928582645 178128036540085680804623)
                  ·
                    rfl

theorem cell22_1561064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 5].length) (baseStart_1561064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561064 prefixEnd_1561064 := by exact prefixLift 1561064
  have htrace : WordTrace (prefixWord ++ tailWord_1561064) baseStart_1561064 baseEnd_1561064 := by
    simpa [prefixWord, tailWord_1561064, baseEnd_1561064] using wordTrace_append hprefix tailTrace_1561064
  have hstable : (prefixWord ++ tailWord_1561064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561064).length < 2 ^ (prefixWord ++ tailWord_1561064).sum := by decide
  have hdescent : baseEnd_1561064 < baseStart_1561064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561105 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 4, 4]
def baseStart_1561105 : Nat := 118140960795 + 1561105 * 2 ^ 59
def prefixEnd_1561105 : Nat := 4983230072969 + 3 ^ 40 * 1561105 * 2
def baseEnd_1561105 : Nat := 534398144758146602138743

theorem tailTrace_1561105 : CollatzResearch.WordTrace tailWord_1561105 prefixEnd_1561105 534398144758146602138743 := by
  unfold tailWord_1561105
  simp only [CollatzResearch.WordTrace]
  refine ⟨56938177009390675352764769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37958784672927116901843179 56938177009390675352764769)
  ·
    refine ⟨42703632757043006514573577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56938177009390675352764769 42703632757043006514573577)
    ·
      refine ⟨32027724567782254885930183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42703632757043006514573577 32027724567782254885930183)
      ·
        refine ⟨48041586851673382328895275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32027724567782254885930183 48041586851673382328895275)
        ·
          refine ⟨72062380277510073493342913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48041586851673382328895275 72062380277510073493342913)
          ·
            refine ⟨54046785208132555120007185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72062380277510073493342913 54046785208132555120007185)
            ·
              refine ⟨40535088906099416340005389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54046785208132555120007185 40535088906099416340005389)
              ·
                refine ⟨15200658339787281127502021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40535088906099416340005389 15200658339787281127502021)
                ·
                  refine ⟨2850123438710115211406629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15200658339787281127502021 2850123438710115211406629)
                  ·
                    refine ⟨534398144758146602138743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2850123438710115211406629 534398144758146602138743)
                    ·
                      rfl

theorem cell22_1561105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_1561105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561105 prefixEnd_1561105 := by exact prefixLift 1561105
  have htrace : WordTrace (prefixWord ++ tailWord_1561105) baseStart_1561105 baseEnd_1561105 := by
    simpa [prefixWord, tailWord_1561105, baseEnd_1561105] using wordTrace_append hprefix tailTrace_1561105
  have hstable : (prefixWord ++ tailWord_1561105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561105).length < 2 ^ (prefixWord ++ tailWord_1561105).sum := by decide
  have hdescent : baseEnd_1561105 < baseStart_1561105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561158 : List Nat := [6, 1, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_1561158 : Nat := 118140960795 + 1561158 * 2 ^ 59
def prefixEnd_1561158 : Nat := 4983230072969 + 3 ^ 40 * 1561158 * 2
def baseEnd_1561158 : Nat := 534416287741272130563581

theorem tailTrace_1561158 : CollatzResearch.WordTrace tailWord_1561158 prefixEnd_1561158 534416287741272130563581 := by
  unfold tailWord_1561158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1779378439943708293888879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37960073385465776936296085 1779378439943708293888879)
  ·
    refine ⟨2669067659915562440833319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1779378439943708293888879 2669067659915562440833319)
    ·
      refine ⟨4003601489873343661249979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2669067659915562440833319 4003601489873343661249979)
      ·
        refine ⟨6005402234810015491874969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4003601489873343661249979 6005402234810015491874969)
        ·
          refine ⟨4504051676107511618906227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6005402234810015491874969 4504051676107511618906227)
          ·
            refine ⟨6756077514161267428359341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4504051676107511618906227 6756077514161267428359341)
            ·
              refine ⟨2533529067810475285634753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6756077514161267428359341 2533529067810475285634753)
              ·
                refine ⟨1900146800857856464226065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2533529067810475285634753 1900146800857856464226065)
                ·
                  refine ⟨1425110100643392348169549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1900146800857856464226065 1425110100643392348169549)
                  ·
                    refine ⟨534416287741272130563581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1425110100643392348169549 534416287741272130563581)
                    ·
                      rfl

theorem cell22_1561158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_1561158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561158 prefixEnd_1561158 := by exact prefixLift 1561158
  have htrace : WordTrace (prefixWord ++ tailWord_1561158) baseStart_1561158 baseEnd_1561158 := by
    simpa [prefixWord, tailWord_1561158, baseEnd_1561158] using wordTrace_append hprefix tailTrace_1561158
  have hstable : (prefixWord ++ tailWord_1561158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561158).length < 2 ^ (prefixWord ++ tailWord_1561158).sum := by decide
  have hdescent : baseEnd_1561158 < baseStart_1561158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561169 : List Nat := [1, 2, 2, 1, 3, 4, 2, 1, 3, 3]
def baseStart_1561169 : Nat := 118140960795 + 1561169 * 2 ^ 59
def prefixEnd_1561169 : Nat := 4983230072969 + 3 ^ 40 * 1561169 * 2
def baseEnd_1561169 : Nat := 534420053266071768538547

theorem tailTrace_1561169 : CollatzResearch.WordTrace tailWord_1561169 prefixEnd_1561169 534420053266071768538547 := by
  unfold tailWord_1561169
  simp only [CollatzResearch.WordTrace]
  refine ⟨56940511281158814283094561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37960340854105876188729707 56940511281158814283094561)
  ·
    refine ⟨42705383460869110712320921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56940511281158814283094561 42705383460869110712320921)
    ·
      refine ⟨32029037595651833034240691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42705383460869110712320921 32029037595651833034240691)
      ·
        refine ⟨48043556393477749551361037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32029037595651833034240691 48043556393477749551361037)
        ·
          refine ⟨18016333647554156081760389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48043556393477749551361037 18016333647554156081760389)
          ·
            refine ⟨3378062558916404265330073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18016333647554156081760389 3378062558916404265330073)
            ·
              refine ⟨2533546919187303198997555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3378062558916404265330073 2533546919187303198997555)
              ·
                refine ⟨3800320378780954798496333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533546919187303198997555 3800320378780954798496333)
                ·
                  refine ⟨1425120142042858049436125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3800320378780954798496333 1425120142042858049436125)
                  ·
                    refine ⟨534420053266071768538547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1425120142042858049436125 534420053266071768538547)
                    ·
                      rfl

theorem cell22_1561169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_1561169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561169 prefixEnd_1561169 := by exact prefixLift 1561169
  have htrace : WordTrace (prefixWord ++ tailWord_1561169) baseStart_1561169 baseEnd_1561169 := by
    simpa [prefixWord, tailWord_1561169, baseEnd_1561169] using wordTrace_append hprefix tailTrace_1561169
  have hstable : (prefixWord ++ tailWord_1561169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561169).length < 2 ^ (prefixWord ++ tailWord_1561169).sum := by decide
  have hdescent : baseEnd_1561169 < baseStart_1561169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561257 : List Nat := [1, 2, 1, 1, 1, 1, 2, 7, 2, 4]
def baseStart_1561257 : Nat := 118140960795 + 1561257 * 2 ^ 59
def prefixEnd_1561257 : Nat := 4983230072969 + 3 ^ 40 * 1561257 * 2
def baseEnd_1561257 : Nat := 534450177464468872338277

theorem tailTrace_1561257 : CollatzResearch.WordTrace tailWord_1561257 prefixEnd_1561257 534450177464468872338277 := by
  unfold tailWord_1561257
  simp only [CollatzResearch.WordTrace]
  refine ⟨56943720904840005312298025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37962480603226670208198683 56943720904840005312298025)
  ·
    refine ⟨42707790678630003984223519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56943720904840005312298025 42707790678630003984223519)
    ·
      refine ⟨64061686017945005976335279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42707790678630003984223519 64061686017945005976335279)
      ·
        refine ⟨96092529026917508964502919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64061686017945005976335279 96092529026917508964502919)
        ·
          refine ⟨144138793540376263446754379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96092529026917508964502919 144138793540376263446754379)
          ·
            refine ⟨216208190310564395170131569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144138793540376263446754379 216208190310564395170131569)
            ·
              refine ⟨162156142732923296377598677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216208190310564395170131569 162156142732923296377598677)
              ·
                refine ⟨3800534595302889758849969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 162156142732923296377598677 3800534595302889758849969)
                ·
                  refine ⟨2850400946477167319137477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3800534595302889758849969 2850400946477167319137477)
                  ·
                    refine ⟨534450177464468872338277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2850400946477167319137477 534450177464468872338277)
                    ·
                      rfl

theorem cell22_1561257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 4].length) (baseStart_1561257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561257 prefixEnd_1561257 := by exact prefixLift 1561257
  have htrace : WordTrace (prefixWord ++ tailWord_1561257) baseStart_1561257 baseEnd_1561257 := by
    simpa [prefixWord, tailWord_1561257, baseEnd_1561257] using wordTrace_append hprefix tailTrace_1561257
  have hstable : (prefixWord ++ tailWord_1561257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561257).length < 2 ^ (prefixWord ++ tailWord_1561257).sum := by decide
  have hdescent : baseEnd_1561257 < baseStart_1561257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561276 : List Nat := [2, 2, 2, 3, 1, 1, 4, 2, 2, 3]
def baseStart_1561276 : Nat := 118140960795 + 1561276 * 2 ^ 59
def prefixEnd_1561276 : Nat := 4983230072969 + 3 ^ 40 * 1561276 * 2
def baseEnd_1561276 : Nat := 534456681552759156113219

theorem tailTrace_1561276 : CollatzResearch.WordTrace tailWord_1561276 prefixEnd_1561276 534456681552759156113219 := by
  unfold tailWord_1561276
  simp only [CollatzResearch.WordTrace]
  refine ⟨28472206945885585778619841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37962942594514114371493121 28472206945885585778619841)
  ·
    refine ⟨21354155209414189333964881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28472206945885585778619841 21354155209414189333964881)
    ·
      refine ⟨16015616407060642000473661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21354155209414189333964881 16015616407060642000473661)
      ·
        refine ⟨6005856152647740750177623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16015616407060642000473661 6005856152647740750177623)
        ·
          refine ⟨9008784228971611125266435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6005856152647740750177623 9008784228971611125266435)
          ·
            refine ⟨13513176343457416687899653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9008784228971611125266435 13513176343457416687899653)
            ·
              refine ⟨2533720564398265628981185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13513176343457416687899653 2533720564398265628981185)
              ·
                refine ⟨1900290423298699221735889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2533720564398265628981185 1900290423298699221735889)
                ·
                  refine ⟨1425217817474024416301917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1900290423298699221735889 1425217817474024416301917)
                  ·
                    refine ⟨534456681552759156113219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1425217817474024416301917 534456681552759156113219)
                    ·
                      rfl

theorem cell22_1561276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_1561276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561276 prefixEnd_1561276 := by exact prefixLift 1561276
  have htrace : WordTrace (prefixWord ++ tailWord_1561276) baseStart_1561276 baseEnd_1561276 := by
    simpa [prefixWord, tailWord_1561276, baseEnd_1561276] using wordTrace_append hprefix tailTrace_1561276
  have hstable : (prefixWord ++ tailWord_1561276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561276).length < 2 ^ (prefixWord ++ tailWord_1561276).sum := by decide
  have hdescent : baseEnd_1561276 < baseStart_1561276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561293 : List Nat := [1, 6, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_1561293 : Nat := 118140960795 + 1561293 * 2 ^ 59
def prefixEnd_1561293 : Nat := 4983230072969 + 3 ^ 40 * 1561293 * 2
def baseEnd_1561293 : Nat := 534462501000176778438167

theorem tailTrace_1561293 : CollatzResearch.WordTrace tailWord_1561293 prefixEnd_1561293 534462501000176778438167 := by
  unfold tailWord_1561293
  simp only [CollatzResearch.WordTrace]
  refine ⟨56945033932709583460608533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37963355955139722307072355 56945033932709583460608533)
  ·
    refine ⟨2669298465595761724716025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56945033932709583460608533 2669298465595761724716025)
    ·
      refine ⟨2001973849196821293537019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2669298465595761724716025 2001973849196821293537019)
      ·
        refine ⟨3002960773795231940305529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2001973849196821293537019 3002960773795231940305529)
        ·
          refine ⟨2252220580346423955229147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3002960773795231940305529 2252220580346423955229147)
          ·
            refine ⟨3378330870519635932843721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2252220580346423955229147 3378330870519635932843721)
            ·
              refine ⟨2533748152889726949632791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3378330870519635932843721 2533748152889726949632791)
              ·
                refine ⟨3800622229334590424449187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533748152889726949632791 3800622229334590424449187)
                ·
                  refine ⟨5700933344001885636673781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3800622229334590424449187 5700933344001885636673781)
                  ·
                    refine ⟨534462501000176778438167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5700933344001885636673781 534462501000176778438167)
                    ·
                      rfl

theorem cell22_1561293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_1561293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561293 prefixEnd_1561293 := by exact prefixLift 1561293
  have htrace : WordTrace (prefixWord ++ tailWord_1561293) baseStart_1561293 baseEnd_1561293 := by
    simpa [prefixWord, tailWord_1561293, baseEnd_1561293] using wordTrace_append hprefix tailTrace_1561293
  have hstable : (prefixWord ++ tailWord_1561293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561293).length < 2 ^ (prefixWord ++ tailWord_1561293).sum := by decide
  have hdescent : baseEnd_1561293 < baseStart_1561293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561304 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 5, 3]
def baseStart_1561304 : Nat := 118140960795 + 1561304 * 2 ^ 59
def prefixEnd_1561304 : Nat := 4983230072969 + 3 ^ 40 * 1561304 * 2
def baseEnd_1561304 : Nat := 534466266524976416413133

theorem tailTrace_1561304 : CollatzResearch.WordTrace tailWord_1561304 prefixEnd_1561304 534466266524976416413133 := by
  unfold tailWord_1561304
  simp only [CollatzResearch.WordTrace]
  refine ⟨28472717567834866169629483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37963623423779821559505977 28472717567834866169629483)
  ·
    refine ⟨42709076351752299254444225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28472717567834866169629483 42709076351752299254444225)
    ·
      refine ⟨32031807263814224440833169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42709076351752299254444225 32031807263814224440833169)
      ·
        refine ⟨24023855447860668330624877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32031807263814224440833169 24023855447860668330624877)
        ·
          refine ⟨9008945792947750623984329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24023855447860668330624877 9008945792947750623984329)
          ·
            refine ⟨6756709344710812967988247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9008945792947750623984329 6756709344710812967988247)
            ·
              refine ⟨10135064017066219451982371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6756709344710812967988247 10135064017066219451982371)
              ·
                refine ⟨15202596025599329177973557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10135064017066219451982371 15202596025599329177973557)
                ·
                  refine ⟨1425243377399937110435021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15202596025599329177973557 1425243377399937110435021)
                  ·
                    refine ⟨534466266524976416413133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1425243377399937110435021 534466266524976416413133)
                    ·
                      rfl

theorem cell22_1561304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_1561304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561304 prefixEnd_1561304 := by exact prefixLift 1561304
  have htrace : WordTrace (prefixWord ++ tailWord_1561304) baseStart_1561304 baseEnd_1561304 := by
    simpa [prefixWord, tailWord_1561304, baseEnd_1561304] using wordTrace_append hprefix tailTrace_1561304
  have hstable : (prefixWord ++ tailWord_1561304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561304).length < 2 ^ (prefixWord ++ tailWord_1561304).sum := by decide
  have hdescent : baseEnd_1561304 < baseStart_1561304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561308 : List Nat := [2, 2, 5, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1561308 : Nat := 118140960795 + 1561308 * 2 ^ 59
def prefixEnd_1561308 : Nat := 4983230072969 + 3 ^ 40 * 1561308 * 2
def baseEnd_1561308 : Nat := 534467635806721739313121

theorem tailTrace_1561308 : CollatzResearch.WordTrace tailWord_1561308 prefixEnd_1561308 534467635806721739313121 := by
  unfold tailWord_1561308
  simp only [CollatzResearch.WordTrace]
  refine ⟨28472790513827620511202289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37963720685103494014936385 28472790513827620511202289)
  ·
    refine ⟨21354592885370715383401717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28472790513827620511202289 21354592885370715383401717)
    ·
      refine ⟨2001993083003504567193911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21354592885370715383401717 2001993083003504567193911)
      ·
        refine ⟨3002989624505256850790867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2001993083003504567193911 3002989624505256850790867)
        ·
          refine ⟨4504484436757885276186301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3002989624505256850790867 4504484436757885276186301)
          ·
            refine ⟨1689181663784206978569863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4504484436757885276186301 1689181663784206978569863)
            ·
              refine ⟨2533772495676310467854795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1689181663784206978569863 2533772495676310467854795)
              ·
                refine ⟨3800658743514465701782193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533772495676310467854795 3800658743514465701782193)
                ·
                  refine ⟨2850494057635849276336645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3800658743514465701782193 2850494057635849276336645)
                  ·
                    refine ⟨534467635806721739313121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2850494057635849276336645 534467635806721739313121)
                    ·
                      rfl

theorem cell22_1561308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1561308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561308 prefixEnd_1561308 := by exact prefixLift 1561308
  have htrace : WordTrace (prefixWord ++ tailWord_1561308) baseStart_1561308 baseEnd_1561308 := by
    simpa [prefixWord, tailWord_1561308, baseEnd_1561308] using wordTrace_append hprefix tailTrace_1561308
  have hstable : (prefixWord ++ tailWord_1561308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561308).length < 2 ^ (prefixWord ++ tailWord_1561308).sum := by decide
  have hdescent : baseEnd_1561308 < baseStart_1561308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561321 : List Nat := [1, 2, 1, 1, 1, 2, 5, 5, 1, 3]
def baseStart_1561321 : Nat := 118140960795 + 1561321 * 2 ^ 59
def prefixEnd_1561321 : Nat := 4983230072969 + 3 ^ 40 * 1561321 * 2
def baseEnd_1561321 : Nat := 534472085972394038738081

theorem tailTrace_1561321 : CollatzResearch.WordTrace tailWord_1561321 prefixEnd_1561321 534472085972394038738081 := by
  unfold tailWord_1561321
  simp only [CollatzResearch.WordTrace]
  refine ⟨56946055176608144242627817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37964036784405429495085211 56946055176608144242627817)
  ·
    refine ⟨42709541382456108181970863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56946055176608144242627817 42709541382456108181970863)
    ·
      refine ⟨64064312073684162272956295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42709541382456108181970863 64064312073684162272956295)
      ·
        refine ⟨96096468110526243409434443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64064312073684162272956295 96096468110526243409434443)
        ·
          refine ⟨144144702165789365114151665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96096468110526243409434443 144144702165789365114151665)
          ·
            refine ⟨108108526624342023835613749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144144702165789365114151665 108108526624342023835613749)
            ·
              refine ⟨10135174371032064734588789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108108526624342023835613749 10135174371032064734588789)
              ·
                refine ⟨950172597284256068867699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10135174371032064734588789 950172597284256068867699)
                ·
                  refine ⟨1425258895926384103301549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 950172597284256068867699 1425258895926384103301549)
                  ·
                    refine ⟨534472085972394038738081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1425258895926384103301549 534472085972394038738081)
                    ·
                      rfl

theorem cell22_1561321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 1, 3].length) (baseStart_1561321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561321 prefixEnd_1561321 := by exact prefixLift 1561321
  have htrace : WordTrace (prefixWord ++ tailWord_1561321) baseStart_1561321 baseEnd_1561321 := by
    simpa [prefixWord, tailWord_1561321, baseEnd_1561321] using wordTrace_append hprefix tailTrace_1561321
  have hstable : (prefixWord ++ tailWord_1561321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561321).length < 2 ^ (prefixWord ++ tailWord_1561321).sum := by decide
  have hdescent : baseEnd_1561321 < baseStart_1561321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561334 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_1561334 : Nat := 118140960795 + 1561334 * 2 ^ 59
def prefixEnd_1561334 : Nat := 4983230072969 + 3 ^ 40 * 1561334 * 2
def baseEnd_1561334 : Nat := 178158845379355446054347

theorem tailTrace_1561334 : CollatzResearch.WordTrace tailWord_1561334 prefixEnd_1561334 178158845379355446054347 := by
  unfold tailWord_1561334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3559158082847565466428191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37964352883707364975234037 3559158082847565466428191)
  ·
    refine ⟨5338737124271348199642287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3559158082847565466428191 5338737124271348199642287)
    ·
      refine ⟨8008105686407022299463431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5338737124271348199642287 8008105686407022299463431)
      ·
        refine ⟨12012158529610533449195147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8008105686407022299463431 12012158529610533449195147)
        ·
          refine ⟨18018237794415800173792721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12012158529610533449195147 18018237794415800173792721)
          ·
            refine ⟨13513678345811850130344541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18018237794415800173792721 13513678345811850130344541)
            ·
              refine ⟨5067629379679443798879203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13513678345811850130344541 5067629379679443798879203)
              ·
                refine ⟨7601444069519165698318805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5067629379679443798879203 7601444069519165698318805)
                ·
                  refine ⟨178158845379355446054347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7601444069519165698318805 178158845379355446054347)
                  ·
                    rfl

theorem cell22_1561334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_1561334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561334 prefixEnd_1561334 := by exact prefixLift 1561334
  have htrace : WordTrace (prefixWord ++ tailWord_1561334) baseStart_1561334 baseEnd_1561334 := by
    simpa [prefixWord, tailWord_1561334, baseEnd_1561334] using wordTrace_append hprefix tailTrace_1561334
  have hstable : (prefixWord ++ tailWord_1561334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561334).length < 2 ^ (prefixWord ++ tailWord_1561334).sum := by decide
  have hdescent : baseEnd_1561334 < baseStart_1561334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561389 : List Nat := [1, 5, 3, 2, 1, 1, 3, 2, 1, 3]
def baseStart_1561389 : Nat := 118140960795 + 1561389 * 2 ^ 59
def prefixEnd_1561389 : Nat := 4983230072969 + 3 ^ 40 * 1561389 * 2
def baseEnd_1561389 : Nat := 534495363762064528037873

theorem tailTrace_1561389 : CollatzResearch.WordTrace tailWord_1561389 prefixEnd_1561389 534495363762064528037873 := by
  unfold tailWord_1561389
  simp only [CollatzResearch.WordTrace]
  refine ⟨56948535340361791856103221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37965690226907861237402147 56948535340361791856103221)
  ·
    refine ⟨5338925188158917986509677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56948535340361791856103221 5338925188158917986509677)
    ·
      refine ⟨2002096945559594244941129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5338925188158917986509677 2002096945559594244941129)
      ·
        refine ⟨1501572709169695683705847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2002096945559594244941129 1501572709169695683705847)
        ·
          refine ⟨2252359063754543525558771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1501572709169695683705847 2252359063754543525558771)
          ·
            refine ⟨3378538595631815288338157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2252359063754543525558771 3378538595631815288338157)
            ·
              refine ⟨1266951973361930733126809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3378538595631815288338157 1266951973361930733126809)
              ·
                refine ⟨950213980021448049845107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1266951973361930733126809 950213980021448049845107)
                ·
                  refine ⟨1425320970032172074767661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 950213980021448049845107 1425320970032172074767661)
                  ·
                    refine ⟨534495363762064528037873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1425320970032172074767661 534495363762064528037873)
                    ·
                      rfl

theorem cell22_1561389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_1561389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561389 prefixEnd_1561389 := by exact prefixLift 1561389
  have htrace : WordTrace (prefixWord ++ tailWord_1561389) baseStart_1561389 baseEnd_1561389 := by
    simpa [prefixWord, tailWord_1561389, baseEnd_1561389] using wordTrace_append hprefix tailTrace_1561389
  have hstable : (prefixWord ++ tailWord_1561389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561389).length < 2 ^ (prefixWord ++ tailWord_1561389).sum := by decide
  have hdescent : baseEnd_1561389 < baseStart_1561389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561411 : List Nat := [1, 1, 1, 3, 1, 4, 3, 3, 2, 3]
def baseStart_1561411 : Nat := 118140960795 + 1561411 * 2 ^ 59
def prefixEnd_1561411 : Nat := 4983230072969 + 3 ^ 40 * 1561411 * 2
def baseEnd_1561411 : Nat := 534502894811663803987805

theorem tailTrace_1561411 : CollatzResearch.WordTrace tailWord_1561411 prefixEnd_1561411 534502894811663803987805 := by
  unfold tailWord_1561411
  simp only [CollatzResearch.WordTrace]
  refine ⟨56949337746282089613404087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37966225164188059742269391 56949337746282089613404087)
  ·
    refine ⟨85424006619423134420106131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56949337746282089613404087 85424006619423134420106131)
    ·
      refine ⟨128136009929134701630159197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85424006619423134420106131 128136009929134701630159197)
      ·
        refine ⟨48051003723425513111309699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128136009929134701630159197 48051003723425513111309699)
        ·
          refine ⟨72076505585138269666964549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48051003723425513111309699 72076505585138269666964549)
          ·
            refine ⟨13514344797213425562555853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72076505585138269666964549 13514344797213425562555853)
            ·
              refine ⟨5067879298955034585958445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13514344797213425562555853 5067879298955034585958445)
              ·
                refine ⟨1900454737108137969734417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5067879298955034585958445 1900454737108137969734417)
                ·
                  refine ⟨1425341052831103477300813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1900454737108137969734417 1425341052831103477300813)
                  ·
                    refine ⟨534502894811663803987805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1425341052831103477300813 534502894811663803987805)
                    ·
                      rfl

theorem cell22_1561411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 3].length) (baseStart_1561411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561411 prefixEnd_1561411 := by exact prefixLift 1561411
  have htrace : WordTrace (prefixWord ++ tailWord_1561411) baseStart_1561411 baseEnd_1561411 := by
    simpa [prefixWord, tailWord_1561411, baseEnd_1561411] using wordTrace_append hprefix tailTrace_1561411
  have hstable : (prefixWord ++ tailWord_1561411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561411).length < 2 ^ (prefixWord ++ tailWord_1561411).sum := by decide
  have hdescent : baseEnd_1561411 < baseStart_1561411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561426 : List Nat := [3, 2, 2, 1, 1, 2, 4, 1, 2, 4]
def baseStart_1561426 : Nat := 118140960795 + 1561426 * 2 ^ 59
def prefixEnd_1561426 : Nat := 4983230072969 + 3 ^ 40 * 1561426 * 2
def baseEnd_1561426 : Nat := 534508029618208764862759

theorem tailTrace_1561426 : CollatzResearch.WordTrace tailWord_1561426 prefixEnd_1561426 534508029618208764862759 := by
  unfold tailWord_1561426
  simp only [CollatzResearch.WordTrace]
  refine ⟨14237471210306936793800033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37966589894151831450133421 14237471210306936793800033)
  ·
    refine ⟨10678103407730202595350025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14237471210306936793800033 10678103407730202595350025)
    ·
      refine ⟨8008577555797651946512519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10678103407730202595350025 8008577555797651946512519)
      ·
        refine ⟨12012866333696477919768779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8008577555797651946512519 12012866333696477919768779)
        ·
          refine ⟨18019299500544716879653169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12012866333696477919768779 18019299500544716879653169)
          ·
            refine ⟨13514474625408537659739877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18019299500544716879653169 13514474625408537659739877)
            ·
              refine ⟨2533963992264100811201227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13514474625408537659739877 2533963992264100811201227)
              ·
                refine ⟨3800945988396151216801841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533963992264100811201227 3800945988396151216801841)
                ·
                  refine ⟨2850709491297113412601381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3800945988396151216801841 2850709491297113412601381)
                  ·
                    refine ⟨534508029618208764862759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2850709491297113412601381 534508029618208764862759)
                    ·
                      rfl

theorem cell22_1561426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_1561426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561426 prefixEnd_1561426 := by exact prefixLift 1561426
  have htrace : WordTrace (prefixWord ++ tailWord_1561426) baseStart_1561426 baseEnd_1561426 := by
    simpa [prefixWord, tailWord_1561426, baseEnd_1561426] using wordTrace_append hprefix tailTrace_1561426
  have hstable : (prefixWord ++ tailWord_1561426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561426).length < 2 ^ (prefixWord ++ tailWord_1561426).sum := by decide
  have hdescent : baseEnd_1561426 < baseStart_1561426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561503 : List Nat := [1, 1, 2, 5, 2, 3, 1, 2, 5]
def baseStart_1561503 : Nat := 118140960795 + 1561503 * 2 ^ 59
def prefixEnd_1561503 : Nat := 4983230072969 + 3 ^ 40 * 1561503 * 2
def baseEnd_1561503 : Nat := 178178129430602076895841

theorem tailTrace_1561503 : CollatzResearch.WordTrace tailWord_1561503 prefixEnd_1561503 178178129430602076895841 := by
  unfold tailWord_1561503
  simp only [CollatzResearch.WordTrace]
  refine ⟨56952693261948789325753163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37968462174632526217168775 56952693261948789325753163)
  ·
    refine ⟨85429039892923183988629745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56952693261948789325753163 85429039892923183988629745)
    ·
      refine ⟨64071779919692387991472309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85429039892923183988629745 64071779919692387991472309)
      ·
        refine ⟨6006729367471161374200529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64071779919692387991472309 6006729367471161374200529)
        ·
          refine ⟨4505047025603371030650397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6006729367471161374200529 4505047025603371030650397)
          ·
            refine ⟨1689392634601264136493899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4505047025603371030650397 1689392634601264136493899)
            ·
              refine ⟨2534088951901896204740849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1689392634601264136493899 2534088951901896204740849)
              ·
                refine ⟨1900566713926422153555637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2534088951901896204740849 1900566713926422153555637)
                ·
                  refine ⟨178178129430602076895841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1900566713926422153555637 178178129430602076895841)
                  ·
                    rfl

theorem cell22_1561503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 5].length) (baseStart_1561503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561503 prefixEnd_1561503 := by exact prefixLift 1561503
  have htrace : WordTrace (prefixWord ++ tailWord_1561503) baseStart_1561503 baseEnd_1561503 := by
    simpa [prefixWord, tailWord_1561503, baseEnd_1561503] using wordTrace_append hprefix tailTrace_1561503
  have hstable : (prefixWord ++ tailWord_1561503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561503).length < 2 ^ (prefixWord ++ tailWord_1561503).sum := by decide
  have hdescent : baseEnd_1561503 < baseStart_1561503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561561 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 4, 4]
def baseStart_1561561 : Nat := 118140960795 + 1561561 * 2 ^ 59
def prefixEnd_1561561 : Nat := 4983230072969 + 3 ^ 40 * 1561561 * 2
def baseEnd_1561561 : Nat := 534554242877113412737345

theorem tailTrace_1561561 : CollatzResearch.WordTrace tailWord_1561561 prefixEnd_1561561 534554242877113412737345 := by
  unfold tailWord_1561561
  simp only [CollatzResearch.WordTrace]
  refine ⟨56954808695738665231364537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37969872463825776820909691 56954808695738665231364537)
  ·
    refine ⟨42716106521803998923523403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56954808695738665231364537 42716106521803998923523403)
    ·
      refine ⟨64074159782705998385285105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42716106521803998923523403 64074159782705998385285105)
      ·
        refine ⟨48055619837029498788963829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64074159782705998385285105 48055619837029498788963829)
        ·
          refine ⟨4505214359721515511465359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48055619837029498788963829 4505214359721515511465359)
          ·
            refine ⟨6757821539582273267198039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4505214359721515511465359 6757821539582273267198039)
            ·
              refine ⟨10136732309373409900797059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6757821539582273267198039 10136732309373409900797059)
              ·
                refine ⟨15205098464060114851195589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10136732309373409900797059 15205098464060114851195589)
                ·
                  refine ⟨2850955962011271534599173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15205098464060114851195589 2850955962011271534599173)
                  ·
                    refine ⟨534554242877113412737345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2850955962011271534599173 534554242877113412737345)
                    ·
                      rfl

theorem cell22_1561561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 4].length) (baseStart_1561561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561561 prefixEnd_1561561 := by exact prefixLift 1561561
  have htrace : WordTrace (prefixWord ++ tailWord_1561561) baseStart_1561561 baseEnd_1561561 := by
    simpa [prefixWord, tailWord_1561561, baseEnd_1561561] using wordTrace_append hprefix tailTrace_1561561
  have hstable : (prefixWord ++ tailWord_1561561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561561).length < 2 ^ (prefixWord ++ tailWord_1561561).sum := by decide
  have hdescent : baseEnd_1561561 < baseStart_1561561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561670 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_1561670 : Nat := 118140960795 + 1561670 * 2 ^ 59
def prefixEnd_1561670 : Nat := 4983230072969 + 3 ^ 40 * 1561670 * 2
def baseEnd_1561670 : Nat := 534591555804673461762011

theorem tailTrace_1561670 : CollatzResearch.WordTrace tailWord_1561670 prefixEnd_1561670 534591555804673461762011 := by
  unfold tailWord_1561670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1779962007885743026471327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37972522834895851231388309 1779962007885743026471327)
  ·
    refine ⟨2669943011828614539706991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1779962007885743026471327 2669943011828614539706991)
    ·
      refine ⟨4004914517742921809560487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2669943011828614539706991 4004914517742921809560487)
      ·
        refine ⟨6007371776614382714340731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4004914517742921809560487 6007371776614382714340731)
        ·
          refine ⟨9011057664921574071511097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6007371776614382714340731 9011057664921574071511097)
          ·
            refine ⟨6758293248691180553633323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9011057664921574071511097 6758293248691180553633323)
            ·
              refine ⟨10137439873036770830449985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6758293248691180553633323 10137439873036770830449985)
              ·
                refine ⟨7603079904777578122837489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10137439873036770830449985 7603079904777578122837489)
                ·
                  refine ⟨5702309928583183592128117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7603079904777578122837489 5702309928583183592128117)
                  ·
                    refine ⟨534591555804673461762011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5702309928583183592128117 534591555804673461762011)
                    ·
                      rfl

theorem cell22_1561670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_1561670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561670 prefixEnd_1561670 := by exact prefixLift 1561670
  have htrace : WordTrace (prefixWord ++ tailWord_1561670) baseStart_1561670 baseEnd_1561670 := by
    simpa [prefixWord, tailWord_1561670, baseEnd_1561670] using wordTrace_append hprefix tailTrace_1561670
  have hstable : (prefixWord ++ tailWord_1561670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561670).length < 2 ^ (prefixWord ++ tailWord_1561670).sum := by decide
  have hdescent : baseEnd_1561670 < baseStart_1561670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561681 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 3, 5]
def baseStart_1561681 : Nat := 118140960795 + 1561681 * 2 ^ 59
def prefixEnd_1561681 : Nat := 4983230072969 + 3 ^ 40 * 1561681 * 2
def baseEnd_1561681 : Nat := 534595321329473099736977

theorem tailTrace_1561681 : CollatzResearch.WordTrace tailWord_1561681 prefixEnd_1561681 534595321329473099736977 := by
  unfold tailWord_1561681
  simp only [CollatzResearch.WordTrace]
  refine ⟨56959185455303925725732897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37972790303535950483821931 56959185455303925725732897)
  ·
    refine ⟨42719389091477944294299673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56959185455303925725732897 42719389091477944294299673)
    ·
      refine ⟨32039541818608458220724755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42719389091477944294299673 32039541818608458220724755)
      ·
        refine ⟨48059312727912687331087133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32039541818608458220724755 48059312727912687331087133)
        ·
          refine ⟨18022242272967257749157675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48059312727912687331087133 18022242272967257749157675)
          ·
            refine ⟨27033363409450886623736513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18022242272967257749157675 27033363409450886623736513)
            ·
              refine ⟨20275022557088164967802385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27033363409450886623736513 20275022557088164967802385)
              ·
                refine ⟨15206266917816123725851789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20275022557088164967802385 15206266917816123725851789)
                ·
                  refine ⟨5702350094181046397194421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15206266917816123725851789 5702350094181046397194421)
                  ·
                    refine ⟨534595321329473099736977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5702350094181046397194421 534595321329473099736977)
                    ·
                      rfl

theorem cell22_1561681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_1561681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561681 prefixEnd_1561681 := by exact prefixLift 1561681
  have htrace : WordTrace (prefixWord ++ tailWord_1561681) baseStart_1561681 baseEnd_1561681 := by
    simpa [prefixWord, tailWord_1561681, baseEnd_1561681] using wordTrace_append hprefix tailTrace_1561681
  have hstable : (prefixWord ++ tailWord_1561681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561681).length < 2 ^ (prefixWord ++ tailWord_1561681).sum := by decide
  have hdescent : baseEnd_1561681 < baseStart_1561681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
