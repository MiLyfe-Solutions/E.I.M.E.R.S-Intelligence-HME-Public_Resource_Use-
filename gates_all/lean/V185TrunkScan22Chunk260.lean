import V185TrunkScan22Chunk259

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2319338 : List Nat := [3, 1, 3, 1, 2, 3, 1, 8]
def baseStart_2319338 : Nat := 118140960795 + 2319338 * 2 ^ 59
def prefixEnd_2319338 : Nat := 4983230072969 + 3 ^ 40 * 2319338 * 2
def baseEnd_2319338 : Nat := 88217421795389023193227

theorem tailTrace_2319338 : CollatzResearch.WordTrace tailWord_2319338 prefixEnd_2319338 88217421795389023193227 := by
  unfold tailWord_2319338
  simp only [CollatzResearch.WordTrace]
  refine ⟨21148301617860503059867667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56395470980961341492980445 21148301617860503059867667)
  ·
    refine ⟨31722452426790754589801501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21148301617860503059867667 31722452426790754589801501)
    ·
      refine ⟨11895919660046532971175563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31722452426790754589801501 11895919660046532971175563)
      ·
        refine ⟨17843879490069799456763345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11895919660046532971175563 17843879490069799456763345)
        ·
          refine ⟨13382909617552349592572509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17843879490069799456763345 13382909617552349592572509)
          ·
            refine ⟨5018591106582131097214691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13382909617552349592572509 5018591106582131097214691)
            ·
              refine ⟨7527886659873196645822037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5018591106582131097214691 7527886659873196645822037)
              ·
                refine ⟨88217421795389023193227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7527886659873196645822037 88217421795389023193227)
                ·
                  rfl

theorem cell22_2319338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 8].length) (baseStart_2319338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319338 prefixEnd_2319338 := by exact prefixLift 2319338
  have htrace : WordTrace (prefixWord ++ tailWord_2319338) baseStart_2319338 baseEnd_2319338 := by
    simpa [prefixWord, tailWord_2319338, baseEnd_2319338] using wordTrace_append hprefix tailTrace_2319338
  have hstable : (prefixWord ++ tailWord_2319338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319338).length < 2 ^ (prefixWord ++ tailWord_2319338).sum := by decide
  have hdescent : baseEnd_2319338 < baseStart_2319338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319421 : List Nat := [1, 4, 1, 3, 1, 4, 2, 2, 1, 3]
def baseStart_2319421 : Nat := 118140960795 + 2319421 * 2 ^ 59
def prefixEnd_2319421 : Nat := 4983230072969 + 3 ^ 40 * 2319421 * 2
def baseEnd_2319421 : Nat := 793985208754716658913789

theorem tailTrace_2319421 : CollatzResearch.WordTrace tailWord_2319421 prefixEnd_2319421 793985208754716658913789 := by
  unfold tailWord_2319421
  simp only [CollatzResearch.WordTrace]
  refine ⟨84596233730141317414742117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56397489153427544943161411 84596233730141317414742117)
  ·
    refine ⟨15861793824401497015264147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84596233730141317414742117 15861793824401497015264147)
    ·
      refine ⟨23792690736602245522896221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15861793824401497015264147 23792690736602245522896221)
      ·
        refine ⟨8922259026225842071086083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23792690736602245522896221 8922259026225842071086083)
        ·
          refine ⟨13383388539338763106629125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8922259026225842071086083 13383388539338763106629125)
          ·
            refine ⟨2509385351126018082492961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13383388539338763106629125 2509385351126018082492961)
            ·
              refine ⟨1882039013344513561869721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2509385351126018082492961 1882039013344513561869721)
              ·
                refine ⟨1411529260008385171402291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1882039013344513561869721 1411529260008385171402291)
                ·
                  refine ⟨2117293890012577757103437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1411529260008385171402291 2117293890012577757103437)
                  ·
                    refine ⟨793985208754716658913789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2117293890012577757103437 793985208754716658913789)
                    ·
                      rfl

theorem cell22_2319421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_2319421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319421 prefixEnd_2319421 := by exact prefixLift 2319421
  have htrace : WordTrace (prefixWord ++ tailWord_2319421) baseStart_2319421 baseEnd_2319421 := by
    simpa [prefixWord, tailWord_2319421, baseEnd_2319421] using wordTrace_append hprefix tailTrace_2319421
  have hstable : (prefixWord ++ tailWord_2319421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319421).length < 2 ^ (prefixWord ++ tailWord_2319421).sum := by decide
  have hdescent : baseEnd_2319421 < baseStart_2319421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319443 : List Nat := [1, 1, 1, 2, 1, 1, 2, 7, 1, 5]
def baseStart_2319443 : Nat := 118140960795 + 2319443 * 2 ^ 59
def prefixEnd_2319443 : Nat := 4983230072969 + 3 ^ 40 * 2319443 * 2
def baseEnd_2319443 : Nat := 793992739804315934863721

theorem tailTrace_2319443 : CollatzResearch.WordTrace tailWord_2319443 prefixEnd_2319443 793992739804315934863721 := by
  unfold tailWord_2319443
  simp only [CollatzResearch.WordTrace]
  refine ⟨84597036136061615172042983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56398024090707743448028655 84597036136061615172042983)
  ·
    refine ⟨126895554204092422758064475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84597036136061615172042983 126895554204092422758064475)
    ·
      refine ⟨190343331306138634137096713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126895554204092422758064475 190343331306138634137096713)
      ·
        refine ⟨142757498479603975602822535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190343331306138634137096713 142757498479603975602822535)
        ·
          refine ⟨214136247719405963404233803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142757498479603975602822535 214136247719405963404233803)
          ·
            refine ⟨321204371579108945106350705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214136247719405963404233803 321204371579108945106350705)
            ·
              refine ⟨240903278684331708829763029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321204371579108945106350705 240903278684331708829763029)
              ·
                refine ⟨5646170594164024425697571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 240903278684331708829763029 5646170594164024425697571)
                ·
                  refine ⟨8469255891246036638546357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5646170594164024425697571 8469255891246036638546357)
                  ·
                    refine ⟨793992739804315934863721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8469255891246036638546357 793992739804315934863721)
                    ·
                      rfl

theorem cell22_2319443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 5].length) (baseStart_2319443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319443 prefixEnd_2319443 := by exact prefixLift 2319443
  have htrace : WordTrace (prefixWord ++ tailWord_2319443) baseStart_2319443 baseEnd_2319443 := by
    simpa [prefixWord, tailWord_2319443, baseEnd_2319443] using wordTrace_append hprefix tailTrace_2319443
  have hstable : (prefixWord ++ tailWord_2319443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319443).length < 2 ^ (prefixWord ++ tailWord_2319443).sum := by decide
  have hdescent : baseEnd_2319443 < baseStart_2319443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319460 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 4, 3]
def baseStart_2319460 : Nat := 118140960795 + 2319460 * 2 ^ 59
def prefixEnd_2319460 : Nat := 4983230072969 + 3 ^ 40 * 2319460 * 2
def baseEnd_2319460 : Nat := 793998559251733557188669

theorem tailTrace_2319460 : CollatzResearch.WordTrace tailWord_2319460 prefixEnd_2319460 793998559251733557188669 := by
  unfold tailWord_2319460
  simp only [CollatzResearch.WordTrace]
  refine ⟨42298828088500013537705917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56398437451333351383607889 42298828088500013537705917)
  ·
    refine ⟨15862060533187505076639719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42298828088500013537705917 15862060533187505076639719)
    ·
      refine ⟨23793090799781257614959579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15862060533187505076639719 23793090799781257614959579)
      ·
        refine ⟨35689636199671886422439369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23793090799781257614959579 35689636199671886422439369)
        ·
          refine ⟨26767227149753914816829527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35689636199671886422439369 26767227149753914816829527)
          ·
            refine ⟨40150840724630872225244291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26767227149753914816829527 40150840724630872225244291)
            ·
              refine ⟨60226261086946308337866437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40150840724630872225244291 60226261086946308337866437)
              ·
                refine ⟨11292423953802432813349957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60226261086946308337866437 11292423953802432813349957)
                ·
                  refine ⟨2117329491337956152503117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11292423953802432813349957 2117329491337956152503117)
                  ·
                    refine ⟨793998559251733557188669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2117329491337956152503117 793998559251733557188669)
                    ·
                      rfl

theorem cell22_2319460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_2319460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319460 prefixEnd_2319460 := by exact prefixLift 2319460
  have htrace : WordTrace (prefixWord ++ tailWord_2319460) baseStart_2319460 baseEnd_2319460 := by
    simpa [prefixWord, tailWord_2319460, baseEnd_2319460] using wordTrace_append hprefix tailTrace_2319460
  have hstable : (prefixWord ++ tailWord_2319460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319460).length < 2 ^ (prefixWord ++ tailWord_2319460).sum := by decide
  have hdescent : baseEnd_2319460 < baseStart_2319460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319464 : List Nat := [2, 1, 4, 4, 1, 1, 1, 3, 1, 4]
def baseStart_2319464 : Nat := 118140960795 + 2319464 * 2 ^ 59
def prefixEnd_2319464 : Nat := 4983230072969 + 3 ^ 40 * 2319464 * 2
def baseEnd_2319464 : Nat := 793999928533478880088657

theorem tailTrace_2319464 : CollatzResearch.WordTrace tailWord_2319464 prefixEnd_2319464 793999928533478880088657 := by
  unfold tailWord_2319464
  simp only [CollatzResearch.WordTrace]
  refine ⟨42298901034492767879278723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56398534712657023839038297 42298901034492767879278723)
  ·
    refine ⟨63448351551739151818918085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42298901034492767879278723 63448351551739151818918085)
    ·
      refine ⟨11896565915951090966047141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63448351551739151818918085 11896565915951090966047141)
      ·
        refine ⟨2230606109240829556133839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11896565915951090966047141 2230606109240829556133839)
        ·
          refine ⟨3345909163861244334200759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2230606109240829556133839 3345909163861244334200759)
          ·
            refine ⟨5018863745791866501301139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3345909163861244334200759 5018863745791866501301139)
            ·
              refine ⟨7528295618687799751951709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5018863745791866501301139 7528295618687799751951709)
              ·
                refine ⟨2823110857007924906981891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7528295618687799751951709 2823110857007924906981891)
                ·
                  refine ⟨4234666285511887360472837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2823110857007924906981891 4234666285511887360472837)
                  ·
                    refine ⟨793999928533478880088657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4234666285511887360472837 793999928533478880088657)
                    ·
                      rfl

theorem cell22_2319464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_2319464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319464 prefixEnd_2319464 := by exact prefixLift 2319464
  have htrace : WordTrace (prefixWord ++ tailWord_2319464) baseStart_2319464 baseEnd_2319464 := by
    simpa [prefixWord, tailWord_2319464, baseEnd_2319464] using wordTrace_append hprefix tailTrace_2319464
  have hstable : (prefixWord ++ tailWord_2319464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319464).length < 2 ^ (prefixWord ++ tailWord_2319464).sum := by decide
  have hdescent : baseEnd_2319464 < baseStart_2319464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319552 : List Nat := [2, 1, 1, 2, 6, 1, 1, 3, 5]
def baseStart_2319552 : Nat := 118140960795 + 2319552 * 2 ^ 59
def prefixEnd_2319552 : Nat := 4983230072969 + 3 ^ 40 * 2319552 * 2
def baseEnd_2319552 : Nat := 264676684243958661296129

theorem tailTrace_2319552 : CollatzResearch.WordTrace tailWord_2319552 prefixEnd_2319552 264676684243958661296129 := by
  unfold tailWord_2319552
  simp only [CollatzResearch.WordTrace]
  refine ⟨42300505846333363393880455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56400674461777817858507273 42300505846333363393880455)
  ·
    refine ⟨63450758769500045090820683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42300505846333363393880455 63450758769500045090820683)
    ·
      refine ⟨95176138154250067636231025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63450758769500045090820683 95176138154250067636231025)
      ·
        refine ⟨71382103615687550727173269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95176138154250067636231025 71382103615687550727173269)
        ·
          refine ⟨3346036106985353940336247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 71382103615687550727173269 3346036106985353940336247)
          ·
            refine ⟨5019054160478030910504371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3346036106985353940336247 5019054160478030910504371)
            ·
              refine ⟨7528581240717046365756557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5019054160478030910504371 7528581240717046365756557)
              ·
                refine ⟨2823217965268892387158709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7528581240717046365756557 2823217965268892387158709)
                ·
                  refine ⟨264676684243958661296129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2823217965268892387158709 264676684243958661296129)
                  ·
                    rfl

theorem cell22_2319552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 5].length) (baseStart_2319552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319552 prefixEnd_2319552 := by exact prefixLift 2319552
  have htrace : WordTrace (prefixWord ++ tailWord_2319552) baseStart_2319552 baseEnd_2319552 := by
    simpa [prefixWord, tailWord_2319552, baseEnd_2319552] using wordTrace_append hprefix tailTrace_2319552
  have hstable : (prefixWord ++ tailWord_2319552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319552).length < 2 ^ (prefixWord ++ tailWord_2319552).sum := by decide
  have hdescent : baseEnd_2319552 < baseStart_2319552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319610 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 1, 6]
def baseStart_2319610 : Nat := 118140960795 + 2319610 * 2 ^ 59
def prefixEnd_2319610 : Nat := 4983230072969 + 3 ^ 40 * 2319610 * 2
def baseEnd_2319610 : Nat := 794049907317183165938209

theorem tailTrace_2319610 : CollatzResearch.WordTrace tailWord_2319610 prefixEnd_2319610 794049907317183165938209 := by
  unfold tailWord_2319610
  simp only [CollatzResearch.WordTrace]
  refine ⟨21150781781614150673343071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56402084750971068462248189 21150781781614150673343071)
  ·
    refine ⟨31726172672421226010014607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21150781781614150673343071 31726172672421226010014607)
    ·
      refine ⟨47589259008631839015021911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31726172672421226010014607 47589259008631839015021911)
      ·
        refine ⟨71383888512947758522532867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47589259008631839015021911 71383888512947758522532867)
        ·
          refine ⟨107075832769421637783799301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71383888512947758522532867 107075832769421637783799301)
          ·
            refine ⟨20076718644266557084462369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107075832769421637783799301 20076718644266557084462369)
            ·
              refine ⟨15057538983199917813346777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20076718644266557084462369 15057538983199917813346777)
              ·
                refine ⟨11293154237399938360010083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15057538983199917813346777 11293154237399938360010083)
                ·
                  refine ⟨16939731356099907540015125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11293154237399938360010083 16939731356099907540015125)
                  ·
                    refine ⟨794049907317183165938209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16939731356099907540015125 794049907317183165938209)
                    ·
                      rfl

theorem cell22_2319610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_2319610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319610 prefixEnd_2319610 := by exact prefixLift 2319610
  have htrace : WordTrace (prefixWord ++ tailWord_2319610) baseStart_2319610 baseEnd_2319610 := by
    simpa [prefixWord, tailWord_2319610, baseEnd_2319610] using wordTrace_append hprefix tailTrace_2319610
  have hstable : (prefixWord ++ tailWord_2319610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319610).length < 2 ^ (prefixWord ++ tailWord_2319610).sum := by decide
  have hdescent : baseEnd_2319610 < baseStart_2319610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319627 : List Nat := [1, 1, 1, 1, 5, 3, 3, 1, 2, 4]
def baseStart_2319627 : Nat := 118140960795 + 2319627 * 2 ^ 59
def prefixEnd_2319627 : Nat := 4983230072969 + 3 ^ 40 * 2319627 * 2
def baseEnd_2319627 : Nat := 794055726764600788263157

theorem tailTrace_2319627 : CollatzResearch.WordTrace tailWord_2319627 prefixEnd_2319627 794055726764600788263157 := by
  unfold tailWord_2319627
  simp only [CollatzResearch.WordTrace]
  refine ⟨84603747167395014596741135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56402498111596676397827423 84603747167395014596741135)
  ·
    refine ⟨126905620751092521895111703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84603747167395014596741135 126905620751092521895111703)
    ·
      refine ⟨190358431126638782842667555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126905620751092521895111703 190358431126638782842667555)
      ·
        refine ⟨285537646689958174264001333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190358431126638782842667555 285537646689958174264001333)
        ·
          refine ⟨26769154377183578837250125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 285537646689958174264001333 26769154377183578837250125)
          ·
            refine ⟨10038432891443842063968797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26769154377183578837250125 10038432891443842063968797)
            ·
              refine ⟨3764412334291440773988299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10038432891443842063968797 3764412334291440773988299)
              ·
                refine ⟨5646618501437161160982449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3764412334291440773988299 5646618501437161160982449)
                ·
                  refine ⟨4234963876077870870736837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5646618501437161160982449 4234963876077870870736837)
                  ·
                    refine ⟨794055726764600788263157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4234963876077870870736837 794055726764600788263157)
                    ·
                      rfl

theorem cell22_2319627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 4].length) (baseStart_2319627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319627 prefixEnd_2319627 := by exact prefixLift 2319627
  have htrace : WordTrace (prefixWord ++ tailWord_2319627) baseStart_2319627 baseEnd_2319627 := by
    simpa [prefixWord, tailWord_2319627, baseEnd_2319627] using wordTrace_append hprefix tailTrace_2319627
  have hstable : (prefixWord ++ tailWord_2319627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319627).length < 2 ^ (prefixWord ++ tailWord_2319627).sum := by decide
  have hdescent : baseEnd_2319627 < baseStart_2319627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319685 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 1, 7]
def baseStart_2319685 : Nat := 118140960795 + 2319685 * 2 ^ 59
def prefixEnd_2319685 : Nat := 4983230072969 + 3 ^ 40 * 2319685 * 2
def baseEnd_2319685 : Nat := 794075581349907970312979

theorem tailTrace_2319685 : CollatzResearch.WordTrace tailWord_2319685 prefixEnd_2319685 794075581349907970312979 := by
  unfold tailWord_2319685
  simp only [CollatzResearch.WordTrace]
  refine ⟨84605862601184890502352509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56403908400789927001568339 84605862601184890502352509)
  ·
    refine ⟨31727198475444333938382191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84605862601184890502352509 31727198475444333938382191)
    ·
      refine ⟨47590797713166500907573287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31727198475444333938382191 47590797713166500907573287)
      ·
        refine ⟨71386196569749751361359931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47590797713166500907573287 71386196569749751361359931)
        ·
          refine ⟨107079294854624627042039897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71386196569749751361359931 107079294854624627042039897)
          ·
            refine ⟨80309471140968470281529923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107079294854624627042039897 80309471140968470281529923)
            ·
              refine ⟨120464206711452705422294885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80309471140968470281529923 120464206711452705422294885)
              ·
                refine ⟨22587038758397382266680291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120464206711452705422294885 22587038758397382266680291)
                ·
                  refine ⟨33880558137596073400020437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22587038758397382266680291 33880558137596073400020437)
                  ·
                    refine ⟨794075581349907970312979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33880558137596073400020437 794075581349907970312979)
                    ·
                      rfl

theorem cell22_2319685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_2319685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319685 prefixEnd_2319685 := by exact prefixLift 2319685
  have htrace : WordTrace (prefixWord ++ tailWord_2319685) baseStart_2319685 baseEnd_2319685 := by
    simpa [prefixWord, tailWord_2319685, baseEnd_2319685] using wordTrace_append hprefix tailTrace_2319685
  have hstable : (prefixWord ++ tailWord_2319685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319685).length < 2 ^ (prefixWord ++ tailWord_2319685).sum := by decide
  have hdescent : baseEnd_2319685 < baseStart_2319685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319717 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 3, 4]
def baseStart_2319717 : Nat := 118140960795 + 2319717 * 2 ^ 59
def prefixEnd_2319717 : Nat := 4983230072969 + 3 ^ 40 * 2319717 * 2
def baseEnd_2319717 : Nat := 794086535603870553512881

theorem tailTrace_2319717 : CollatzResearch.WordTrace tailWord_2319717 prefixEnd_2319717 794086535603870553512881 := by
  unfold tailWord_2319717
  simp only [CollatzResearch.WordTrace]
  refine ⟨84607029737068959967517405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56404686491379306645011603 84607029737068959967517405)
  ·
    refine ⟨31727636151400859987819027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84607029737068959967517405 31727636151400859987819027)
    ·
      refine ⟨47591454227101289981728541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31727636151400859987819027 47591454227101289981728541)
      ·
        refine ⟨17846795335162983743148203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47591454227101289981728541 17846795335162983743148203)
        ·
          refine ⟨26770193002744475614722305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17846795335162983743148203 26770193002744475614722305)
          ·
            refine ⟨20077644752058356711041729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26770193002744475614722305 20077644752058356711041729)
            ·
              refine ⟨15058233564043767533281297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20077644752058356711041729 15058233564043767533281297)
              ·
                refine ⟨11293675173032825649960973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15058233564043767533281297 11293675173032825649960973)
                ·
                  refine ⟨4235128189887309618735365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11293675173032825649960973 4235128189887309618735365)
                  ·
                    refine ⟨794086535603870553512881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4235128189887309618735365 794086535603870553512881)
                    ·
                      rfl

theorem cell22_2319717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_2319717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319717 prefixEnd_2319717 := by exact prefixLift 2319717
  have htrace : WordTrace (prefixWord ++ tailWord_2319717) baseStart_2319717 baseEnd_2319717 := by
    simpa [prefixWord, tailWord_2319717, baseEnd_2319717] using wordTrace_append hprefix tailTrace_2319717
  have hstable : (prefixWord ++ tailWord_2319717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319717).length < 2 ^ (prefixWord ++ tailWord_2319717).sum := by decide
  have hdescent : baseEnd_2319717 < baseStart_2319717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319747 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 3, 5]
def baseStart_2319747 : Nat := 118140960795 + 2319747 * 2 ^ 59
def prefixEnd_2319747 : Nat := 4983230072969 + 3 ^ 40 * 2319747 * 2
def baseEnd_2319747 : Nat := 794096805216960475262789

theorem tailTrace_2319747 : CollatzResearch.WordTrace tailWord_2319747 prefixEnd_2319747 794096805216960475262789 := by
  unfold tailWord_2319747
  simp only [CollatzResearch.WordTrace]
  refine ⟨84608123926960275091109495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56405415951306850060739663 84608123926960275091109495)
  ·
    refine ⟨126912185890440412636664243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84608123926960275091109495 126912185890440412636664243)
    ·
      refine ⟨190368278835660618954996365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126912185890440412636664243 190368278835660618954996365)
      ·
        refine ⟨71388104563372732108123637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190368278835660618954996365 71388104563372732108123637)
        ·
          refine ⟨6692634802816193635136591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71388104563372732108123637 6692634802816193635136591)
          ·
            refine ⟨10038952204224290452704887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6692634802816193635136591 10038952204224290452704887)
            ·
              refine ⟨15058428306336435679057331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10038952204224290452704887 15058428306336435679057331)
              ·
                refine ⟨22587642459504653518585997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15058428306336435679057331 22587642459504653518585997)
                ·
                  refine ⟨8470365922314245069469749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22587642459504653518585997 8470365922314245069469749)
                  ·
                    refine ⟨794096805216960475262789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8470365922314245069469749 794096805216960475262789)
                    ·
                      rfl

theorem cell22_2319747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 5].length) (baseStart_2319747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319747 prefixEnd_2319747 := by exact prefixLift 2319747
  have htrace : WordTrace (prefixWord ++ tailWord_2319747) baseStart_2319747 baseEnd_2319747 := by
    simpa [prefixWord, tailWord_2319747, baseEnd_2319747] using wordTrace_append hprefix tailTrace_2319747
  have hstable : (prefixWord ++ tailWord_2319747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319747).length < 2 ^ (prefixWord ++ tailWord_2319747).sum := by decide
  have hdescent : baseEnd_2319747 < baseStart_2319747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319751 : List Nat := [1, 1, 4, 2, 2, 3, 3, 1, 1, 4]
def baseStart_2319751 : Nat := 118140960795 + 2319751 * 2 ^ 59
def prefixEnd_2319751 : Nat := 4983230072969 + 3 ^ 40 * 2319751 * 2
def baseEnd_2319751 : Nat := 794098174498705798162777

theorem tailTrace_2319751 : CollatzResearch.WordTrace tailWord_2319751 prefixEnd_2319751 794098174498705798162777 := by
  unfold tailWord_2319751
  simp only [CollatzResearch.WordTrace]
  refine ⟨84608269818945783774255107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56405513212630522516170071 84608269818945783774255107)
  ·
    refine ⟨126912404728418675661382661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84608269818945783774255107 126912404728418675661382661)
    ·
      refine ⟨23796075886578501686509249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126912404728418675661382661 23796075886578501686509249)
      ·
        refine ⟨17847056914933876264881937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23796075886578501686509249 17847056914933876264881937)
        ·
          refine ⟨13385292686200407198661453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17847056914933876264881937 13385292686200407198661453)
          ·
            refine ⟨5019484757325152699498045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13385292686200407198661453 5019484757325152699498045)
            ·
              refine ⟨1882306783996932262311767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5019484757325152699498045 1882306783996932262311767)
              ·
                refine ⟨2823460175995398393467651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1882306783996932262311767 2823460175995398393467651)
                ·
                  refine ⟨4235190263993097590201477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2823460175995398393467651 4235190263993097590201477)
                  ·
                    refine ⟨794098174498705798162777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4235190263993097590201477 794098174498705798162777)
                    ·
                      rfl

theorem cell22_2319751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_2319751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319751 prefixEnd_2319751 := by exact prefixLift 2319751
  have htrace : WordTrace (prefixWord ++ tailWord_2319751) baseStart_2319751 baseEnd_2319751 := by
    simpa [prefixWord, tailWord_2319751, baseEnd_2319751] using wordTrace_append hprefix tailTrace_2319751
  have hstable : (prefixWord ++ tailWord_2319751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319751).length < 2 ^ (prefixWord ++ tailWord_2319751).sum := by decide
  have hdescent : baseEnd_2319751 < baseStart_2319751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320051 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 4, 3]
def baseStart_2320051 : Nat := 118140960795 + 2320051 * 2 ^ 59
def prefixEnd_2320051 : Nat := 4983230072969 + 3 ^ 40 * 2320051 * 2
def baseEnd_2320051 : Nat := 794200870629605015661857

theorem tailTrace_2320051 : CollatzResearch.WordTrace tailWord_2320051 prefixEnd_2320051 794200870629605015661857 := by
  unfold tailWord_2320051
  simp only [CollatzResearch.WordTrace]
  refine ⟨84619211717858935010176007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56412807811905956673450671 84619211717858935010176007)
  ·
    refine ⟨126928817576788402515264011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84619211717858935010176007 126928817576788402515264011)
    ·
      refine ⟨190393226365182603772896017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126928817576788402515264011 190393226365182603772896017)
      ·
        refine ⟨142794919773886952829672013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190393226365182603772896017 142794919773886952829672013)
        ·
          refine ⟨53548094915207607311127005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142794919773886952829672013 53548094915207607311127005)
          ·
            refine ⟨20080535593202852741672627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53548094915207607311127005 20080535593202852741672627)
            ·
              refine ⟨30120803389804279112508941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20080535593202852741672627 30120803389804279112508941)
              ·
                refine ⟨11295301271176604667190853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30120803389804279112508941 11295301271176604667190853)
                ·
                  refine ⟨2117868988345613375098285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11295301271176604667190853 2117868988345613375098285)
                  ·
                    refine ⟨794200870629605015661857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2117868988345613375098285 794200870629605015661857)
                    ·
                      rfl

theorem cell22_2320051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 3].length) (baseStart_2320051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320051 prefixEnd_2320051 := by exact prefixLift 2320051
  have htrace : WordTrace (prefixWord ++ tailWord_2320051) baseStart_2320051 baseEnd_2320051 := by
    simpa [prefixWord, tailWord_2320051, baseEnd_2320051] using wordTrace_append hprefix tailTrace_2320051
  have hstable : (prefixWord ++ tailWord_2320051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320051).length < 2 ^ (prefixWord ++ tailWord_2320051).sum := by decide
  have hdescent : baseEnd_2320051 < baseStart_2320051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320079 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 2, 7]
def baseStart_2320079 : Nat := 118140960795 + 2320079 * 2 ^ 59
def prefixEnd_2320079 : Nat := 4983230072969 + 3 ^ 40 * 2320079 * 2
def baseEnd_2320079 : Nat := 794210455601822275961771

theorem tailTrace_2320079 : CollatzResearch.WordTrace tailWord_2320079 prefixEnd_2320079 794210455601822275961771 := by
  unfold tailWord_2320079
  simp only [CollatzResearch.WordTrace]
  refine ⟨84620232961757495792195291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56413488641171663861463527 84620232961757495792195291)
  ·
    refine ⟨126930349442636243688292937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84620232961757495792195291 126930349442636243688292937)
    ·
      refine ⟨95197762081977182766219703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126930349442636243688292937 95197762081977182766219703)
      ·
        refine ⟨142796643122965774149329555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95197762081977182766219703 142796643122965774149329555)
        ·
          refine ⟨214194964684448661223994333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142796643122965774149329555 214194964684448661223994333)
          ·
            refine ⟨80323111756668247958997875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 214194964684448661223994333 80323111756668247958997875)
            ·
              refine ⟨120484667635002371938496813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80323111756668247958997875 120484667635002371938496813)
              ·
                refine ⟨45181750363125889476936305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120484667635002371938496813 45181750363125889476936305)
                ·
                  refine ⟨33886312772344417107702229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45181750363125889476936305 33886312772344417107702229)
                  ·
                    refine ⟨794210455601822275961771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33886312772344417107702229 794210455601822275961771)
                    ·
                      rfl

theorem cell22_2320079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_2320079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320079 prefixEnd_2320079 := by exact prefixLift 2320079
  have htrace : WordTrace (prefixWord ++ tailWord_2320079) baseStart_2320079 baseEnd_2320079 := by
    simpa [prefixWord, tailWord_2320079, baseEnd_2320079] using wordTrace_append hprefix tailTrace_2320079
  have hstable : (prefixWord ++ tailWord_2320079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320079).length < 2 ^ (prefixWord ++ tailWord_2320079).sum := by decide
  have hdescent : baseEnd_2320079 < baseStart_2320079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320130 : List Nat := [3, 4, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_2320130 : Nat := 118140960795 + 2320130 * 2 ^ 59
def prefixEnd_2320130 : Nat := 4983230072969 + 3 ^ 40 * 2320130 * 2
def baseEnd_2320130 : Nat := 794227913944075142936615

theorem tailTrace_2320130 : CollatzResearch.WordTrace tailWord_2320130 prefixEnd_2320130 794227913944075142936615 := by
  unfold tailWord_2320130
  simp only [CollatzResearch.WordTrace]
  refine ⟨21155523271143182875575461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56414728723048487668201229 21155523271143182875575461)
  ·
    refine ⟨3966660613339346789170399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21155523271143182875575461 3966660613339346789170399)
    ·
      refine ⟨5949990920009020183755599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3966660613339346789170399 5949990920009020183755599)
      ·
        refine ⟨8924986380013530275633399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5949990920009020183755599 8924986380013530275633399)
        ·
          refine ⟨13387479570020295413450099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8924986380013530275633399 13387479570020295413450099)
          ·
            refine ⟨20081219355030443120175149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13387479570020295413450099 20081219355030443120175149)
            ·
              refine ⟨7530457258136416170065681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20081219355030443120175149 7530457258136416170065681)
              ·
                refine ⟨5647842943602312127549261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7530457258136416170065681 5647842943602312127549261)
                ·
                  refine ⟨2117941103850867047830973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5647842943602312127549261 2117941103850867047830973)
                  ·
                    refine ⟨794227913944075142936615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2117941103850867047830973 794227913944075142936615)
                    ·
                      rfl

theorem cell22_2320130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_2320130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320130 prefixEnd_2320130 := by exact prefixLift 2320130
  have htrace : WordTrace (prefixWord ++ tailWord_2320130) baseStart_2320130 baseEnd_2320130 := by
    simpa [prefixWord, tailWord_2320130, baseEnd_2320130] using wordTrace_append hprefix tailTrace_2320130
  have hstable : (prefixWord ++ tailWord_2320130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320130).length < 2 ^ (prefixWord ++ tailWord_2320130).sum := by decide
  have hdescent : baseEnd_2320130 < baseStart_2320130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320190 : List Nat := [4, 2, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_2320190 : Nat := 118140960795 + 2320190 * 2 ^ 59
def prefixEnd_2320190 : Nat := 4983230072969 + 3 ^ 40 * 2320190 * 2
def baseEnd_2320190 : Nat := 794248453170254986436431

theorem tailTrace_2320190 : CollatzResearch.WordTrace tailWord_2320190 prefixEnd_2320190 794248453170254986436431 := by
  unfold tailWord_2320190
  simp only [CollatzResearch.WordTrace]
  refine ⟨10578035183044420218685753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56416187642903574499657349 10578035183044420218685753)
  ·
    refine ⟨7933526387283315164014315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10578035183044420218685753 7933526387283315164014315)
    ·
      refine ⟨11900289580924972746021473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7933526387283315164014315 11900289580924972746021473)
      ·
        refine ⟨8925217185693729559516105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11900289580924972746021473 8925217185693729559516105)
        ·
          refine ⟨6693912889270297169637079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8925217185693729559516105 6693912889270297169637079)
          ·
            refine ⟨10040869333905445754455619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6693912889270297169637079 10040869333905445754455619)
            ·
              refine ⟨15061304000858168631683429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10040869333905445754455619 15061304000858168631683429)
              ·
                refine ⟨2823994500160906618440643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15061304000858168631683429 2823994500160906618440643)
                ·
                  refine ⟨4235991750241359927660965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2823994500160906618440643 4235991750241359927660965)
                  ·
                    refine ⟨794248453170254986436431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4235991750241359927660965 794248453170254986436431)
                    ·
                      rfl

theorem cell22_2320190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_2320190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320190 prefixEnd_2320190 := by exact prefixLift 2320190
  have htrace : WordTrace (prefixWord ++ tailWord_2320190) baseStart_2320190 baseEnd_2320190 := by
    simpa [prefixWord, tailWord_2320190, baseEnd_2320190] using wordTrace_append hprefix tailTrace_2320190
  have hstable : (prefixWord ++ tailWord_2320190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320190).length < 2 ^ (prefixWord ++ tailWord_2320190).sum := by decide
  have hdescent : baseEnd_2320190 < baseStart_2320190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320201 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 1, 6]
def baseStart_2320201 : Nat := 118140960795 + 2320201 * 2 ^ 59
def prefixEnd_2320201 : Nat := 4983230072969 + 3 ^ 40 * 2320201 * 2
def baseEnd_2320201 : Nat := 794252218695054624411397

theorem tailTrace_2320201 : CollatzResearch.WordTrace tailWord_2320201 prefixEnd_2320201 794252218695054624411397 := by
  unfold tailWord_2320201
  simp only [CollatzResearch.WordTrace]
  refine ⟨84624682667315510628136457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56416455111543673752090971 84624682667315510628136457)
  ·
    refine ⟨63468512000486632971102343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84624682667315510628136457 63468512000486632971102343)
    ·
      refine ⟨95202768000729949456653515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63468512000486632971102343 95202768000729949456653515)
      ·
        refine ⟨142804152001094924184980273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95202768000729949456653515 142804152001094924184980273)
        ·
          refine ⟨107103114000821193138735205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142804152001094924184980273 107103114000821193138735205)
          ·
            refine ⟨20081833875153973713512851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107103114000821193138735205 20081833875153973713512851)
            ·
              refine ⟨30122750812730960570269277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20081833875153973713512851 30122750812730960570269277)
              ·
                refine ⟨11296031554774110213850979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30122750812730960570269277 11296031554774110213850979)
                ·
                  refine ⟨16944047332161165320776469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11296031554774110213850979 16944047332161165320776469)
                  ·
                    refine ⟨794252218695054624411397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16944047332161165320776469 794252218695054624411397)
                    ·
                      rfl

theorem cell22_2320201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_2320201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320201 prefixEnd_2320201 := by exact prefixLift 2320201
  have htrace : WordTrace (prefixWord ++ tailWord_2320201) baseStart_2320201 baseEnd_2320201 := by
    simpa [prefixWord, tailWord_2320201, baseEnd_2320201] using wordTrace_append hprefix tailTrace_2320201
  have hstable : (prefixWord ++ tailWord_2320201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320201).length < 2 ^ (prefixWord ++ tailWord_2320201).sum := by decide
  have hdescent : baseEnd_2320201 < baseStart_2320201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320218 : List Nat := [3, 1, 1, 2, 1, 3, 3, 2, 2, 4]
def baseStart_2320218 : Nat := 118140960795 + 2320218 * 2 ^ 59
def prefixEnd_2320218 : Nat := 4983230072969 + 3 ^ 40 * 2320218 * 2
def baseEnd_2320218 : Nat := 794258038142472246736345

theorem tailTrace_2320218 : CollatzResearch.WordTrace tailWord_2320218 prefixEnd_2320218 794258038142472246736345 := by
  unfold tailWord_2320218
  simp only [CollatzResearch.WordTrace]
  refine ⟨21156325677063480632876327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56416868472169281687670205 21156325677063480632876327)
  ·
    refine ⟨31734488515595220949314491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21156325677063480632876327 31734488515595220949314491)
    ·
      refine ⟨47601732773392831423971737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31734488515595220949314491 47601732773392831423971737)
      ·
        refine ⟨35701299580044623567978803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47601732773392831423971737 35701299580044623567978803)
        ·
          refine ⟨53551949370066935351968205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35701299580044623567978803 53551949370066935351968205)
          ·
            refine ⟨20081981013775100756988077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53551949370066935351968205 20081981013775100756988077)
            ·
              refine ⟨7530742880165662783870529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20081981013775100756988077 7530742880165662783870529)
              ·
                refine ⟨5648057160124247087902897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7530742880165662783870529 5648057160124247087902897)
                ·
                  refine ⟨4236042870093185315927173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5648057160124247087902897 4236042870093185315927173)
                  ·
                    refine ⟨794258038142472246736345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4236042870093185315927173 794258038142472246736345)
                    ·
                      rfl

theorem cell22_2320218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_2320218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320218 prefixEnd_2320218 := by exact prefixLift 2320218
  have htrace : WordTrace (prefixWord ++ tailWord_2320218) baseStart_2320218 baseEnd_2320218 := by
    simpa [prefixWord, tailWord_2320218, baseEnd_2320218] using wordTrace_append hprefix tailTrace_2320218
  have hstable : (prefixWord ++ tailWord_2320218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320218).length < 2 ^ (prefixWord ++ tailWord_2320218).sum := by decide
  have hdescent : baseEnd_2320218 < baseStart_2320218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320237 : List Nat := [1, 5, 1, 1, 1, 1, 6, 1, 2, 3]
def baseStart_2320237 : Nat := 118140960795 + 2320237 * 2 ^ 59
def prefixEnd_2320237 : Nat := 4983230072969 + 3 ^ 40 * 2320237 * 2
def baseEnd_2320237 : Nat := 794264542230762530511287

theorem tailTrace_2320237 : CollatzResearch.WordTrace tailWord_2320237 prefixEnd_2320237 794264542230762530511287 := by
  unfold tailWord_2320237
  simp only [CollatzResearch.WordTrace]
  refine ⟨84625995695185088776446965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56417330463456725850964643 84625995695185088776446965)
  ·
    refine ⟨7933687096423602072791903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84625995695185088776446965 7933687096423602072791903)
    ·
      refine ⟨11900530644635403109187855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7933687096423602072791903 11900530644635403109187855)
      ·
        refine ⟨17850795966953104663781783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11900530644635403109187855 17850795966953104663781783)
        ·
          refine ⟨26776193950429656995672675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17850795966953104663781783 26776193950429656995672675)
          ·
            refine ⟨40164290925644485493509013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26776193950429656995672675 40164290925644485493509013)
            ·
              refine ⟨1882701137139585257508235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40164290925644485493509013 1882701137139585257508235)
              ·
                refine ⟨2824051705709377886262353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1882701137139585257508235 2824051705709377886262353)
                ·
                  refine ⟨2118038779282033414696765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2824051705709377886262353 2118038779282033414696765)
                  ·
                    refine ⟨794264542230762530511287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2118038779282033414696765 794264542230762530511287)
                    ·
                      rfl

theorem cell22_2320237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_2320237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320237 prefixEnd_2320237 := by exact prefixLift 2320237
  have htrace : WordTrace (prefixWord ++ tailWord_2320237) baseStart_2320237 baseEnd_2320237 := by
    simpa [prefixWord, tailWord_2320237, baseEnd_2320237] using wordTrace_append hprefix tailTrace_2320237
  have hstable : (prefixWord ++ tailWord_2320237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320237).length < 2 ^ (prefixWord ++ tailWord_2320237).sum := by decide
  have hdescent : baseEnd_2320237 < baseStart_2320237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320295 : List Nat := [1, 1, 6, 1, 2, 1, 2, 3, 5]
def baseStart_2320295 : Nat := 118140960795 + 2320295 * 2 ^ 59
def prefixEnd_2320295 : Nat := 4983230072969 + 3 ^ 40 * 2320295 * 2
def baseEnd_2320295 : Nat := 264761465605356570853703

theorem tailTrace_2320295 : CollatzResearch.WordTrace tailWord_2320295 prefixEnd_2320295 264761465605356570853703 := by
  unfold tailWord_2320295
  simp only [CollatzResearch.WordTrace]
  refine ⟨84628111128974964682058339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56418740752649976454705559 84628111128974964682058339)
  ·
    refine ⟨126942166693462447023087509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84628111128974964682058339 126942166693462447023087509)
    ·
      refine ⟨5950414063756052204207227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 126942166693462447023087509 5950414063756052204207227)
      ·
        refine ⟨8925621095634078306310841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5950414063756052204207227 8925621095634078306310841)
        ·
          refine ⟨6694215821725558729733131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8925621095634078306310841 6694215821725558729733131)
          ·
            refine ⟨10041323732588338094599697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6694215821725558729733131 10041323732588338094599697)
            ·
              refine ⟨7530992799441253570949773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10041323732588338094599697 7530992799441253570949773)
              ·
                refine ⟨2824122299790470089106165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7530992799441253570949773 2824122299790470089106165)
                ·
                  refine ⟨264761465605356570853703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2824122299790470089106165 264761465605356570853703)
                  ·
                    rfl

theorem cell22_2320295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 5].length) (baseStart_2320295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320295 prefixEnd_2320295 := by exact prefixLift 2320295
  have htrace : WordTrace (prefixWord ++ tailWord_2320295) baseStart_2320295 baseEnd_2320295 := by
    simpa [prefixWord, tailWord_2320295, baseEnd_2320295] using wordTrace_append hprefix tailTrace_2320295
  have hstable : (prefixWord ++ tailWord_2320295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320295).length < 2 ^ (prefixWord ++ tailWord_2320295).sum := by decide
  have hdescent : baseEnd_2320295 < baseStart_2320295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320316 : List Nat := [2, 2, 2, 5, 1, 1, 2, 3, 1, 3]
def baseStart_2320316 : Nat := 118140960795 + 2320316 * 2 ^ 59
def prefixEnd_2320316 : Nat := 4983230072969 + 3 ^ 40 * 2320316 * 2
def baseEnd_2320316 : Nat := 794291585545232657786045

theorem tailTrace_2320316 : CollatzResearch.WordTrace tailWord_2320316 prefixEnd_2320316 794291585545232657786045 := by
  unfold tailWord_2320316
  simp only [CollatzResearch.WordTrace]
  refine ⟨42314438530949442634286401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56419251374599256845715201 42314438530949442634286401)
  ·
    refine ⟨31735828898212081975714801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42314438530949442634286401 31735828898212081975714801)
    ·
      refine ⟨23801871673659061481786101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31735828898212081975714801 23801871673659061481786101)
      ·
        refine ⟨2231425469405537013917447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23801871673659061481786101 2231425469405537013917447)
        ·
          refine ⟨3347138204108305520876171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2231425469405537013917447 3347138204108305520876171)
          ·
            refine ⟨5020707306162458281314257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3347138204108305520876171 5020707306162458281314257)
            ·
              refine ⟨3765530479621843710985693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5020707306162458281314257 3765530479621843710985693)
              ·
                refine ⟨1412073929858191391619635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3765530479621843710985693 1412073929858191391619635)
                ·
                  refine ⟨2118110894787287087429453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1412073929858191391619635 2118110894787287087429453)
                  ·
                    refine ⟨794291585545232657786045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2118110894787287087429453 794291585545232657786045)
                    ·
                      rfl

theorem cell22_2320316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_2320316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320316 prefixEnd_2320316 := by exact prefixLift 2320316
  have htrace : WordTrace (prefixWord ++ tailWord_2320316) baseStart_2320316 baseEnd_2320316 := by
    simpa [prefixWord, tailWord_2320316, baseEnd_2320316] using wordTrace_append hprefix tailTrace_2320316
  have hstable : (prefixWord ++ tailWord_2320316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320316).length < 2 ^ (prefixWord ++ tailWord_2320316).sum := by decide
  have hdescent : baseEnd_2320316 < baseStart_2320316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320340 : List Nat := [2, 4, 1, 2, 1, 1, 4, 1, 6]
def baseStart_2320340 : Nat := 118140960795 + 2320340 * 2 ^ 59
def prefixEnd_2320340 : Nat := 4983230072969 + 3 ^ 40 * 2320340 * 2
def baseEnd_2320340 : Nat := 264766600411901531728657

theorem tailTrace_2320340 : CollatzResearch.WordTrace tailWord_2320340 prefixEnd_2320340 264766600411901531728657 := by
  unfold tailWord_2320340
  simp only [CollatzResearch.WordTrace]
  refine ⟨42314876206905968683723237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56419834942541291578297649 42314876206905968683723237)
  ·
    refine ⟨7934039288794869128198107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42314876206905968683723237 7934039288794869128198107)
    ·
      refine ⟨11901058933192303692297161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7934039288794869128198107 11901058933192303692297161)
      ·
        refine ⟨8925794199894227769222871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11901058933192303692297161 8925794199894227769222871)
        ·
          refine ⟨13388691299841341653834307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8925794199894227769222871 13388691299841341653834307)
          ·
            refine ⟨20083036949762012480751461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13388691299841341653834307 20083036949762012480751461)
            ·
              refine ⟨3765569428080377340140899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20083036949762012480751461 3765569428080377340140899)
              ·
                refine ⟨5648354142120566010211349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3765569428080377340140899 5648354142120566010211349)
                ·
                  refine ⟨264766600411901531728657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5648354142120566010211349 264766600411901531728657)
                  ·
                    rfl

theorem cell22_2320340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_2320340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320340 prefixEnd_2320340 := by exact prefixLift 2320340
  have htrace : WordTrace (prefixWord ++ tailWord_2320340) baseStart_2320340 baseEnd_2320340 := by
    simpa [prefixWord, tailWord_2320340, baseEnd_2320340] using wordTrace_append hprefix tailTrace_2320340
  have hstable : (prefixWord ++ tailWord_2320340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320340).length < 2 ^ (prefixWord ++ tailWord_2320340).sum := by decide
  have hdescent : baseEnd_2320340 < baseStart_2320340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320353 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 1, 6]
def baseStart_2320353 : Nat := 118140960795 + 2320353 * 2 ^ 59
def prefixEnd_2320353 : Nat := 4983230072969 + 3 ^ 40 * 2320353 * 2
def baseEnd_2320353 : Nat := 794304251401376894610931

theorem tailTrace_2320353 : CollatzResearch.WordTrace tailWord_2320353 prefixEnd_2320353 794304251401376894610931 := by
  unfold tailWord_2320353
  simp only [CollatzResearch.WordTrace]
  refine ⟨84630226562764840587669713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56420151041843227058446475 84630226562764840587669713)
  ·
    refine ⟨63472669922073630440752285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84630226562764840587669713 63472669922073630440752285)
    ·
      refine ⟨23802251220777611415282107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63472669922073630440752285 23802251220777611415282107)
      ·
        refine ⟨35703376831166417122923161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23802251220777611415282107 35703376831166417122923161)
        ·
          refine ⟨26777532623374812842192371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35703376831166417122923161 26777532623374812842192371)
          ·
            refine ⟨40166298935062219263288557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26777532623374812842192371 40166298935062219263288557)
            ·
              refine ⟨15062362100648332223733209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40166298935062219263288557 15062362100648332223733209)
              ·
                refine ⟨11296771575486249167799907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15062362100648332223733209 11296771575486249167799907)
                ·
                  refine ⟨16945157363229373751699861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11296771575486249167799907 16945157363229373751699861)
                  ·
                    refine ⟨794304251401376894610931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16945157363229373751699861 794304251401376894610931)
                    ·
                      rfl

theorem cell22_2320353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_2320353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320353 prefixEnd_2320353 := by exact prefixLift 2320353
  have htrace : WordTrace (prefixWord ++ tailWord_2320353) baseStart_2320353 baseEnd_2320353 := by
    simpa [prefixWord, tailWord_2320353, baseEnd_2320353] using wordTrace_append hprefix tailTrace_2320353
  have hstable : (prefixWord ++ tailWord_2320353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320353).length < 2 ^ (prefixWord ++ tailWord_2320353).sum := by decide
  have hdescent : baseEnd_2320353 < baseStart_2320353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320355 : List Nat := [1, 1, 1, 6, 1, 2, 3, 1, 1, 5]
def baseStart_2320355 : Nat := 118140960795 + 2320355 * 2 ^ 59
def prefixEnd_2320355 : Nat := 4983230072969 + 3 ^ 40 * 2320355 * 2
def baseEnd_2320355 : Nat := 794304936042249556060925

theorem tailTrace_2320355 : CollatzResearch.WordTrace tailWord_2320355 prefixEnd_2320355 794304936042249556060925 := by
  unfold tailWord_2320355
  simp only [CollatzResearch.WordTrace]
  refine ⟨84630299508757594929242519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56420199672505063286161679 84630299508757594929242519)
  ·
    refine ⟨126945449263136392393863779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84630299508757594929242519 126945449263136392393863779)
    ·
      refine ⟨190418173894704588590795669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126945449263136392393863779 190418173894704588590795669)
      ·
        refine ⟨8925851901314277590193547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 190418173894704588590795669 8925851901314277590193547)
        ·
          refine ⟨13388777851971416385290321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8925851901314277590193547 13388777851971416385290321)
          ·
            refine ⟨10041583388978562288967741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13388777851971416385290321 10041583388978562288967741)
            ·
              refine ⟨3765593770866960858362903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10041583388978562288967741 3765593770866960858362903)
              ·
                refine ⟨5648390656300441287544355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3765593770866960858362903 5648390656300441287544355)
                ·
                  refine ⟨8472585984450661931316533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5648390656300441287544355 8472585984450661931316533)
                  ·
                    refine ⟨794304936042249556060925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8472585984450661931316533 794304936042249556060925)
                    ·
                      rfl

theorem cell22_2320355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 5].length) (baseStart_2320355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320355 prefixEnd_2320355 := by exact prefixLift 2320355
  have htrace : WordTrace (prefixWord ++ tailWord_2320355) baseStart_2320355 baseEnd_2320355 := by
    simpa [prefixWord, tailWord_2320355, baseEnd_2320355] using wordTrace_append hprefix tailTrace_2320355
  have hstable : (prefixWord ++ tailWord_2320355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320355).length < 2 ^ (prefixWord ++ tailWord_2320355).sum := by decide
  have hdescent : baseEnd_2320355 < baseStart_2320355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320428 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 3, 7]
def baseStart_2320428 : Nat := 118140960795 + 2320428 * 2 ^ 59
def prefixEnd_2320428 : Nat := 4983230072969 + 3 ^ 40 * 2320428 * 2
def baseEnd_2320428 : Nat := 794329925434101698985701

theorem tailTrace_2320428 : CollatzResearch.WordTrace tailWord_2320428 prefixEnd_2320428 794329925434101698985701 := by
  unfold tailWord_2320428
  simp only [CollatzResearch.WordTrace]
  refine ⟨42316481018746564198324969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56421974691662085597766625 42316481018746564198324969)
  ·
    refine ⟨31737360764059923148743727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42316481018746564198324969 31737360764059923148743727)
    ·
      refine ⟨47606041146089884723115591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31737360764059923148743727 47606041146089884723115591)
      ·
        refine ⟨71409061719134827084673387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47606041146089884723115591 71409061719134827084673387)
        ·
          refine ⟨107113592578702240627010081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71409061719134827084673387 107113592578702240627010081)
          ·
            refine ⟨80335194434026680470257561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107113592578702240627010081 80335194434026680470257561)
            ·
              refine ⟨60251395825520010352693171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80335194434026680470257561 60251395825520010352693171)
              ·
                refine ⟨90377093738280015529039757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60251395825520010352693171 90377093738280015529039757)
                ·
                  refine ⟨33891410151855005823389909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90377093738280015529039757 33891410151855005823389909)
                  ·
                    refine ⟨794329925434101698985701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33891410151855005823389909 794329925434101698985701)
                    ·
                      rfl

theorem cell22_2320428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_2320428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320428 prefixEnd_2320428 := by exact prefixLift 2320428
  have htrace : WordTrace (prefixWord ++ tailWord_2320428) baseStart_2320428 baseEnd_2320428 := by
    simpa [prefixWord, tailWord_2320428, baseEnd_2320428] using wordTrace_append hprefix tailTrace_2320428
  have hstable : (prefixWord ++ tailWord_2320428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320428).length < 2 ^ (prefixWord ++ tailWord_2320428).sum := by decide
  have hdescent : baseEnd_2320428 < baseStart_2320428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320445 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_2320445 : Nat := 118140960795 + 2320445 * 2 ^ 59
def prefixEnd_2320445 : Nat := 4983230072969 + 3 ^ 40 * 2320445 * 2
def baseEnd_2320445 : Nat := 794335744881519321310649

theorem tailTrace_2320445 : CollatzResearch.WordTrace tailWord_2320445 prefixEnd_2320445 794335744881519321310649 := by
  unfold tailWord_2320445
  simp only [CollatzResearch.WordTrace]
  refine ⟨84633582078431540300018789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56422388052287693533345859 84633582078431540300018789)
  ·
    refine ⟨15868796639705913806253523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84633582078431540300018789 15868796639705913806253523)
    ·
      refine ⟨23803194959558870709380285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15868796639705913806253523 23803194959558870709380285)
      ·
        refine ⟨8926198109834576516017607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23803194959558870709380285 8926198109834576516017607)
        ·
          refine ⟨13389297164751864774026411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8926198109834576516017607 13389297164751864774026411)
          ·
            refine ⟨20083945747127797161039617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13389297164751864774026411 20083945747127797161039617)
            ·
              refine ⟨15062959310345847870779713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20083945747127797161039617 15062959310345847870779713)
              ·
                refine ⟨11297219482759385903084785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15062959310345847870779713 11297219482759385903084785)
                ·
                  refine ⟨8472914612069539427313589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11297219482759385903084785 8472914612069539427313589)
                  ·
                    refine ⟨794335744881519321310649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8472914612069539427313589 794335744881519321310649)
                    ·
                      rfl

theorem cell22_2320445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_2320445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320445 prefixEnd_2320445 := by exact prefixLift 2320445
  have htrace : WordTrace (prefixWord ++ tailWord_2320445) baseStart_2320445 baseEnd_2320445 := by
    simpa [prefixWord, tailWord_2320445, baseEnd_2320445] using wordTrace_append hprefix tailTrace_2320445
  have hstable : (prefixWord ++ tailWord_2320445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320445).length < 2 ^ (prefixWord ++ tailWord_2320445).sum := by decide
  have hdescent : baseEnd_2320445 < baseStart_2320445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320460 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 3, 4]
def baseStart_2320460 : Nat := 118140960795 + 2320460 * 2 ^ 59
def prefixEnd_2320460 : Nat := 4983230072969 + 3 ^ 40 * 2320460 * 2
def baseEnd_2320460 : Nat := 794340879688064282185603

theorem tailTrace_2320460 : CollatzResearch.WordTrace tailWord_2320460 prefixEnd_2320460 794340879688064282185603 := by
  unfold tailWord_2320460
  simp only [CollatzResearch.WordTrace]
  refine ⟨42317064586688598930907417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56422752782251465241209889 42317064586688598930907417)
  ·
    refine ⟨31737798440016449198180563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42317064586688598930907417 31737798440016449198180563)
    ·
      refine ⟨47606697660024673797270845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31737798440016449198180563 47606697660024673797270845)
      ·
        refine ⟨17852511622509252673976567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47606697660024673797270845 17852511622509252673976567)
        ·
          refine ⟨26778767433763879010964851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17852511622509252673976567 26778767433763879010964851)
          ·
            refine ⟨40168151150645818516447277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26778767433763879010964851 40168151150645818516447277)
            ·
              refine ⟨15063056681492181943667729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40168151150645818516447277 15063056681492181943667729)
              ·
                refine ⟨11297292511119136457750797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15063056681492181943667729 11297292511119136457750797)
                ·
                  refine ⟨4236484691669676171656549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11297292511119136457750797 4236484691669676171656549)
                  ·
                    refine ⟨794340879688064282185603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4236484691669676171656549 794340879688064282185603)
                    ·
                      rfl

theorem cell22_2320460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_2320460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320460 prefixEnd_2320460 := by exact prefixLift 2320460
  have htrace : WordTrace (prefixWord ++ tailWord_2320460) baseStart_2320460 baseEnd_2320460 := by
    simpa [prefixWord, tailWord_2320460, baseEnd_2320460] using wordTrace_append hprefix tailTrace_2320460
  have hstable : (prefixWord ++ tailWord_2320460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320460).length < 2 ^ (prefixWord ++ tailWord_2320460).sum := by decide
  have hdescent : baseEnd_2320460 < baseStart_2320460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320492 : List Nat := [2, 2, 1, 1, 3, 3, 1, 5, 4]
def baseStart_2320492 : Nat := 118140960795 + 2320492 * 2 ^ 59
def prefixEnd_2320492 : Nat := 4983230072969 + 3 ^ 40 * 2320492 * 2
def baseEnd_2320492 : Nat := 264783944647342288461835

theorem tailTrace_2320492 : CollatzResearch.WordTrace tailWord_2320492 prefixEnd_2320492 264783944647342288461835 := by
  unfold tailWord_2320492
  simp only [CollatzResearch.WordTrace]
  refine ⟨42317648154630633663489865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56423530872840844884653153 42317648154630633663489865)
  ·
    refine ⟨31738236115972975247617399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42317648154630633663489865 31738236115972975247617399)
    ·
      refine ⟨47607354173959462871426099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31738236115972975247617399 47607354173959462871426099)
      ·
        refine ⟨71411031260939194307139149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47607354173959462871426099 71411031260939194307139149)
        ·
          refine ⟨26779136722852197865177181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71411031260939194307139149 26779136722852197865177181)
          ·
            refine ⟨10042176271069574199441443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26779136722852197865177181 10042176271069574199441443)
            ·
              refine ⟨15063264406604361299162165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10042176271069574199441443 15063264406604361299162165)
              ·
                refine ⟨1412181038119158871796453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15063264406604361299162165 1412181038119158871796453)
                ·
                  refine ⟨264783944647342288461835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1412181038119158871796453 264783944647342288461835)
                  ·
                    rfl

theorem cell22_2320492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 4].length) (baseStart_2320492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320492 prefixEnd_2320492 := by exact prefixLift 2320492
  have htrace : WordTrace (prefixWord ++ tailWord_2320492) baseStart_2320492 baseEnd_2320492 := by
    simpa [prefixWord, tailWord_2320492, baseEnd_2320492] using wordTrace_append hprefix tailTrace_2320492
  have hstable : (prefixWord ++ tailWord_2320492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320492).length < 2 ^ (prefixWord ++ tailWord_2320492).sum := by decide
  have hdescent : baseEnd_2320492 < baseStart_2320492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320554 : List Nat := [3, 1, 5, 1, 2, 2, 8]
def baseStart_2320554 : Nat := 118140960795 + 2320554 * 2 ^ 59
def prefixEnd_2320554 : Nat := 4983230072969 + 3 ^ 40 * 2320554 * 2
def baseEnd_2320554 : Nat := 29421224363299235938345

theorem tailTrace_2320554 : CollatzResearch.WordTrace tailWord_2320554 prefixEnd_2320554 29421224363299235938345 := by
  unfold tailWord_2320554
  simp only [CollatzResearch.WordTrace]
  refine ⟨21159389408759162978934179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56425038423357767943824477 21159389408759162978934179)
  ·
    refine ⟨31739084113138744468401269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21159389408759162978934179 31739084113138744468401269)
    ·
      refine ⟨2975539135606757293912619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31739084113138744468401269 2975539135606757293912619)
      ·
        refine ⟨4463308703410135940868929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2975539135606757293912619 4463308703410135940868929)
        ·
          refine ⟨3347481527557601955651697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4463308703410135940868929 3347481527557601955651697)
          ·
            refine ⟨2510611145668201466738773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3347481527557601955651697 2510611145668201466738773)
            ·
              refine ⟨29421224363299235938345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2510611145668201466738773 29421224363299235938345)
              ·
                rfl

theorem cell22_2320554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 8].length) (baseStart_2320554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320554 prefixEnd_2320554 := by exact prefixLift 2320554
  have htrace : WordTrace (prefixWord ++ tailWord_2320554) baseStart_2320554 baseEnd_2320554 := by
    simpa [prefixWord, tailWord_2320554, baseEnd_2320554] using wordTrace_append hprefix tailTrace_2320554
  have hstable : (prefixWord ++ tailWord_2320554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320554).length < 2 ^ (prefixWord ++ tailWord_2320554).sum := by decide
  have hdescent : baseEnd_2320554 < baseStart_2320554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320644 : List Nat := [2, 3, 2, 2, 3, 1, 1, 2, 6]
def baseStart_2320644 : Nat := 118140960795 + 2320644 * 2 ^ 59
def prefixEnd_2320644 : Nat := 4983230072969 + 3 ^ 40 * 2320644 * 2
def baseEnd_2320644 : Nat := 264801288882783045195013

theorem tailTrace_2320644 : CollatzResearch.WordTrace tailWord_2320644 prefixEnd_2320644 264801288882783045195013 := by
  unfold tailWord_2320644
  simp only [CollatzResearch.WordTrace]
  refine ⟨42320420102355298643256493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56427226803140398191008657 42320420102355298643256493)
  ·
    refine ⟨15870157538383236991221185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42320420102355298643256493 15870157538383236991221185)
    ·
      refine ⟨11902618153787427743415889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15870157538383236991221185 11902618153787427743415889)
      ·
        refine ⟨8926963615340570807561917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11902618153787427743415889 8926963615340570807561917)
        ·
          refine ⟨3347611355752714052835719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8926963615340570807561917 3347611355752714052835719)
          ·
            refine ⟨5021417033629071079253579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3347611355752714052835719 5021417033629071079253579)
            ·
              refine ⟨7532125550443606618880369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5021417033629071079253579 7532125550443606618880369)
              ·
                refine ⟨5649094162832704964160277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7532125550443606618880369 5649094162832704964160277)
                ·
                  refine ⟨264801288882783045195013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5649094162832704964160277 264801288882783045195013)
                  ·
                    rfl

theorem cell22_2320644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_2320644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320644 prefixEnd_2320644 := by exact prefixLift 2320644
  have htrace : WordTrace (prefixWord ++ tailWord_2320644) baseStart_2320644 baseEnd_2320644 := by
    simpa [prefixWord, tailWord_2320644, baseEnd_2320644] using wordTrace_append hprefix tailTrace_2320644
  have hstable : (prefixWord ++ tailWord_2320644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320644).length < 2 ^ (prefixWord ++ tailWord_2320644).sum := by decide
  have hdescent : baseEnd_2320644 < baseStart_2320644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320655 : List Nat := [1, 1, 2, 1, 1, 1, 3, 12]
def baseStart_2320655 : Nat := 118140960795 + 2320655 * 2 ^ 59
def prefixEnd_2320655 : Nat := 4983230072969 + 3 ^ 40 * 2320655 * 2
def baseEnd_2320655 : Nat := 88267514685905419284445

theorem tailTrace_2320655 : CollatzResearch.WordTrace tailWord_2320655 prefixEnd_2320655 88267514685905419284445 := by
  unfold tailWord_2320655
  simp only [CollatzResearch.WordTrace]
  refine ⟨84641241407670746165163419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56427494271780497443442279 84641241407670746165163419)
  ·
    refine ⟨126961862111506119247745129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84641241407670746165163419 126961862111506119247745129)
    ·
      refine ⟨95221396583629589435808847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126961862111506119247745129 95221396583629589435808847)
      ·
        refine ⟨142832094875444384153713271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95221396583629589435808847 142832094875444384153713271)
        ·
          refine ⟨214248142313166576230569907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142832094875444384153713271 214248142313166576230569907)
          ·
            refine ⟨321372213469749864345854861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214248142313166576230569907 321372213469749864345854861)
            ·
              refine ⟨120514580051156199129695573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 321372213469749864345854861 120514580051156199129695573)
              ·
                refine ⟨88267514685905419284445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 120514580051156199129695573 88267514685905419284445)
                ·
                  rfl

theorem cell22_2320655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 12].length) (baseStart_2320655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320655 prefixEnd_2320655 := by exact prefixLift 2320655
  have htrace : WordTrace (prefixWord ++ tailWord_2320655) baseStart_2320655 baseEnd_2320655 := by
    simpa [prefixWord, tailWord_2320655, baseEnd_2320655] using wordTrace_append hprefix tailTrace_2320655
  have hstable : (prefixWord ++ tailWord_2320655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320655).length < 2 ^ (prefixWord ++ tailWord_2320655).sum := by decide
  have hdescent : baseEnd_2320655 < baseStart_2320655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320657 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 1, 6]
def baseStart_2320657 : Nat := 118140960795 + 2320657 * 2 ^ 59
def prefixEnd_2320657 : Nat := 4983230072969 + 3 ^ 40 * 2320657 * 2
def baseEnd_2320657 : Nat := 794408316814021435009999

theorem tailTrace_2320657 : CollatzResearch.WordTrace tailWord_2320657 prefixEnd_2320657 794408316814021435009999 := by
  unfold tailWord_2320657
  simp only [CollatzResearch.WordTrace]
  refine ⟨84641314353663500506736225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56427542902442333671157483 84641314353663500506736225)
  ·
    refine ⟨63480985765247625380052169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84641314353663500506736225 63480985765247625380052169)
    ·
      refine ⟨47610739323935719035039127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63480985765247625380052169 47610739323935719035039127)
      ·
        refine ⟨71416108985903578552558691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47610739323935719035039127 71416108985903578552558691)
        ·
          refine ⟨107124163478855367828838037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71416108985903578552558691 107124163478855367828838037)
          ·
            refine ⟨5021445163071345366976783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 107124163478855367828838037 5021445163071345366976783)
            ·
              refine ⟨7532167744607018050465175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5021445163071345366976783 7532167744607018050465175)
              ·
                refine ⟨11298251616910527075697763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7532167744607018050465175 11298251616910527075697763)
                ·
                  refine ⟨16947377425365790613546645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11298251616910527075697763 16947377425365790613546645)
                  ·
                    refine ⟨794408316814021435009999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16947377425365790613546645 794408316814021435009999)
                    ·
                      rfl

theorem cell22_2320657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_2320657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320657 prefixEnd_2320657 := by exact prefixLift 2320657
  have htrace : WordTrace (prefixWord ++ tailWord_2320657) baseStart_2320657 baseEnd_2320657 := by
    simpa [prefixWord, tailWord_2320657, baseEnd_2320657] using wordTrace_append hprefix tailTrace_2320657
  have hstable : (prefixWord ++ tailWord_2320657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320657).length < 2 ^ (prefixWord ++ tailWord_2320657).sum := by decide
  have hdescent : baseEnd_2320657 < baseStart_2320657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320672 : List Nat := [2, 1, 1, 5, 2, 2, 9]
def baseStart_2320672 : Nat := 118140960795 + 2320672 * 2 ^ 59
def prefixEnd_2320672 : Nat := 4983230072969 + 3 ^ 40 * 2320672 * 2
def baseEnd_2320672 : Nat := 29422720430391347995739

theorem tailTrace_2320672 : CollatzResearch.WordTrace tailWord_2320672 prefixEnd_2320672 29422720430391347995739 := by
  unfold tailWord_2320672
  simp only [CollatzResearch.WordTrace]
  refine ⟨42320930724304579034266135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56427907632406105379021513 42320930724304579034266135)
  ·
    refine ⟨63481396086456868551399203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42320930724304579034266135 63481396086456868551399203)
    ·
      refine ⟨95222094129685302827098805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63481396086456868551399203 95222094129685302827098805)
      ·
        refine ⟨8927071324657997140040513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95222094129685302827098805 8927071324657997140040513)
        ·
          refine ⟨6695303493493497855030385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8927071324657997140040513 6695303493493497855030385)
          ·
            refine ⟨5021477620120123391272789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6695303493493497855030385 5021477620120123391272789)
            ·
              refine ⟨29422720430391347995739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5021477620120123391272789 29422720430391347995739)
              ·
                rfl

theorem cell22_2320672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 9].length) (baseStart_2320672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320672 prefixEnd_2320672 := by exact prefixLift 2320672
  have htrace : WordTrace (prefixWord ++ tailWord_2320672) baseStart_2320672 baseEnd_2320672 := by
    simpa [prefixWord, tailWord_2320672, baseEnd_2320672] using wordTrace_append hprefix tailTrace_2320672
  have hstable : (prefixWord ++ tailWord_2320672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320672).length < 2 ^ (prefixWord ++ tailWord_2320672).sum := by decide
  have hdescent : baseEnd_2320672 < baseStart_2320672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320676 : List Nat := [2, 3, 1, 3, 1, 2, 3, 2, 2, 3]
def baseStart_2320676 : Nat := 118140960795 + 2320676 * 2 ^ 59
def prefixEnd_2320676 : Nat := 4983230072969 + 3 ^ 40 * 2320676 * 2
def baseEnd_2320676 : Nat := 794414820902311718784941

theorem tailTrace_2320676 : CollatzResearch.WordTrace tailWord_2320676 prefixEnd_2320676 794414820902311718784941 := by
  unfold tailWord_2320676
  simp only [CollatzResearch.WordTrace]
  refine ⟨42321003670297333375838941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56428004893729777834451921 42321003670297333375838941)
  ·
    refine ⟨15870376376361500015939603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42321003670297333375838941 15870376376361500015939603)
    ·
      refine ⟨23805564564542250023909405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15870376376361500015939603 23805564564542250023909405)
      ·
        refine ⟨8927086711703343758966027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23805564564542250023909405 8927086711703343758966027)
        ·
          refine ⟨13390630067555015638449041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8927086711703343758966027 13390630067555015638449041)
          ·
            refine ⟨10042972550666261728836781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13390630067555015638449041 10042972550666261728836781)
            ·
              refine ⟨3766114706499848148313793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10042972550666261728836781 3766114706499848148313793)
              ·
                refine ⟨2824586029874886111235345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3766114706499848148313793 2824586029874886111235345)
                ·
                  refine ⟨2118439522406164583426509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2824586029874886111235345 2118439522406164583426509)
                  ·
                    refine ⟨794414820902311718784941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2118439522406164583426509 794414820902311718784941)
                    ·
                      rfl

theorem cell22_2320676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_2320676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320676 prefixEnd_2320676 := by exact prefixLift 2320676
  have htrace : WordTrace (prefixWord ++ tailWord_2320676) baseStart_2320676 baseEnd_2320676 := by
    simpa [prefixWord, tailWord_2320676, baseEnd_2320676] using wordTrace_append hprefix tailTrace_2320676
  have hstable : (prefixWord ++ tailWord_2320676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320676).length < 2 ^ (prefixWord ++ tailWord_2320676).sum := by decide
  have hdescent : baseEnd_2320676 < baseStart_2320676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320738 : List Nat := [3, 3, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_2320738 : Nat := 118140960795 + 2320738 * 2 ^ 59
def prefixEnd_2320738 : Nat := 4983230072969 + 3 ^ 40 * 2320738 * 2
def baseEnd_2320738 : Nat := 794436044769364223734751

theorem tailTrace_2320738 : CollatzResearch.WordTrace tailWord_2320738 prefixEnd_2320738 794436044769364223734751 := by
  unfold tailWord_2320738
  simp only [CollatzResearch.WordTrace]
  refine ⟨21161067166592512835108717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56429512444246700893623245 21161067166592512835108717)
  ·
    refine ⟨7935400187472192313165769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21161067166592512835108717 7935400187472192313165769)
    ·
      refine ⟨5951550140604144234874327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7935400187472192313165769 5951550140604144234874327)
      ·
        refine ⟨8927325210906216352311491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5951550140604144234874327 8927325210906216352311491)
        ·
          refine ⟨13390987816359324528467237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8927325210906216352311491 13390987816359324528467237)
          ·
            refine ⟨2510810215567373349087607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13390987816359324528467237 2510810215567373349087607)
            ·
              refine ⟨3766215323351060023631411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2510810215567373349087607 3766215323351060023631411)
              ·
                refine ⟨5649322985026590035447117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3766215323351060023631411 5649322985026590035447117)
                ·
                  refine ⟨2118496119384971263292669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5649322985026590035447117 2118496119384971263292669)
                  ·
                    refine ⟨794436044769364223734751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2118496119384971263292669 794436044769364223734751)
                    ·
                      rfl

theorem cell22_2320738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_2320738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320738 prefixEnd_2320738 := by exact prefixLift 2320738
  have htrace : WordTrace (prefixWord ++ tailWord_2320738) baseStart_2320738 baseEnd_2320738 := by
    simpa [prefixWord, tailWord_2320738, baseEnd_2320738] using wordTrace_append hprefix tailTrace_2320738
  have hstable : (prefixWord ++ tailWord_2320738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320738).length < 2 ^ (prefixWord ++ tailWord_2320738).sum := by decide
  have hdescent : baseEnd_2320738 < baseStart_2320738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320747 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 5, 4]
def baseStart_2320747 : Nat := 118140960795 + 2320747 * 2 ^ 59
def prefixEnd_2320747 : Nat := 4983230072969 + 3 ^ 40 * 2320747 * 2
def baseEnd_2320747 : Nat := 794439125653291200259723

theorem tailTrace_2320747 : CollatzResearch.WordTrace tailWord_2320747 prefixEnd_2320747 794439125653291200259723 := by
  unfold tailWord_2320747
  simp only [CollatzResearch.WordTrace]
  refine ⟨84644596923337445877512495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56429731282224963918341663 84644596923337445877512495)
  ·
    refine ⟨126966895385006168816268743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84644596923337445877512495 126966895385006168816268743)
    ·
      refine ⟨190450343077509253224403115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126966895385006168816268743 190450343077509253224403115)
      ·
        refine ⟨285675514616263879836604673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190450343077509253224403115 285675514616263879836604673)
        ·
          refine ⟨214256635962197909877453505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285675514616263879836604673 214256635962197909877453505)
          ·
            refine ⟨160692476971648432408090129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214256635962197909877453505 160692476971648432408090129)
            ·
              refine ⟨120519357728736324306067597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160692476971648432408090129 120519357728736324306067597)
              ·
                refine ⟨45194759148276121614775349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120519357728736324306067597 45194759148276121614775349)
                ·
                  refine ⟨4237008670150886401385189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45194759148276121614775349 4237008670150886401385189)
                  ·
                    refine ⟨794439125653291200259723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4237008670150886401385189 794439125653291200259723)
                    ·
                      rfl

theorem cell22_2320747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 4].length) (baseStart_2320747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320747 prefixEnd_2320747 := by exact prefixLift 2320747
  have htrace : WordTrace (prefixWord ++ tailWord_2320747) baseStart_2320747 baseEnd_2320747 := by
    simpa [prefixWord, tailWord_2320747, baseEnd_2320747] using wordTrace_append hprefix tailTrace_2320747
  have hstable : (prefixWord ++ tailWord_2320747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320747).length < 2 ^ (prefixWord ++ tailWord_2320747).sum := by decide
  have hdescent : baseEnd_2320747 < baseStart_2320747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320764 : List Nat := [2, 2, 2, 1, 1, 1, 2, 6, 1, 4]
def baseStart_2320764 : Nat := 118140960795 + 2320764 * 2 ^ 59
def prefixEnd_2320764 : Nat := 4983230072969 + 3 ^ 40 * 2320764 * 2
def baseEnd_2320764 : Nat := 794444945100708822584671

theorem tailTrace_2320764 : CollatzResearch.WordTrace tailWord_2320764 prefixEnd_2320764 794444945100708822584671 := by
  unfold tailWord_2320764
  simp only [CollatzResearch.WordTrace]
  refine ⟨42322608482137928890440673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56430144642850571853920897 42322608482137928890440673)
  ·
    refine ⟨31741956361603446667830505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42322608482137928890440673 31741956361603446667830505)
    ·
      refine ⟨23806467271202585000872879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31741956361603446667830505 23806467271202585000872879)
      ·
        refine ⟨35709700906803877501309319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23806467271202585000872879 35709700906803877501309319)
        ·
          refine ⟨53564551360205816251963979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35709700906803877501309319 53564551360205816251963979)
          ·
            refine ⟨80346827040308724377945969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53564551360205816251963979 80346827040308724377945969)
            ·
              refine ⟨60260120280231543283459477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80346827040308724377945969 60260120280231543283459477)
              ·
                refine ⟨2824693138135853591412163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60260120280231543283459477 2824693138135853591412163)
                ·
                  refine ⟨4237039707203780387118245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2824693138135853591412163 4237039707203780387118245)
                  ·
                    refine ⟨794444945100708822584671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4237039707203780387118245 794444945100708822584671)
                    ·
                      rfl

theorem cell22_2320764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_2320764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320764 prefixEnd_2320764 := by exact prefixLift 2320764
  have htrace : WordTrace (prefixWord ++ tailWord_2320764) baseStart_2320764 baseEnd_2320764 := by
    simpa [prefixWord, tailWord_2320764, baseEnd_2320764] using wordTrace_append hprefix tailTrace_2320764
  have hstable : (prefixWord ++ tailWord_2320764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320764).length < 2 ^ (prefixWord ++ tailWord_2320764).sum := by decide
  have hdescent : baseEnd_2320764 < baseStart_2320764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320944 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 1, 6]
def baseStart_2320944 : Nat := 118140960795 + 2320944 * 2 ^ 59
def prefixEnd_2320944 : Nat := 4983230072969 + 3 ^ 40 * 2320944 * 2
def baseEnd_2320944 : Nat := 794506562779248353084119

theorem tailTrace_2320944 : CollatzResearch.WordTrace tailWord_2320944 prefixEnd_2320944 794506562779248353084119 := by
  unfold tailWord_2320944
  simp only [CollatzResearch.WordTrace]
  refine ⟨42325891051811874261216943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56434521402415832348289257 42325891051811874261216943)
  ·
    refine ⟨63488836577717811391825415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42325891051811874261216943 63488836577717811391825415)
    ·
      refine ⟨95233254866576717087738123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63488836577717811391825415 95233254866576717087738123)
      ·
        refine ⟨142849882299865075631607185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95233254866576717087738123 142849882299865075631607185)
        ·
          refine ⟨107137411724898806723705389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142849882299865075631607185 107137411724898806723705389)
          ·
            refine ⟨40176529396837052521389521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107137411724898806723705389 40176529396837052521389521)
            ·
              refine ⟨30132397047627789391042141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40176529396837052521389521 30132397047627789391042141)
              ·
                refine ⟨11299648892860421021640803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30132397047627789391042141 11299648892860421021640803)
                ·
                  refine ⟨16949473339290631532461205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11299648892860421021640803 16949473339290631532461205)
                  ·
                    refine ⟨794506562779248353084119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16949473339290631532461205 794506562779248353084119)
                    ·
                      rfl

theorem cell22_2320944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_2320944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320944 prefixEnd_2320944 := by exact prefixLift 2320944
  have htrace : WordTrace (prefixWord ++ tailWord_2320944) baseStart_2320944 baseEnd_2320944 := by
    simpa [prefixWord, tailWord_2320944, baseEnd_2320944] using wordTrace_append hprefix tailTrace_2320944
  have hstable : (prefixWord ++ tailWord_2320944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320944).length < 2 ^ (prefixWord ++ tailWord_2320944).sum := by decide
  have hdescent : baseEnd_2320944 < baseStart_2320944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320946 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 6, 3]
def baseStart_2320946 : Nat := 118140960795 + 2320946 * 2 ^ 59
def prefixEnd_2320946 : Nat := 4983230072969 + 3 ^ 40 * 2320946 * 2
def baseEnd_2320946 : Nat := 794507247420121014534113

theorem tailTrace_2320946 : CollatzResearch.WordTrace tailWord_2320946 prefixEnd_2320946 794507247420121014534113 := by
  unfold tailWord_2320946
  simp only [CollatzResearch.WordTrace]
  refine ⟨21162963762404125716001673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56434570033077668576004461 21162963762404125716001673)
  ·
    refine ⟨15872222821803094287001255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21162963762404125716001673 15872222821803094287001255)
    ·
      refine ⟨23808334232704641430501883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15872222821803094287001255 23808334232704641430501883)
      ·
        refine ⟨35712501349056962145752825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23808334232704641430501883 35712501349056962145752825)
        ·
          refine ⟨26784376011792721609314619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35712501349056962145752825 26784376011792721609314619)
          ·
            refine ⟨40176564017689082413971929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26784376011792721609314619 40176564017689082413971929)
            ·
              refine ⟨30132423013266811810478947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40176564017689082413971929 30132423013266811810478947)
              ·
                refine ⟨45198634519900217715718421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30132423013266811810478947 45198634519900217715718421)
                ·
                  refine ⟨2118685993120322705424301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45198634519900217715718421 2118685993120322705424301)
                  ·
                    refine ⟨794507247420121014534113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2118685993120322705424301 794507247420121014534113)
                    ·
                      rfl

theorem cell22_2320946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_2320946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320946 prefixEnd_2320946 := by exact prefixLift 2320946
  have htrace : WordTrace (prefixWord ++ tailWord_2320946) baseStart_2320946 baseEnd_2320946 := by
    simpa [prefixWord, tailWord_2320946, baseEnd_2320946] using wordTrace_append hprefix tailTrace_2320946
  have hstable : (prefixWord ++ tailWord_2320946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320946).length < 2 ^ (prefixWord ++ tailWord_2320946).sum := by decide
  have hdescent : baseEnd_2320946 < baseStart_2320946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320965 : List Nat := [1, 3, 1, 1, 1, 7, 2, 2, 4]
def baseStart_2320965 : Nat := 118140960795 + 2320965 * 2 ^ 59
def prefixEnd_2320965 : Nat := 4983230072969 + 3 ^ 40 * 2320965 * 2
def baseEnd_2320965 : Nat := 264837917169470432769685

theorem tailTrace_2320965 : CollatzResearch.WordTrace tailWord_2320965 prefixEnd_2320965 264837917169470432769685 := by
  unfold tailWord_2320965
  simp only [CollatzResearch.WordTrace]
  refine ⟨84652548036547669108948349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56435032024365112739298899 84652548036547669108948349)
  ·
    refine ⟨31744705513705375915855631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84652548036547669108948349 31744705513705375915855631)
    ·
      refine ⟨47617058270558063873783447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31744705513705375915855631 47617058270558063873783447)
      ·
        refine ⟨71425587405837095810675171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47617058270558063873783447 71425587405837095810675171)
        ·
          refine ⟨107138381108755643716012757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71425587405837095810675171 107138381108755643716012757)
          ·
            refine ⟨2511055807236460399594049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 107138381108755643716012757 2511055807236460399594049)
            ·
              refine ⟨1883291855427345299695537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2511055807236460399594049 1883291855427345299695537)
              ·
                refine ⟨1412468891570508974771653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1883291855427345299695537 1412468891570508974771653)
                ·
                  refine ⟨264837917169470432769685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1412468891570508974771653 264837917169470432769685)
                  ·
                    rfl

theorem cell22_2320965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 4].length) (baseStart_2320965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2320965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2320965 prefixEnd_2320965 := by exact prefixLift 2320965
  have htrace : WordTrace (prefixWord ++ tailWord_2320965) baseStart_2320965 baseEnd_2320965 := by
    simpa [prefixWord, tailWord_2320965, baseEnd_2320965] using wordTrace_append hprefix tailTrace_2320965
  have hstable : (prefixWord ++ tailWord_2320965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320965).length < 2 ^ (prefixWord ++ tailWord_2320965).sum := by decide
  have hdescent : baseEnd_2320965 < baseStart_2320965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321014 : List Nat := [5, 1, 1, 2, 4, 1, 1, 2, 2, 3]
def baseStart_2321014 : Nat := 118140960795 + 2321014 * 2 ^ 59
def prefixEnd_2321014 : Nat := 4983230072969 + 3 ^ 40 * 2321014 * 2
def baseEnd_2321014 : Nat := 794530525209791503833905

theorem tailTrace_2321014 : CollatzResearch.WordTrace tailWord_2321014 prefixEnd_2321014 794530525209791503833905 := by
  unfold tailWord_2321014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5290895950835634404842631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56436223475580100318321397 5290895950835634404842631)
  ·
    refine ⟨7936343926253451607263947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5290895950835634404842631 7936343926253451607263947)
    ·
      refine ⟨11904515889380177410895921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7936343926253451607263947 11904515889380177410895921)
      ·
        refine ⟨8928386917035133058171941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11904515889380177410895921 8928386917035133058171941)
        ·
          refine ⟨1674072546944087448407239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8928386917035133058171941 1674072546944087448407239)
          ·
            refine ⟨2511108820416131172610859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1674072546944087448407239 2511108820416131172610859)
            ·
              refine ⟨3766663230624196758916289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2511108820416131172610859 3766663230624196758916289)
              ·
                refine ⟨2824997422968147569187217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3766663230624196758916289 2824997422968147569187217)
                ·
                  refine ⟨2118748067226110676890413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2824997422968147569187217 2118748067226110676890413)
                  ·
                    refine ⟨794530525209791503833905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2118748067226110676890413 794530525209791503833905)
                    ·
                      rfl

theorem cell22_2321014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_2321014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321014 prefixEnd_2321014 := by exact prefixLift 2321014
  have htrace : WordTrace (prefixWord ++ tailWord_2321014) baseStart_2321014 baseEnd_2321014 := by
    simpa [prefixWord, tailWord_2321014, baseEnd_2321014] using wordTrace_append hprefix tailTrace_2321014
  have hstable : (prefixWord ++ tailWord_2321014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321014).length < 2 ^ (prefixWord ++ tailWord_2321014).sum := by decide
  have hdescent : baseEnd_2321014 < baseStart_2321014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321025 : List Nat := [1, 2, 4, 2, 1, 1, 1, 6, 1, 3]
def baseStart_2321025 : Nat := 118140960795 + 2321025 * 2 ^ 59
def prefixEnd_2321025 : Nat := 4983230072969 + 3 ^ 40 * 2321025 * 2
def baseEnd_2321025 : Nat := 794534290734591141808871

theorem tailTrace_2321025 : CollatzResearch.WordTrace tailWord_2321025 prefixEnd_2321025 794534290734591141808871 := by
  unfold tailWord_2321025
  simp only [CollatzResearch.WordTrace]
  refine ⟨84654736416330299356132529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56436490944220199570755019 84654736416330299356132529)
  ·
    refine ⟨63491052312247724517099397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84654736416330299356132529 63491052312247724517099397)
    ·
      refine ⟨11904572308546448346956137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63491052312247724517099397 11904572308546448346956137)
      ·
        refine ⟨8928429231409836260217103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11904572308546448346956137 8928429231409836260217103)
        ·
          refine ⟨13392643847114754390325655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8928429231409836260217103 13392643847114754390325655)
          ·
            refine ⟨20088965770672131585488483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13392643847114754390325655 20088965770672131585488483)
            ·
              refine ⟨30133448656008197378232725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20088965770672131585488483 30133448656008197378232725)
              ·
                refine ⟨1412505405750384252104659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30133448656008197378232725 1412505405750384252104659)
                ·
                  refine ⟨2118758108625576378156989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1412505405750384252104659 2118758108625576378156989)
                  ·
                    refine ⟨794534290734591141808871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2118758108625576378156989 794534290734591141808871)
                    ·
                      rfl

theorem cell22_2321025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_2321025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321025 prefixEnd_2321025 := by exact prefixLift 2321025
  have htrace : WordTrace (prefixWord ++ tailWord_2321025) baseStart_2321025 baseEnd_2321025 := by
    simpa [prefixWord, tailWord_2321025, baseEnd_2321025] using wordTrace_append hprefix tailTrace_2321025
  have hstable : (prefixWord ++ tailWord_2321025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321025).length < 2 ^ (prefixWord ++ tailWord_2321025).sum := by decide
  have hdescent : baseEnd_2321025 < baseStart_2321025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321089 : List Nat := [1, 2, 6, 2, 1, 2, 2, 1, 5]
def baseStart_2321089 : Nat := 118140960795 + 2321089 * 2 ^ 59
def prefixEnd_2321089 : Nat := 4983230072969 + 3 ^ 40 * 2321089 * 2
def baseEnd_2321089 : Nat := 264852066414172102736225

theorem tailTrace_2321089 : CollatzResearch.WordTrace tailWord_2321089 prefixEnd_2321089 264852066414172102736225 := by
  unfold tailWord_2321089
  simp only [CollatzResearch.WordTrace]
  refine ⟨84657070688098438286462321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56438047125398958857641547 84657070688098438286462321)
  ·
    refine ⟨63492803016073828714846741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84657070688098438286462321 63492803016073828714846741)
    ·
      refine ⟨2976225141378460721008441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63492803016073828714846741 2976225141378460721008441)
      ·
        refine ⟨2232168856033845540756331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2976225141378460721008441 2232168856033845540756331)
        ·
          refine ⟨3348253284050768311134497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2232168856033845540756331 3348253284050768311134497)
          ·
            refine ⟨2511189963038076233350873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3348253284050768311134497 2511189963038076233350873)
            ·
              refine ⟨1883392472278557175013155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2511189963038076233350873 1883392472278557175013155)
              ·
                refine ⟨2825088708417835762519733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1883392472278557175013155 2825088708417835762519733)
                ·
                  refine ⟨264852066414172102736225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2825088708417835762519733 264852066414172102736225)
                  ·
                    rfl

theorem cell22_2321089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 5].length) (baseStart_2321089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321089 prefixEnd_2321089 := by exact prefixLift 2321089
  have htrace : WordTrace (prefixWord ++ tailWord_2321089) baseStart_2321089 baseEnd_2321089 := by
    simpa [prefixWord, tailWord_2321089, baseEnd_2321089] using wordTrace_append hprefix tailTrace_2321089
  have hstable : (prefixWord ++ tailWord_2321089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321089).length < 2 ^ (prefixWord ++ tailWord_2321089).sum := by decide
  have hdescent : baseEnd_2321089 < baseStart_2321089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321111 : List Nat := [1, 1, 3, 2, 1, 4, 2, 8]
def baseStart_2321111 : Nat := 118140960795 + 2321111 * 2 ^ 59
def prefixEnd_2321111 : Nat := 4983230072969 + 3 ^ 40 * 2321111 * 2
def baseEnd_2321111 : Nat := 88284858921346176017623

theorem tailTrace_2321111 : CollatzResearch.WordTrace tailWord_2321111 prefixEnd_2321111 88284858921346176017623 := by
  unfold tailWord_2321111
  simp only [CollatzResearch.WordTrace]
  refine ⟨84657873094018736043763187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56438582062679157362508791 84657873094018736043763187)
  ·
    refine ⟨126986809641028104065644781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84657873094018736043763187 126986809641028104065644781)
    ·
      refine ⟨47620053615385539024616793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126986809641028104065644781 47620053615385539024616793)
      ·
        refine ⟨35715040211539154268462595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47620053615385539024616793 35715040211539154268462595)
        ·
          refine ⟨53572560317308731402693893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35715040211539154268462595 53572560317308731402693893)
          ·
            refine ⟨10044855059495387138005105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53572560317308731402693893 10044855059495387138005105)
            ·
              refine ⟨7533641294621540353503829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10044855059495387138005105 7533641294621540353503829)
              ·
                refine ⟨88284858921346176017623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7533641294621540353503829 88284858921346176017623)
                ·
                  rfl

theorem cell22_2321111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 8].length) (baseStart_2321111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321111 prefixEnd_2321111 := by exact prefixLift 2321111
  have htrace : WordTrace (prefixWord ++ tailWord_2321111) baseStart_2321111 baseEnd_2321111 := by
    simpa [prefixWord, tailWord_2321111, baseEnd_2321111] using wordTrace_append hprefix tailTrace_2321111
  have hstable : (prefixWord ++ tailWord_2321111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321111).length < 2 ^ (prefixWord ++ tailWord_2321111).sum := by decide
  have hdescent : baseEnd_2321111 < baseStart_2321111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321113 : List Nat := [1, 2, 1, 2, 3, 2, 4, 1, 2, 4]
def baseStart_2321113 : Nat := 118140960795 + 2321113 * 2 ^ 59
def prefixEnd_2321113 : Nat := 4983230072969 + 3 ^ 40 * 2321113 * 2
def baseEnd_2321113 : Nat := 794564414932988245608601

theorem tailTrace_2321113 : CollatzResearch.WordTrace tailWord_2321113 prefixEnd_2321113 794564414932988245608601 := by
  unfold tailWord_2321113
  simp only [CollatzResearch.WordTrace]
  refine ⟨84657946040011490385335993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56438630693340993590223995 84657946040011490385335993)
  ·
    refine ⟨63493459530008617789001995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84657946040011490385335993 63493459530008617789001995)
    ·
      refine ⟨95240189295012926683502993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63493459530008617789001995 95240189295012926683502993)
      ·
        refine ⟨71430141971259695012627245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95240189295012926683502993 71430141971259695012627245)
        ·
          refine ⟨26786303239222385629735217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71430141971259695012627245 26786303239222385629735217)
          ·
            refine ⟨20089727429416789222301413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26786303239222385629735217 20089727429416789222301413)
            ·
              refine ⟨3766823893015647979181515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20089727429416789222301413 3766823893015647979181515)
              ·
                refine ⟨5650235839523471968772273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3766823893015647979181515 5650235839523471968772273)
                ·
                  refine ⟨4237676879642603976579205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5650235839523471968772273 4237676879642603976579205)
                  ·
                    refine ⟨794564414932988245608601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4237676879642603976579205 794564414932988245608601)
                    ·
                      rfl

theorem cell22_2321113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 4].length) (baseStart_2321113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321113 prefixEnd_2321113 := by exact prefixLift 2321113
  have htrace : WordTrace (prefixWord ++ tailWord_2321113) baseStart_2321113 baseEnd_2321113 := by
    simpa [prefixWord, tailWord_2321113, baseEnd_2321113] using wordTrace_append hprefix tailTrace_2321113
  have hstable : (prefixWord ++ tailWord_2321113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321113).length < 2 ^ (prefixWord ++ tailWord_2321113).sum := by decide
  have hdescent : baseEnd_2321113 < baseStart_2321113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321128 : List Nat := [2, 1, 4, 1, 5, 9]
def baseStart_2321128 : Nat := 118140960795 + 2321128 * 2 ^ 59
def prefixEnd_2321128 : Nat := 4983230072969 + 3 ^ 40 * 2321128 * 2
def baseEnd_2321128 : Nat := 9809500614068311191155

theorem tailTrace_2321128 : CollatzResearch.WordTrace tailWord_2321128 prefixEnd_2321128 9809500614068311191155 := by
  unfold tailWord_2321128
  simp only [CollatzResearch.WordTrace]
  refine ⟨42329246567478573973566019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56438995423304765298088025 42329246567478573973566019)
  ·
    refine ⟨63493869851217860960349029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42329246567478573973566019 63493869851217860960349029)
    ·
      refine ⟨11905100597103348930065443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63493869851217860960349029 11905100597103348930065443)
      ·
        refine ⟨17857650895655023395098165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11905100597103348930065443 17857650895655023395098165)
        ·
          refine ⟨1674154771467658443290453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17857650895655023395098165 1674154771467658443290453)
          ·
            refine ⟨9809500614068311191155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1674154771467658443290453 9809500614068311191155)
            ·
              rfl

theorem cell22_2321128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 9].length) (baseStart_2321128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321128 prefixEnd_2321128 := by exact prefixLift 2321128
  have htrace : WordTrace (prefixWord ++ tailWord_2321128) baseStart_2321128 baseEnd_2321128 := by
    simpa [prefixWord, tailWord_2321128, baseEnd_2321128] using wordTrace_append hprefix tailTrace_2321128
  have hstable : (prefixWord ++ tailWord_2321128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321128).length < 2 ^ (prefixWord ++ tailWord_2321128).sum := by decide
  have hdescent : baseEnd_2321128 < baseStart_2321128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321143 : List Nat := [1, 1, 3, 1, 1, 1, 3, 5, 3, 3]
def baseStart_2321143 : Nat := 118140960795 + 2321143 * 2 ^ 59
def prefixEnd_2321143 : Nat := 4983230072969 + 3 ^ 40 * 2321143 * 2
def baseEnd_2321143 : Nat := 794574684546078167358509

theorem tailTrace_2321143 : CollatzResearch.WordTrace tailWord_2321143 prefixEnd_2321143 794574684546078167358509 := by
  unfold tailWord_2321143
  simp only [CollatzResearch.WordTrace]
  refine ⟨84659040229902805508928083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56439360153268537005952055 84659040229902805508928083)
  ·
    refine ⟨126988560344854208263392125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84659040229902805508928083 126988560344854208263392125)
    ·
      refine ⟨47620710129320328098772047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126988560344854208263392125 47620710129320328098772047)
      ·
        refine ⟨71431065193980492148158071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47620710129320328098772047 71431065193980492148158071)
        ·
          refine ⟨107146597790970738222237107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71431065193980492148158071 107146597790970738222237107)
          ·
            refine ⟨160719896686456107333355661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107146597790970738222237107 160719896686456107333355661)
            ·
              refine ⟨60269961257421040250008373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160719896686456107333355661 60269961257421040250008373)
              ·
                refine ⟨5650308867883222523438285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60269961257421040250008373 5650308867883222523438285)
                ·
                  refine ⟨2118865825456208446289357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5650308867883222523438285 2118865825456208446289357)
                  ·
                    refine ⟨794574684546078167358509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2118865825456208446289357 794574684546078167358509)
                    ·
                      rfl

theorem cell22_2321143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_2321143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321143 prefixEnd_2321143 := by exact prefixLift 2321143
  have htrace : WordTrace (prefixWord ++ tailWord_2321143) baseStart_2321143 baseEnd_2321143 := by
    simpa [prefixWord, tailWord_2321143, baseEnd_2321143] using wordTrace_append hprefix tailTrace_2321143
  have hstable : (prefixWord ++ tailWord_2321143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321143).length < 2 ^ (prefixWord ++ tailWord_2321143).sum := by decide
  have hdescent : baseEnd_2321143 < baseStart_2321143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321160 : List Nat := [2, 1, 3, 2, 2, 3, 1, 2, 3, 3]
def baseStart_2321160 : Nat := 118140960795 + 2321160 * 2 ^ 59
def prefixEnd_2321160 : Nat := 4983230072969 + 3 ^ 40 * 2321160 * 2
def baseEnd_2321160 : Nat := 794580503993495789683457

theorem tailTrace_2321160 : CollatzResearch.WordTrace tailWord_2321160 prefixEnd_2321160 794580503993495789683457 := by
  unfold tailWord_2321160
  simp only [CollatzResearch.WordTrace]
  refine ⟨42329830135420608706148467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56439773513894144941531289 42329830135420608706148467)
  ·
    refine ⟨63494745203130913059222701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42329830135420608706148467 63494745203130913059222701)
    ·
      refine ⟨23810529451174092397208513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63494745203130913059222701 23810529451174092397208513)
      ·
        refine ⟨17857897088380569297906385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23810529451174092397208513 17857897088380569297906385)
        ·
          refine ⟨13393422816285426973429789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17857897088380569297906385 13393422816285426973429789)
          ·
            refine ⟨5022533556107035115036171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13393422816285426973429789 5022533556107035115036171)
            ·
              refine ⟨7533800334160552672554257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5022533556107035115036171 7533800334160552672554257)
              ·
                refine ⟨5650350250620414504415693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7533800334160552672554257 5650350250620414504415693)
                ·
                  refine ⟨2118881343982655439155885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5650350250620414504415693 2118881343982655439155885)
                  ·
                    refine ⟨794580503993495789683457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2118881343982655439155885 794580503993495789683457)
                    ·
                      rfl

theorem cell22_2321160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_2321160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321160 prefixEnd_2321160 := by exact prefixLift 2321160
  have htrace : WordTrace (prefixWord ++ tailWord_2321160) baseStart_2321160 baseEnd_2321160 := by
    simpa [prefixWord, tailWord_2321160, baseEnd_2321160] using wordTrace_append hprefix tailTrace_2321160
  have hstable : (prefixWord ++ tailWord_2321160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321160).length < 2 ^ (prefixWord ++ tailWord_2321160).sum := by decide
  have hdescent : baseEnd_2321160 < baseStart_2321160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321171 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 1, 7]
def baseStart_2321171 : Nat := 118140960795 + 2321171 * 2 ^ 59
def prefixEnd_2321171 : Nat := 4983230072969 + 3 ^ 40 * 2321171 * 2
def baseEnd_2321171 : Nat := 794584269518295427658423

theorem tailTrace_2321171 : CollatzResearch.WordTrace tailWord_2321171 prefixEnd_2321171 794584269518295427658423 := by
  unfold tailWord_2321171
  simp only [CollatzResearch.WordTrace]
  refine ⟨84660061473801366290947367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56440040982534244193964911 84660061473801366290947367)
  ·
    refine ⟨126990092210702049436421051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84660061473801366290947367 126990092210702049436421051)
    ·
      refine ⟨190485138316053074154631577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126990092210702049436421051 190485138316053074154631577)
      ·
        refine ⟨142863853737039805615973683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190485138316053074154631577 142863853737039805615973683)
        ·
          refine ⟨214295780605559708423960525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142863853737039805615973683 214295780605559708423960525)
          ·
            refine ⟨80360917727084890658985197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 214295780605559708423960525 80360917727084890658985197)
            ·
              refine ⟨30135344147656833997119449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80360917727084890658985197 30135344147656833997119449)
              ·
                refine ⟨22601508110742625497839587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30135344147656833997119449 22601508110742625497839587)
                ·
                  refine ⟨33902262166113938246759381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22601508110742625497839587 33902262166113938246759381)
                  ·
                    refine ⟨794584269518295427658423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33902262166113938246759381 794584269518295427658423)
                    ·
                      rfl

theorem cell22_2321171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 7].length) (baseStart_2321171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321171 prefixEnd_2321171 := by exact prefixLift 2321171
  have htrace : WordTrace (prefixWord ++ tailWord_2321171) baseStart_2321171 baseEnd_2321171 := by
    simpa [prefixWord, tailWord_2321171, baseEnd_2321171] using wordTrace_append hprefix tailTrace_2321171
  have hstable : (prefixWord ++ tailWord_2321171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321171).length < 2 ^ (prefixWord ++ tailWord_2321171).sum := by decide
  have hdescent : baseEnd_2321171 < baseStart_2321171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321194 : List Nat := [3, 1, 4, 3, 1, 1, 2, 1, 3, 3]
def baseStart_2321194 : Nat := 118140960795 + 2321194 * 2 ^ 59
def prefixEnd_2321194 : Nat := 4983230072969 + 3 ^ 40 * 2321194 * 2
def baseEnd_2321194 : Nat := 794592142888331034333353

theorem tailTrace_2321194 : CollatzResearch.WordTrace tailWord_2321194 prefixEnd_2321194 794592142888331034333353 := by
  unfold tailWord_2321194
  simp only [CollatzResearch.WordTrace]
  refine ⟨21165225088179510304758659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56440600235145360812689757 21165225088179510304758659)
  ·
    refine ⟨31747837632269265457137989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21165225088179510304758659 31747837632269265457137989)
    ·
      refine ⟨5952719556050487273213373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31747837632269265457137989 5952719556050487273213373)
      ·
        refine ⟨2232269833518932727455015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5952719556050487273213373 2232269833518932727455015)
        ·
          refine ⟨3348404750278399091182523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2232269833518932727455015 3348404750278399091182523)
          ·
            refine ⟨5022607125417598636773785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3348404750278399091182523 5022607125417598636773785)
            ·
              refine ⟨3766955344063198977580339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5022607125417598636773785 3766955344063198977580339)
              ·
                refine ⟨5650433016094798466370509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3766955344063198977580339 5650433016094798466370509)
                ·
                  refine ⟨2118912381035549424888941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5650433016094798466370509 2118912381035549424888941)
                  ·
                    refine ⟨794592142888331034333353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2118912381035549424888941 794592142888331034333353)
                    ·
                      rfl

theorem cell22_2321194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_2321194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321194 prefixEnd_2321194 := by exact prefixLift 2321194
  have htrace : WordTrace (prefixWord ++ tailWord_2321194) baseStart_2321194 baseEnd_2321194 := by
    simpa [prefixWord, tailWord_2321194, baseEnd_2321194] using wordTrace_append hprefix tailTrace_2321194
  have hstable : (prefixWord ++ tailWord_2321194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321194).length < 2 ^ (prefixWord ++ tailWord_2321194).sum := by decide
  have hdescent : baseEnd_2321194 < baseStart_2321194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321267 : List Nat := [1, 1, 1, 2, 2, 1, 8, 1, 2, 3]
def baseStart_2321267 : Nat := 118140960795 + 2321267 * 2 ^ 59
def prefixEnd_2321267 : Nat := 4983230072969 + 3 ^ 40 * 2321267 * 2
def baseEnd_2321267 : Nat := 794617132280183177258129

theorem tailTrace_2321267 : CollatzResearch.WordTrace tailWord_2321267 prefixEnd_2321267 794617132280183177258129 := by
  unfold tailWord_2321267
  simp only [CollatzResearch.WordTrace]
  refine ⟨84663562881453574686442055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56442375254302383124294703 84663562881453574686442055)
  ·
    refine ⟨126995344322180362029663083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84663562881453574686442055 126995344322180362029663083)
    ·
      refine ⟨190493016483270543044494625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126995344322180362029663083 190493016483270543044494625)
      ·
        refine ⟨142869762362452907283370969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190493016483270543044494625 142869762362452907283370969)
        ·
          refine ⟨107152321771839680462528227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142869762362452907283370969 107152321771839680462528227)
          ·
            refine ⟨160728482657759520693792341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107152321771839680462528227 160728482657759520693792341)
            ·
              refine ⟨1883536906145619383130379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 160728482657759520693792341 1883536906145619383130379)
              ·
                refine ⟨2825305359218429074695569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1883536906145619383130379 2825305359218429074695569)
                ·
                  refine ⟨2118979019413821806021677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2825305359218429074695569 2118979019413821806021677)
                  ·
                    refine ⟨794617132280183177258129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2118979019413821806021677 794617132280183177258129)
                    ·
                      rfl

theorem cell22_2321267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 2, 3].length) (baseStart_2321267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321267 prefixEnd_2321267 := by exact prefixLift 2321267
  have htrace : WordTrace (prefixWord ++ tailWord_2321267) baseStart_2321267 baseEnd_2321267 := by
    simpa [prefixWord, tailWord_2321267, baseEnd_2321267] using wordTrace_append hprefix tailTrace_2321267
  have hstable : (prefixWord ++ tailWord_2321267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321267).length < 2 ^ (prefixWord ++ tailWord_2321267).sum := by decide
  have hdescent : baseEnd_2321267 < baseStart_2321267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321323 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 2, 5]
def baseStart_2321323 : Nat := 118140960795 + 2321323 * 2 ^ 59
def prefixEnd_2321323 : Nat := 4983230072969 + 3 ^ 40 * 2321323 * 2
def baseEnd_2321323 : Nat := 794636302224617697857957

theorem tailTrace_2321323 : CollatzResearch.WordTrace tailWord_2321323 prefixEnd_2321323 794636302224617697857957 := by
  unfold tailWord_2321323
  simp only [CollatzResearch.WordTrace]
  refine ⟨84665605369250696250480623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56443736912833797500320415 84665605369250696250480623)
  ·
    refine ⟨126998408053876044375720935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84665605369250696250480623 126998408053876044375720935)
    ·
      refine ⟨190497612080814066563581403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126998408053876044375720935 190497612080814066563581403)
      ·
        refine ⟨285746418121221099845372105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190497612080814066563581403 285746418121221099845372105)
        ·
          refine ⟨214309813590915824884029079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285746418121221099845372105 214309813590915824884029079)
          ·
            refine ⟨321464720386373737326043619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214309813590915824884029079 321464720386373737326043619)
            ·
              refine ⟨482197080579560605989065429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321464720386373737326043619 482197080579560605989065429)
              ·
                refine ⟨11301494076083451702868721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 482197080579560605989065429 11301494076083451702868721)
                ·
                  refine ⟨8476120557062588777151541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11301494076083451702868721 8476120557062588777151541)
                  ·
                    refine ⟨794636302224617697857957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8476120557062588777151541 794636302224617697857957)
                    ·
                      rfl

theorem cell22_2321323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 5].length) (baseStart_2321323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321323 prefixEnd_2321323 := by exact prefixLift 2321323
  have htrace : WordTrace (prefixWord ++ tailWord_2321323) baseStart_2321323 baseEnd_2321323 := by
    simpa [prefixWord, tailWord_2321323, baseEnd_2321323] using wordTrace_append hprefix tailTrace_2321323
  have hstable : (prefixWord ++ tailWord_2321323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321323).length < 2 ^ (prefixWord ++ tailWord_2321323).sum := by decide
  have hdescent : baseEnd_2321323 < baseStart_2321323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321370 : List Nat := [3, 1, 1, 2, 4, 1, 1, 3, 6]
def baseStart_2321370 : Nat := 118140960795 + 2321370 * 2 ^ 59
def prefixEnd_2321370 : Nat := 4983230072969 + 3 ^ 40 * 2321370 * 2
def baseEnd_2321370 : Nat := 264884130428375080644271

theorem tailTrace_2321370 : CollatzResearch.WordTrace tailWord_2321370 prefixEnd_2321370 264884130428375080644271 := by
  unfold tailWord_2321370
  simp only [CollatzResearch.WordTrace]
  refine ⟨21166829900020105819360391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56444879733386948851627709 21166829900020105819360391)
  ·
    refine ⟨31750244850030158729040587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21166829900020105819360391 31750244850030158729040587)
    ·
      refine ⟨47625367275045238093560881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31750244850030158729040587 47625367275045238093560881)
      ·
        refine ⟨35719025456283928570170661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47625367275045238093560881 35719025456283928570170661)
        ·
          refine ⟨6697317273053236606906999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35719025456283928570170661 6697317273053236606906999)
          ·
            refine ⟨10045975909579854910360499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6697317273053236606906999 10045975909579854910360499)
            ·
              refine ⟨15068963864369782365540749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10045975909579854910360499 15068963864369782365540749)
              ·
                refine ⟨5650861449138668387077781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15068963864369782365540749 5650861449138668387077781)
                ·
                  refine ⟨264884130428375080644271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5650861449138668387077781 264884130428375080644271)
                  ·
                    rfl

theorem cell22_2321370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_2321370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321370 prefixEnd_2321370 := by exact prefixLift 2321370
  have htrace : WordTrace (prefixWord ++ tailWord_2321370) baseStart_2321370 baseEnd_2321370 := by
    simpa [prefixWord, tailWord_2321370, baseEnd_2321370] using wordTrace_append hprefix tailTrace_2321370
  have hstable : (prefixWord ++ tailWord_2321370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321370).length < 2 ^ (prefixWord ++ tailWord_2321370).sum := by decide
  have hdescent : baseEnd_2321370 < baseStart_2321370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321400 : List Nat := [2, 1, 2, 1, 1, 3, 1, 5, 2, 4]
def baseStart_2321400 : Nat := 118140960795 + 2321400 * 2 ^ 59
def prefixEnd_2321400 : Nat := 4983230072969 + 3 ^ 40 * 2321400 * 2
def baseEnd_2321400 : Nat := 794662660898215163682721

theorem tailTrace_2321400 : CollatzResearch.WordTrace tailWord_2321400 prefixEnd_2321400 794662660898215163682721 := by
  unfold tailWord_2321400
  simp only [CollatzResearch.WordTrace]
  refine ⟨42334206894985869200516827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56445609193314492267355769 42334206894985869200516827)
  ·
    refine ⟨63501310342478803800775241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42334206894985869200516827 63501310342478803800775241)
    ·
      refine ⟨47625982756859102850581431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63501310342478803800775241 47625982756859102850581431)
      ·
        refine ⟨71438974135288654275872147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47625982756859102850581431 71438974135288654275872147)
        ·
          refine ⟨107158461202932981413808221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71438974135288654275872147 107158461202932981413808221)
          ·
            refine ⟨40184422951099868030178083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107158461202932981413808221 40184422951099868030178083)
            ·
              refine ⟨60276634426649802045267125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40184422951099868030178083 60276634426649802045267125)
              ·
                refine ⟨5650934477498418941743793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60276634426649802045267125 5650934477498418941743793)
                ·
                  refine ⟨4238200858123814206307845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5650934477498418941743793 4238200858123814206307845)
                  ·
                    refine ⟨794662660898215163682721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4238200858123814206307845 794662660898215163682721)
                    ·
                      rfl

theorem cell22_2321400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_2321400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321400 prefixEnd_2321400 := by exact prefixLift 2321400
  have htrace : WordTrace (prefixWord ++ tailWord_2321400) baseStart_2321400 baseEnd_2321400 := by
    simpa [prefixWord, tailWord_2321400, baseEnd_2321400] using wordTrace_append hprefix tailTrace_2321400
  have hstable : (prefixWord ++ tailWord_2321400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321400).length < 2 ^ (prefixWord ++ tailWord_2321400).sum := by decide
  have hdescent : baseEnd_2321400 < baseStart_2321400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321404 : List Nat := [2, 2, 2, 1, 2, 5, 1, 3, 4]
def baseStart_2321404 : Nat := 118140960795 + 2321404 * 2 ^ 59
def prefixEnd_2321404 : Nat := 4983230072969 + 3 ^ 40 * 2321404 * 2
def baseEnd_2321404 : Nat := 264888010059986828860903

theorem tailTrace_2321404 : CollatzResearch.WordTrace tailWord_2321404 prefixEnd_2321404 264888010059986828860903 := by
  unfold tailWord_2321404
  simp only [CollatzResearch.WordTrace]
  refine ⟨42334279840978623542089633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56445706454638164722786177 42334279840978623542089633)
  ·
    refine ⟨31750709880733967656567225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42334279840978623542089633 31750709880733967656567225)
    ·
      refine ⟨23813032410550475742425419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31750709880733967656567225 23813032410550475742425419)
      ·
        refine ⟨35719548615825713613638129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23813032410550475742425419 35719548615825713613638129)
        ·
          refine ⟨26789661461869285210228597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35719548615825713613638129 26789661461869285210228597)
          ·
            refine ⟨2511530762050245488458931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26789661461869285210228597 2511530762050245488458931)
            ·
              refine ⟨3767296143075368232688397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2511530762050245488458931 3767296143075368232688397)
              ·
                refine ⟨1412736053653263087258149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3767296143075368232688397 1412736053653263087258149)
                ·
                  refine ⟨264888010059986828860903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1412736053653263087258149 264888010059986828860903)
                  ·
                    rfl

theorem cell22_2321404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 4].length) (baseStart_2321404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321404 prefixEnd_2321404 := by exact prefixLift 2321404
  have htrace : WordTrace (prefixWord ++ tailWord_2321404) baseStart_2321404 baseEnd_2321404 := by
    simpa [prefixWord, tailWord_2321404, baseEnd_2321404] using wordTrace_append hprefix tailTrace_2321404
  have hstable : (prefixWord ++ tailWord_2321404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321404).length < 2 ^ (prefixWord ++ tailWord_2321404).sum := by decide
  have hdescent : baseEnd_2321404 < baseStart_2321404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321475 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 2, 5]
def baseStart_2321475 : Nat := 118140960795 + 2321475 * 2 ^ 59
def prefixEnd_2321475 : Nat := 4983230072969 + 3 ^ 40 * 2321475 * 2
def baseEnd_2321475 : Nat := 794688334930939968057491

theorem tailTrace_2321475 : CollatzResearch.WordTrace tailWord_2321475 prefixEnd_2321475 794688334930939968057491 := by
  unfold tailWord_2321475
  simp only [CollatzResearch.WordTrace]
  refine ⟨84671149264700026210013879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56447432843133350806675919 84671149264700026210013879)
  ·
    refine ⟨127006723897050039315020819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84671149264700026210013879 127006723897050039315020819)
    ·
      refine ⟨190510085845575058972531229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127006723897050039315020819 190510085845575058972531229)
      ·
        refine ⟨71441282192090647114699211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190510085845575058972531229 71441282192090647114699211)
        ·
          refine ⟨107161923288135970672048817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71441282192090647114699211 107161923288135970672048817)
          ·
            refine ⟨80371442466101978004036613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107161923288135970672048817 80371442466101978004036613)
            ·
              refine ⟨15069645462394120875756865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80371442466101978004036613 15069645462394120875756865)
              ·
                refine ⟨11302234096795590656817649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15069645462394120875756865 11302234096795590656817649)
                ·
                  refine ⟨8476675572596692992613237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11302234096795590656817649 8476675572596692992613237)
                  ·
                    refine ⟨794688334930939968057491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8476675572596692992613237 794688334930939968057491)
                    ·
                      rfl

theorem cell22_2321475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 5].length) (baseStart_2321475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321475 prefixEnd_2321475 := by exact prefixLift 2321475
  have htrace : WordTrace (prefixWord ++ tailWord_2321475) baseStart_2321475 baseEnd_2321475 := by
    simpa [prefixWord, tailWord_2321475, baseEnd_2321475] using wordTrace_append hprefix tailTrace_2321475
  have hstable : (prefixWord ++ tailWord_2321475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321475).length < 2 ^ (prefixWord ++ tailWord_2321475).sum := by decide
  have hdescent : baseEnd_2321475 < baseStart_2321475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321505 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 8]
def baseStart_2321505 : Nat := 118140960795 + 2321505 * 2 ^ 59
def prefixEnd_2321505 : Nat := 4983230072969 + 3 ^ 40 * 2321505 * 2
def baseEnd_2321505 : Nat := 264899534848009963269133

theorem tailTrace_2321505 : CollatzResearch.WordTrace tailWord_2321505 prefixEnd_2321505 264899534848009963269133 := by
  unfold tailWord_2321505
  simp only [CollatzResearch.WordTrace]
  refine ⟨84672243454591341333605969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56448162303060894222403979 84672243454591341333605969)
  ·
    refine ⟨63504182590943506000204477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84672243454591341333605969 63504182590943506000204477)
    ·
      refine ⟨23814068471603814750076679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63504182590943506000204477 23814068471603814750076679)
      ·
        refine ⟨35721102707405722125115019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23814068471603814750076679 35721102707405722125115019)
        ·
          refine ⟨53581654061108583187672529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35721102707405722125115019 53581654061108583187672529)
          ·
            refine ⟨40186240545831437390754397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53581654061108583187672529 40186240545831437390754397)
            ·
              refine ⟨15069840204686789021532899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40186240545831437390754397 15069840204686789021532899)
              ·
                refine ⟨22604760307030183532299349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15069840204686789021532899 22604760307030183532299349)
                ·
                  refine ⟨264899534848009963269133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22604760307030183532299349 264899534848009963269133)
                  ·
                    rfl

theorem cell22_2321505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 8].length) (baseStart_2321505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321505 prefixEnd_2321505 := by exact prefixLift 2321505
  have htrace : WordTrace (prefixWord ++ tailWord_2321505) baseStart_2321505 baseEnd_2321505 := by
    simpa [prefixWord, tailWord_2321505, baseEnd_2321505] using wordTrace_append hprefix tailTrace_2321505
  have hstable : (prefixWord ++ tailWord_2321505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321505).length < 2 ^ (prefixWord ++ tailWord_2321505).sum := by decide
  have hdescent : baseEnd_2321505 < baseStart_2321505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321507 : List Nat := [1, 1, 1, 5, 1, 1, 1, 6, 1, 4]
def baseStart_2321507 : Nat := 118140960795 + 2321507 * 2 ^ 59
def prefixEnd_2321507 : Nat := 4983230072969 + 3 ^ 40 * 2321507 * 2
def baseEnd_2321507 : Nat := 794699289184902551257393

theorem tailTrace_2321507 : CollatzResearch.WordTrace tailWord_2321507 prefixEnd_2321507 794699289184902551257393 := by
  unfold tailWord_2321507
  simp only [CollatzResearch.WordTrace]
  refine ⟨84672316400584095675178775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56448210933722730450119183 84672316400584095675178775)
  ·
    refine ⟨127008474600876143512768163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84672316400584095675178775 127008474600876143512768163)
    ·
      refine ⟨190512711901314215269152245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127008474600876143512768163 190512711901314215269152245)
      ·
        refine ⟨17860566740748207681483023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 190512711901314215269152245 17860566740748207681483023)
        ·
          refine ⟨26790850111122311522224535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17860566740748207681483023 26790850111122311522224535)
          ·
            refine ⟨40186275166683467283336803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26790850111122311522224535 40186275166683467283336803)
            ·
              refine ⟨60279412750025200925005205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40186275166683467283336803 60279412750025200925005205)
              ·
                refine ⟨2825597472657431293359619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60279412750025200925005205 2825597472657431293359619)
                ·
                  refine ⟨4238396208986146940039429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2825597472657431293359619 4238396208986146940039429)
                  ·
                    refine ⟨794699289184902551257393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4238396208986146940039429 794699289184902551257393)
                    ·
                      rfl

theorem cell22_2321507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 4].length) (baseStart_2321507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321507 prefixEnd_2321507 := by exact prefixLift 2321507
  have htrace : WordTrace (prefixWord ++ tailWord_2321507) baseStart_2321507 baseEnd_2321507 := by
    simpa [prefixWord, tailWord_2321507, baseEnd_2321507] using wordTrace_append hprefix tailTrace_2321507
  have hstable : (prefixWord ++ tailWord_2321507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321507).length < 2 ^ (prefixWord ++ tailWord_2321507).sum := by decide
  have hdescent : baseEnd_2321507 < baseStart_2321507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321554 : List Nat := [3, 2, 3, 1, 1, 2, 3, 1, 1, 5]
def baseStart_2321554 : Nat := 118140960795 + 2321554 * 2 ^ 59
def prefixEnd_2321554 : Nat := 4983230072969 + 3 ^ 40 * 2321554 * 2
def baseEnd_2321554 : Nat := 794715378245410095332249

theorem tailTrace_2321554 : CollatzResearch.WordTrace tailWord_2321554 prefixEnd_2321554 794715378245410095332249 := by
  unfold tailWord_2321554
  simp only [CollatzResearch.WordTrace]
  refine ⟨21168507657853455675534929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56449353754275881801426477 21168507657853455675534929)
  ·
    refine ⟨15876380743390091756651197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21168507657853455675534929 15876380743390091756651197)
    ·
      refine ⟨5953642778771284408744199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15876380743390091756651197 5953642778771284408744199)
      ·
        refine ⟨8930464168156926613116299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5953642778771284408744199 8930464168156926613116299)
        ·
          refine ⟨13395696252235389919674449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8930464168156926613116299 13395696252235389919674449)
          ·
            refine ⟨10046772189176542439755837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13395696252235389919674449 10046772189176542439755837)
            ·
              refine ⟨3767539570941203414908439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10046772189176542439755837 3767539570941203414908439)
              ·
                refine ⟨5651309356411805122362659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3767539570941203414908439 5651309356411805122362659)
                ·
                  refine ⟨8476964034617707683543989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5651309356411805122362659 8476964034617707683543989)
                  ·
                    refine ⟨794715378245410095332249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8476964034617707683543989 794715378245410095332249)
                    ·
                      rfl

theorem cell22_2321554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_2321554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321554 prefixEnd_2321554 := by exact prefixLift 2321554
  have htrace : WordTrace (prefixWord ++ tailWord_2321554) baseStart_2321554 baseEnd_2321554 := by
    simpa [prefixWord, tailWord_2321554, baseEnd_2321554] using wordTrace_append hprefix tailTrace_2321554
  have hstable : (prefixWord ++ tailWord_2321554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321554).length < 2 ^ (prefixWord ++ tailWord_2321554).sum := by decide
  have hdescent : baseEnd_2321554 < baseStart_2321554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321590 : List Nat := [5, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_2321590 : Nat := 118140960795 + 2321590 * 2 ^ 59
def prefixEnd_2321590 : Nat := 4983230072969 + 3 ^ 40 * 2321590 * 2
def baseEnd_2321590 : Nat := 264909233927039333810713

theorem tailTrace_2321590 : CollatzResearch.WordTrace tailWord_2321590 prefixEnd_2321590 264909233927039333810713 := by
  unfold tailWord_2321590
  simp only [CollatzResearch.WordTrace]
  refine ⟨5292208978705212553153139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56450229106188933900300149 5292208978705212553153139)
  ·
    refine ⟨7938313468057818829729709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5292208978705212553153139 7938313468057818829729709)
    ·
      refine ⟨2976867550521682061148641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7938313468057818829729709 2976867550521682061148641)
      ·
        refine ⟨2232650662891261545861481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2976867550521682061148641 2232650662891261545861481)
        ·
          refine ⟨1674487997168446159396111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2232650662891261545861481 1674487997168446159396111)
          ·
            refine ⟨2511731995752669239094167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1674487997168446159396111 2511731995752669239094167)
            ·
              refine ⟨3767597993629003858641251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2511731995752669239094167 3767597993629003858641251)
              ·
                refine ⟨5651396990443505787961877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3767597993629003858641251 5651396990443505787961877)
                ·
                  refine ⟨264909233927039333810713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5651396990443505787961877 264909233927039333810713)
                  ·
                    rfl

theorem cell22_2321590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_2321590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321590 prefixEnd_2321590 := by exact prefixLift 2321590
  have htrace : WordTrace (prefixWord ++ tailWord_2321590) baseStart_2321590 baseEnd_2321590 := by
    simpa [prefixWord, tailWord_2321590, baseEnd_2321590] using wordTrace_append hprefix tailTrace_2321590
  have hstable : (prefixWord ++ tailWord_2321590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321590).length < 2 ^ (prefixWord ++ tailWord_2321590).sum := by decide
  have hdescent : baseEnd_2321590 < baseStart_2321590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321599 : List Nat := [1, 1, 2, 2, 2, 2, 5, 1, 3, 3]
def baseStart_2321599 : Nat := 118140960795 + 2321599 * 2 ^ 59
def prefixEnd_2321599 : Nat := 4983230072969 + 3 ^ 40 * 2321599 * 2
def baseEnd_2321599 : Nat := 794730782665044977957111

theorem tailTrace_2321599 : CollatzResearch.WordTrace tailWord_2321599 prefixEnd_2321599 794730782665044977957111 := by
  unfold tailWord_2321599
  simp only [CollatzResearch.WordTrace]
  refine ⟨84675671916250795387527851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56450447944167196925018567 84675671916250795387527851)
  ·
    refine ⟨127013507874376193081291777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84675671916250795387527851 127013507874376193081291777)
    ·
      refine ⟨95260130905782144810968833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127013507874376193081291777 95260130905782144810968833)
      ·
        refine ⟨71445098179336608608226625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95260130905782144810968833 71445098179336608608226625)
        ·
          refine ⟨53583823634502456456169969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71445098179336608608226625 53583823634502456456169969)
          ·
            refine ⟨40187867725876842342127477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53583823634502456456169969 40187867725876842342127477)
            ·
              refine ⟨3767612599300953969574451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40187867725876842342127477 3767612599300953969574451)
              ·
                refine ⟨5651418898951430954361677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3767612599300953969574451 5651418898951430954361677)
                ·
                  refine ⟨2119282087106786607885629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5651418898951430954361677 2119282087106786607885629)
                  ·
                    refine ⟨794730782665044977957111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2119282087106786607885629 794730782665044977957111)
                    ·
                      rfl

theorem cell22_2321599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 3].length) (baseStart_2321599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321599 prefixEnd_2321599 := by exact prefixLift 2321599
  have htrace : WordTrace (prefixWord ++ tailWord_2321599) baseStart_2321599 baseEnd_2321599 := by
    simpa [prefixWord, tailWord_2321599, baseEnd_2321599] using wordTrace_append hprefix tailTrace_2321599
  have hstable : (prefixWord ++ tailWord_2321599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321599).length < 2 ^ (prefixWord ++ tailWord_2321599).sum := by decide
  have hdescent : baseEnd_2321599 < baseStart_2321599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321657 : List Nat := [1, 2, 1, 3, 1, 1, 4, 3, 6]
def baseStart_2321657 : Nat := 118140960795 + 2321657 * 2 ^ 59
def prefixEnd_2321657 : Nat := 4983230072969 + 3 ^ 40 * 2321657 * 2
def baseEnd_2321657 : Nat := 264916879083450720002311

theorem tailTrace_2321657 : CollatzResearch.WordTrace tailWord_2321657 prefixEnd_2321657 264916879083450720002311 := by
  unfold tailWord_2321657
  simp only [CollatzResearch.WordTrace]
  refine ⟨84677787350040671293139225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56451858233360447528759483 84677787350040671293139225)
  ·
    refine ⟨63508340512530503469854419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84677787350040671293139225 63508340512530503469854419)
    ·
      refine ⟨95262510768795755204781629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63508340512530503469854419 95262510768795755204781629)
      ·
        refine ⟨35723441538298408201793111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95262510768795755204781629 35723441538298408201793111)
        ·
          refine ⟨53585162307447612302689667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35723441538298408201793111 53585162307447612302689667)
          ·
            refine ⟨80377743461171418454034501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53585162307447612302689667 80377743461171418454034501)
            ·
              refine ⟨15070826898969640960131469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80377743461171418454034501 15070826898969640960131469)
              ·
                refine ⟨5651560087113615360049301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15070826898969640960131469 5651560087113615360049301)
                ·
                  refine ⟨264916879083450720002311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5651560087113615360049301 264916879083450720002311)
                  ·
                    rfl

theorem cell22_2321657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 6].length) (baseStart_2321657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321657 prefixEnd_2321657 := by exact prefixLift 2321657
  have htrace : WordTrace (prefixWord ++ tailWord_2321657) baseStart_2321657 baseEnd_2321657 := by
    simpa [prefixWord, tailWord_2321657, baseEnd_2321657] using wordTrace_append hprefix tailTrace_2321657
  have hstable : (prefixWord ++ tailWord_2321657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321657).length < 2 ^ (prefixWord ++ tailWord_2321657).sum := by decide
  have hdescent : baseEnd_2321657 < baseStart_2321657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321693 : List Nat := [1, 4, 2, 3, 1, 1, 4, 1, 1, 4]
def baseStart_2321693 : Nat := 118140960795 + 2321693 * 2 ^ 59
def prefixEnd_2321693 : Nat := 4983230072969 + 3 ^ 40 * 2321693 * 2
def baseEnd_2321693 : Nat := 794762960786060066106823

theorem tailTrace_2321693 : CollatzResearch.WordTrace tailWord_2321693 prefixEnd_2321693 794762960786060066106823 := by
  unfold tailWord_2321693
  simp only [CollatzResearch.WordTrace]
  refine ⟨84679100377910249441449733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56452733585273499627633155 84679100377910249441449733)
  ·
    refine ⟨15877331320858171770271825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84679100377910249441449733 15877331320858171770271825)
    ·
      refine ⟨11907998490643628827703869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15877331320858171770271825 11907998490643628827703869)
      ·
        refine ⟨4465499433991360810388951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11907998490643628827703869 4465499433991360810388951)
        ·
          refine ⟨6698249150987041215583427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4465499433991360810388951 6698249150987041215583427)
          ·
            refine ⟨10047373726480561823375141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6698249150987041215583427 10047373726480561823375141)
            ·
              refine ⟨1883882573715105341882839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10047373726480561823375141 1883882573715105341882839)
              ·
                refine ⟨2825823860572658012824259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1883882573715105341882839 2825823860572658012824259)
                ·
                  refine ⟨4238735790858987019236389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2825823860572658012824259 4238735790858987019236389)
                  ·
                    refine ⟨794762960786060066106823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4238735790858987019236389 794762960786060066106823)
                    ·
                      rfl

theorem cell22_2321693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_2321693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321693 prefixEnd_2321693 := by exact prefixLift 2321693
  have htrace : WordTrace (prefixWord ++ tailWord_2321693) baseStart_2321693 baseEnd_2321693 := by
    simpa [prefixWord, tailWord_2321693, baseEnd_2321693] using wordTrace_append hprefix tailTrace_2321693
  have hstable : (prefixWord ++ tailWord_2321693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321693).length < 2 ^ (prefixWord ++ tailWord_2321693).sum := by decide
  have hdescent : baseEnd_2321693 < baseStart_2321693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321747 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 9]
def baseStart_2321747 : Nat := 118140960795 + 2321747 * 2 ^ 59
def prefixEnd_2321747 : Nat := 4983230072969 + 3 ^ 40 * 2321747 * 2
def baseEnd_2321747 : Nat := 264927148696540641752219

theorem tailTrace_2321747 : CollatzResearch.WordTrace tailWord_2321747 prefixEnd_2321747 264927148696540641752219 := by
  unfold tailWord_2321747
  simp only [CollatzResearch.WordTrace]
  refine ⟨84681069919714616663915495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56454046613143077775943663 84681069919714616663915495)
  ·
    refine ⟨127021604879571924995873243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84681069919714616663915495 127021604879571924995873243)
    ·
      refine ⟨190532407319357887493809865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127021604879571924995873243 190532407319357887493809865)
      ·
        refine ⟨142899305489518415620357399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190532407319357887493809865 142899305489518415620357399)
        ·
          refine ⟨214348958234277623430536099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142899305489518415620357399 214348958234277623430536099)
          ·
            refine ⟨321523437351416435145804149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214348958234277623430536099 321523437351416435145804149)
            ·
              refine ⟨30142822251695290794919139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 321523437351416435145804149 30142822251695290794919139)
              ·
                refine ⟨45214233377542936192378709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30142822251695290794919139 45214233377542936192378709)
                ·
                  refine ⟨264927148696540641752219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45214233377542936192378709 264927148696540641752219)
                  ·
                    rfl

theorem cell22_2321747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 9].length) (baseStart_2321747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321747 prefixEnd_2321747 := by exact prefixLift 2321747
  have htrace : WordTrace (prefixWord ++ tailWord_2321747) baseStart_2321747 baseEnd_2321747 := by
    simpa [prefixWord, tailWord_2321747, baseEnd_2321747] using wordTrace_append hprefix tailTrace_2321747
  have hstable : (prefixWord ++ tailWord_2321747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321747).length < 2 ^ (prefixWord ++ tailWord_2321747).sum := by decide
  have hdescent : baseEnd_2321747 < baseStart_2321747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321764 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 7]
def baseStart_2321764 : Nat := 118140960795 + 2321764 * 2 ^ 59
def prefixEnd_2321764 : Nat := 4983230072969 + 3 ^ 40 * 2321764 * 2
def baseEnd_2321764 : Nat := 264929088512346515860535

theorem tailTrace_2321764 : CollatzResearch.WordTrace tailWord_2321764 prefixEnd_2321764 264929088512346515860535 := by
  unfold tailWord_2321764
  simp only [CollatzResearch.WordTrace]
  refine ⟨42340844980326514283642173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56454459973768685711522897 42340844980326514283642173)
  ·
    refine ⟨15877816867622442856365815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42340844980326514283642173 15877816867622442856365815)
    ·
      refine ⟨23816725301433664284548723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15877816867622442856365815 23816725301433664284548723)
      ·
        refine ⟨35725087952150496426823085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23816725301433664284548723 35725087952150496426823085)
        ·
          refine ⟨13396907982056436160058657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35725087952150496426823085 13396907982056436160058657)
          ·
            refine ⟨10047680986542327120043993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13396907982056436160058657 10047680986542327120043993)
            ·
              refine ⟨7535760739906745340032995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10047680986542327120043993 7535760739906745340032995)
              ·
                refine ⟨11303641109860118010049493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7535760739906745340032995 11303641109860118010049493)
                ·
                  refine ⟨264929088512346515860535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11303641109860118010049493 264929088512346515860535)
                  ·
                    rfl

theorem cell22_2321764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_2321764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321764 prefixEnd_2321764 := by exact prefixLift 2321764
  have htrace : WordTrace (prefixWord ++ tailWord_2321764) baseStart_2321764 baseEnd_2321764 := by
    simpa [prefixWord, tailWord_2321764, baseEnd_2321764] using wordTrace_append hprefix tailTrace_2321764
  have hstable : (prefixWord ++ tailWord_2321764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321764).length < 2 ^ (prefixWord ++ tailWord_2321764).sum := by decide
  have hdescent : baseEnd_2321764 < baseStart_2321764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321774 : List Nat := [4, 1, 2, 4, 2, 1, 2, 1, 2, 3]
def baseStart_2321774 : Nat := 118140960795 + 2321774 * 2 ^ 59
def prefixEnd_2321774 : Nat := 4983230072969 + 3 ^ 40 * 2321774 * 2
def baseEnd_2321774 : Nat := 794790688741402854831575

theorem tailTrace_2321774 : CollatzResearch.WordTrace tailWord_2321774 prefixEnd_2321774 794790688741402854831575 := by
  unfold tailWord_2321774
  simp only [CollatzResearch.WordTrace]
  refine ⟨10585256836327100034393547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56454703127077866850098917 10585256836327100034393547)
  ·
    refine ⟨15877885254490650051590321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10585256836327100034393547 15877885254490650051590321)
    ·
      refine ⟨11908413940867987538692741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15877885254490650051590321 11908413940867987538692741)
      ·
        refine ⟨2232827613912747663504889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11908413940867987538692741 2232827613912747663504889)
        ·
          refine ⟨1674620710434560747628667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2232827613912747663504889 1674620710434560747628667)
          ·
            refine ⟨2511931065651841121443001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1674620710434560747628667 2511931065651841121443001)
            ·
              refine ⟨1883948299238880841082251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2511931065651841121443001 1883948299238880841082251)
              ·
                refine ⟨2825922448858321261623377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1883948299238880841082251 2825922448858321261623377)
                ·
                  refine ⟨2119441836643740946217533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2825922448858321261623377 2119441836643740946217533)
                  ·
                    refine ⟨794790688741402854831575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2119441836643740946217533 794790688741402854831575)
                    ·
                      rfl

theorem cell22_2321774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_2321774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321774 prefixEnd_2321774 := by exact prefixLift 2321774
  have htrace : WordTrace (prefixWord ++ tailWord_2321774) baseStart_2321774 baseEnd_2321774 := by
    simpa [prefixWord, tailWord_2321774, baseEnd_2321774] using wordTrace_append hprefix tailTrace_2321774
  have hstable : (prefixWord ++ tailWord_2321774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321774).length < 2 ^ (prefixWord ++ tailWord_2321774).sum := by decide
  have hdescent : baseEnd_2321774 < baseStart_2321774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321824 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 3, 5]
def baseStart_2321824 : Nat := 118140960795 + 2321824 * 2 ^ 59
def prefixEnd_2321824 : Nat := 4983230072969 + 3 ^ 40 * 2321824 * 2
def baseEnd_2321824 : Nat := 794807804763219391081421

theorem tailTrace_2321824 : CollatzResearch.WordTrace tailWord_2321824 prefixEnd_2321824 794807804763219391081421 := by
  unfold tailWord_2321824
  simp only [CollatzResearch.WordTrace]
  refine ⟨42341939170217829407234263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56455918893623772542979017 42341939170217829407234263)
  ·
    refine ⟨63512908755326744110851395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42341939170217829407234263 63512908755326744110851395)
    ·
      refine ⟨95269363132990116166277093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63512908755326744110851395 95269363132990116166277093)
      ·
        refine ⟨17863005587435646781176955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95269363132990116166277093 17863005587435646781176955)
        ·
          refine ⟨26794508381153470171765433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17863005587435646781176955 26794508381153470171765433)
          ·
            refine ⟨20095881285865102628824075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26794508381153470171765433 20095881285865102628824075)
            ·
              refine ⟨30143821928797653943236113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20095881285865102628824075 30143821928797653943236113)
              ·
                refine ⟨22607866446598240457427085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30143821928797653943236113 22607866446598240457427085)
                ·
                  refine ⟨8477949917474340171535157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22607866446598240457427085 8477949917474340171535157)
                  ·
                    refine ⟨794807804763219391081421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8477949917474340171535157 794807804763219391081421)
                    ·
                      rfl

theorem cell22_2321824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_2321824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321824 prefixEnd_2321824 := by exact prefixLift 2321824
  have htrace : WordTrace (prefixWord ++ tailWord_2321824) baseStart_2321824 baseEnd_2321824 := by
    simpa [prefixWord, tailWord_2321824, baseEnd_2321824] using wordTrace_append hprefix tailTrace_2321824
  have hstable : (prefixWord ++ tailWord_2321824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321824).length < 2 ^ (prefixWord ++ tailWord_2321824).sum := by decide
  have hdescent : baseEnd_2321824 < baseStart_2321824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321839 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 4, 4]
def baseStart_2321839 : Nat := 118140960795 + 2321839 * 2 ^ 59
def prefixEnd_2321839 : Nat := 4983230072969 + 3 ^ 40 * 2321839 * 2
def baseEnd_2321839 : Nat := 794812939569764351956375

theorem tailTrace_2321839 : CollatzResearch.WordTrace tailWord_2321839 prefixEnd_2321839 794812939569764351956375 := by
  unfold tailWord_2321839
  simp only [CollatzResearch.WordTrace]
  refine ⟨84684425435381316376264571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56456283623587544250843047 84684425435381316376264571)
  ·
    refine ⟨127026638153071974564396857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84684425435381316376264571 127026638153071974564396857)
    ·
      refine ⟨95269978614803980923297643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127026638153071974564396857 95269978614803980923297643)
      ·
        refine ⟨142904967922205971384946465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95269978614803980923297643 142904967922205971384946465)
        ·
          refine ⟨107178725941654478538709849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142904967922205971384946465 107178725941654478538709849)
          ·
            refine ⟨80384044456240858904032387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107178725941654478538709849 80384044456240858904032387)
            ·
              refine ⟨120576066684361288356048581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80384044456240858904032387 120576066684361288356048581)
              ·
                refine ⟨22608012503317741566759109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120576066684361288356048581 22608012503317741566759109)
                ·
                  refine ⟨4239002344372076543767333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22608012503317741566759109 4239002344372076543767333)
                  ·
                    refine ⟨794812939569764351956375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4239002344372076543767333 794812939569764351956375)
                    ·
                      rfl

theorem cell22_2321839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 4].length) (baseStart_2321839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321839 prefixEnd_2321839 := by exact prefixLift 2321839
  have htrace : WordTrace (prefixWord ++ tailWord_2321839) baseStart_2321839 baseEnd_2321839 := by
    simpa [prefixWord, tailWord_2321839, baseEnd_2321839] using wordTrace_append hprefix tailTrace_2321839
  have hstable : (prefixWord ++ tailWord_2321839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321839).length < 2 ^ (prefixWord ++ tailWord_2321839).sum := by decide
  have hdescent : baseEnd_2321839 < baseStart_2321839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321841 : List Nat := [1, 2, 2, 4, 1, 1, 4, 1, 1, 5]
def baseStart_2321841 : Nat := 118140960795 + 2321841 * 2 ^ 59
def prefixEnd_2321841 : Nat := 4983230072969 + 3 ^ 40 * 2321841 * 2
def baseEnd_2321841 : Nat := 794813624210637013406369

theorem tailTrace_2321841 : CollatzResearch.WordTrace tailWord_2321841 prefixEnd_2321841 794813624210637013406369 := by
  unfold tailWord_2321841
  simp only [CollatzResearch.WordTrace]
  refine ⟨84684498381374070717837377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56456332254249380478558251 84684498381374070717837377)
  ·
    refine ⟨63513373786030553038378033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84684498381374070717837377 63513373786030553038378033)
    ·
      refine ⟨47635030339522914778783525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63513373786030553038378033 47635030339522914778783525)
      ·
        refine ⟨8931568188660546521021911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47635030339522914778783525 8931568188660546521021911)
        ·
          refine ⟨13397352282990819781532867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8931568188660546521021911 13397352282990819781532867)
          ·
            refine ⟨20096028424486229672299301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13397352282990819781532867 20096028424486229672299301)
            ·
              refine ⟨3768005329591168063556119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20096028424486229672299301 3768005329591168063556119)
              ·
                refine ⟨5652007994386752095334179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3768005329591168063556119 5652007994386752095334179)
                ·
                  refine ⟨8478011991580128143001269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5652007994386752095334179 8478011991580128143001269)
                  ·
                    refine ⟨794813624210637013406369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8478011991580128143001269 794813624210637013406369)
                    ·
                      rfl

theorem cell22_2321841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_2321841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321841 prefixEnd_2321841 := by exact prefixLift 2321841
  have htrace : WordTrace (prefixWord ++ tailWord_2321841) baseStart_2321841 baseEnd_2321841 := by
    simpa [prefixWord, tailWord_2321841, baseEnd_2321841] using wordTrace_append hprefix tailTrace_2321841
  have hstable : (prefixWord ++ tailWord_2321841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321841).length < 2 ^ (prefixWord ++ tailWord_2321841).sum := by decide
  have hdescent : baseEnd_2321841 < baseStart_2321841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321856 : List Nat := [2, 1, 1, 2, 3, 1, 5, 1, 2, 4]
def baseStart_2321856 : Nat := 118140960795 + 2321856 * 2 ^ 59
def prefixEnd_2321856 : Nat := 4983230072969 + 3 ^ 40 * 2321856 * 2
def baseEnd_2321856 : Nat := 794818759017181974281323

theorem tailTrace_2321856 : CollatzResearch.WordTrace tailWord_2321856 prefixEnd_2321856 794818759017181974281323 := by
  unfold tailWord_2321856
  simp only [CollatzResearch.WordTrace]
  refine ⟨42342522738159864139816711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56456696984213152186422281 42342522738159864139816711)
  ·
    refine ⟨63513784107239796209725067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42342522738159864139816711 63513784107239796209725067)
    ·
      refine ⟨95270676160859694314587601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63513784107239796209725067 95270676160859694314587601)
      ·
        refine ⟨71453007120644770735940701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95270676160859694314587601 71453007120644770735940701)
        ·
          refine ⟨26794877670241789025977763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71453007120644770735940701 26794877670241789025977763)
          ·
            refine ⟨40192316505362683538966645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26794877670241789025977763 40192316505362683538966645)
            ·
              refine ⟨3768029672377751581778123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40192316505362683538966645 3768029672377751581778123)
              ·
                refine ⟨5652044508566627372667185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3768029672377751581778123 5652044508566627372667185)
                ·
                  refine ⟨4239033381424970529500389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5652044508566627372667185 4239033381424970529500389)
                  ·
                    refine ⟨794818759017181974281323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4239033381424970529500389 794818759017181974281323)
                    ·
                      rfl

theorem cell22_2321856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 2, 4].length) (baseStart_2321856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321856 prefixEnd_2321856 := by exact prefixLift 2321856
  have htrace : WordTrace (prefixWord ++ tailWord_2321856) baseStart_2321856 baseEnd_2321856 := by
    simpa [prefixWord, tailWord_2321856, baseEnd_2321856] using wordTrace_append hprefix tailTrace_2321856
  have hstable : (prefixWord ++ tailWord_2321856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321856).length < 2 ^ (prefixWord ++ tailWord_2321856).sum := by decide
  have hdescent : baseEnd_2321856 < baseStart_2321856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321860 : List Nat := [2, 3, 3, 2, 1, 2, 2, 3, 4]
def baseStart_2321860 : Nat := 118140960795 + 2321860 * 2 ^ 59
def prefixEnd_2321860 : Nat := 4983230072969 + 3 ^ 40 * 2321860 * 2
def baseEnd_2321860 : Nat := 264940042766309099060437

theorem tailTrace_2321860 : CollatzResearch.WordTrace tailWord_2321860 prefixEnd_2321860 264940042766309099060437 := by
  unfold tailWord_2321860
  simp only [CollatzResearch.WordTrace]
  refine ⟨42342595684152618481389517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56456794245536824641852689 42342595684152618481389517)
  ·
    refine ⟨15878473381557231930521069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42342595684152618481389517 15878473381557231930521069)
    ·
      refine ⟨5954427518083961973945401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15878473381557231930521069 5954427518083961973945401)
      ·
        refine ⟨4465820638562971480459051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5954427518083961973945401 4465820638562971480459051)
        ·
          refine ⟨6698730957844457220688577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4465820638562971480459051 6698730957844457220688577)
          ·
            refine ⟨5024048218383342915516433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6698730957844457220688577 5024048218383342915516433)
            ·
              refine ⟨3768036163787507186637325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5024048218383342915516433 3768036163787507186637325)
              ·
                refine ⟨1413013561420315194988997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3768036163787507186637325 1413013561420315194988997)
                ·
                  refine ⟨264940042766309099060437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1413013561420315194988997 264940042766309099060437)
                  ·
                    rfl

theorem cell22_2321860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_2321860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321860 prefixEnd_2321860 := by exact prefixLift 2321860
  have htrace : WordTrace (prefixWord ++ tailWord_2321860) baseStart_2321860 baseEnd_2321860 := by
    simpa [prefixWord, tailWord_2321860, baseEnd_2321860] using wordTrace_append hprefix tailTrace_2321860
  have hstable : (prefixWord ++ tailWord_2321860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321860).length < 2 ^ (prefixWord ++ tailWord_2321860).sum := by decide
  have hdescent : baseEnd_2321860 < baseStart_2321860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321946 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 3, 4]
def baseStart_2321946 : Nat := 118140960795 + 2321946 * 2 ^ 59
def prefixEnd_2321946 : Nat := 4983230072969 + 3 ^ 40 * 2321946 * 2
def baseEnd_2321946 : Nat := 794849567856451739531047

theorem tailTrace_2321946 : CollatzResearch.WordTrace tailWord_2321946 prefixEnd_2321946 794849567856451739531047 := by
  unfold tailWord_2321946
  simp only [CollatzResearch.WordTrace]
  refine ⟨21172082011498418412602423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56458885363995782433606461 21172082011498418412602423)
  ·
    refine ⟨31758123017247627618903635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21172082011498418412602423 31758123017247627618903635)
    ·
      refine ⟨47637184525871441428355453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31758123017247627618903635 47637184525871441428355453)
      ·
        refine ⟨17863944197201790535633295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47637184525871441428355453 17863944197201790535633295)
        ·
          refine ⟨26795916295802685803449943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17863944197201790535633295 26795916295802685803449943)
          ·
            refine ⟨40193874443704028705174915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26795916295802685803449943 40193874443704028705174915)
            ·
              refine ⟨60290811665556043057762373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40193874443704028705174915 60290811665556043057762373)
              ·
                refine ⟨11304527187291758073330445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60290811665556043057762373 11304527187291758073330445)
                ·
                  refine ⟨4239197695234409277498917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11304527187291758073330445 4239197695234409277498917)
                  ·
                    refine ⟨794849567856451739531047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4239197695234409277498917 794849567856451739531047)
                    ·
                      rfl

theorem cell22_2321946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_2321946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321946 prefixEnd_2321946 := by exact prefixLift 2321946
  have htrace : WordTrace (prefixWord ++ tailWord_2321946) baseStart_2321946 baseEnd_2321946 := by
    simpa [prefixWord, tailWord_2321946, baseEnd_2321946] using wordTrace_append hprefix tailTrace_2321946
  have hstable : (prefixWord ++ tailWord_2321946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321946).length < 2 ^ (prefixWord ++ tailWord_2321946).sum := by decide
  have hdescent : baseEnd_2321946 < baseStart_2321946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321976 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 3, 5]
def baseStart_2321976 : Nat := 118140960795 + 2321976 * 2 ^ 59
def prefixEnd_2321976 : Nat := 4983230072969 + 3 ^ 40 * 2321976 * 2
def baseEnd_2321976 : Nat := 794859837469541661280955

theorem tailTrace_2321976 : CollatzResearch.WordTrace tailWord_2321976 prefixEnd_2321976 794859837469541661280955 := by
  unfold tailWord_2321976
  simp only [CollatzResearch.WordTrace]
  refine ⟨42344711117942494387000891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56459614823923325849334521 42344711117942494387000891)
  ·
    refine ⟨63517066676913741580501337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42344711117942494387000891 63517066676913741580501337)
    ·
      refine ⟨47637800007685306185376003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63517066676913741580501337 47637800007685306185376003)
      ·
        refine ⟨71456700011527959278064005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47637800007685306185376003 71456700011527959278064005)
        ·
          refine ⟨13398131252161492364637001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71456700011527959278064005 13398131252161492364637001)
          ·
            refine ⟨10048598439121119273477751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13398131252161492364637001 10048598439121119273477751)
            ·
              refine ⟨15072897658681678910216627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10048598439121119273477751 15072897658681678910216627)
              ·
                refine ⟨22609346488022518365324941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15072897658681678910216627 22609346488022518365324941)
                ·
                  refine ⟨8478504933008444386996853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22609346488022518365324941 8478504933008444386996853)
                  ·
                    refine ⟨794859837469541661280955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8478504933008444386996853 794859837469541661280955)
                    ·
                      rfl

theorem cell22_2321976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_2321976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321976 prefixEnd_2321976 := by exact prefixLift 2321976
  have htrace : WordTrace (prefixWord ++ tailWord_2321976) baseStart_2321976 baseEnd_2321976 := by
    simpa [prefixWord, tailWord_2321976, baseEnd_2321976] using wordTrace_append hprefix tailTrace_2321976
  have hstable : (prefixWord ++ tailWord_2321976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321976).length < 2 ^ (prefixWord ++ tailWord_2321976).sum := by decide
  have hdescent : baseEnd_2321976 < baseStart_2321976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321978 : List Nat := [3, 1, 1, 1, 3, 2, 2, 5, 4]
def baseStart_2321978 : Nat := 118140960795 + 2321978 * 2 ^ 59
def prefixEnd_2321978 : Nat := 4983230072969 + 3 ^ 40 * 2321978 * 2
def baseEnd_2321978 : Nat := 264953507370138107576983

theorem tailTrace_2321978 : CollatzResearch.WordTrace tailWord_2321978 prefixEnd_2321978 264953507370138107576983 := by
  unfold tailWord_2321978
  simp only [CollatzResearch.WordTrace]
  refine ⟨21172373795469435778893647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56459663454585162077049725 21172373795469435778893647)
  ·
    refine ⟨31758560693204153668340471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21172373795469435778893647 31758560693204153668340471)
    ·
      refine ⟨47637841039806230502510707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31758560693204153668340471 47637841039806230502510707)
      ·
        refine ⟨71456761559709345753766061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47637841039806230502510707 71456761559709345753766061)
        ·
          refine ⟨26796285584891004657662273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71456761559709345753766061 26796285584891004657662273)
          ·
            refine ⟨20097214188668253493246705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26796285584891004657662273 20097214188668253493246705)
            ·
              refine ⟨15072910641501190119935029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20097214188668253493246705 15072910641501190119935029)
              ·
                refine ⟨1413085372640736573743909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15072910641501190119935029 1413085372640736573743909)
                ·
                  refine ⟨264953507370138107576983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1413085372640736573743909 264953507370138107576983)
                  ·
                    rfl

theorem cell22_2321978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 4].length) (baseStart_2321978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2321978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2321978 prefixEnd_2321978 := by exact prefixLift 2321978
  have htrace : WordTrace (prefixWord ++ tailWord_2321978) baseStart_2321978 baseEnd_2321978 := by
    simpa [prefixWord, tailWord_2321978, baseEnd_2321978] using wordTrace_append hprefix tailTrace_2321978
  have hstable : (prefixWord ++ tailWord_2321978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321978).length < 2 ^ (prefixWord ++ tailWord_2321978).sum := by decide
  have hdescent : baseEnd_2321978 < baseStart_2321978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322055 : List Nat := [1, 1, 4, 2, 1, 4, 2, 1, 3, 3]
def baseStart_2322055 : Nat := 118140960795 + 2322055 * 2 ^ 59
def prefixEnd_2322055 : Nat := 4983230072969 + 3 ^ 40 * 2322055 * 2
def baseEnd_2322055 : Nat := 794886880784011788555713

theorem tailTrace_2322055 : CollatzResearch.WordTrace tailWord_2322055 prefixEnd_2322055 794886880784011788555713 := by
  unfold tailWord_2322055
  simp only [CollatzResearch.WordTrace]
  refine ⟨84692303602598785266127619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56461535735065856844085079 84692303602598785266127619)
  ·
    refine ⟨127038455403898177899191429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84692303602598785266127619 127038455403898177899191429)
    ·
      refine ⟨23819710388230908356098393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127038455403898177899191429 23819710388230908356098393)
      ·
        refine ⟨17864782791173181267073795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23819710388230908356098393 17864782791173181267073795)
        ·
          refine ⟨26797174186759771900610693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17864782791173181267073795 26797174186759771900610693)
          ·
            refine ⟨5024470160017457231364505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26797174186759771900610693 5024470160017457231364505)
            ·
              refine ⟨3768352620013092923523379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5024470160017457231364505 3768352620013092923523379)
              ·
                refine ⟨5652528930019639385285069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3768352620013092923523379 5652528930019639385285069)
                ·
                  refine ⟨2119698348757364769481901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5652528930019639385285069 2119698348757364769481901)
                  ·
                    refine ⟨794886880784011788555713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2119698348757364769481901 794886880784011788555713)
                    ·
                      rfl

theorem cell22_2322055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_2322055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322055 prefixEnd_2322055 := by exact prefixLift 2322055
  have htrace : WordTrace (prefixWord ++ tailWord_2322055) baseStart_2322055 baseEnd_2322055 := by
    simpa [prefixWord, tailWord_2322055, baseEnd_2322055] using wordTrace_append hprefix tailTrace_2322055
  have hstable : (prefixWord ++ tailWord_2322055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322055).length < 2 ^ (prefixWord ++ tailWord_2322055).sum := by decide
  have hdescent : baseEnd_2322055 < baseStart_2322055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322096 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 8]
def baseStart_2322096 : Nat := 118140960795 + 2322096 * 2 ^ 59
def prefixEnd_2322096 : Nat := 4983230072969 + 3 ^ 40 * 2322096 * 2
def baseEnd_2322096 : Nat := 264966971973967116093529

theorem tailTrace_2322096 : CollatzResearch.WordTrace tailWord_2322096 prefixEnd_2322096 264966971973967116093529 := by
  unfold tailWord_2322096
  simp only [CollatzResearch.WordTrace]
  refine ⟨42346899497725124634185071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56462532663633499512246761 42346899497725124634185071)
  ·
    refine ⟨63520349246587686951277607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42346899497725124634185071 63520349246587686951277607)
    ·
      refine ⟨95280523869881530426916411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63520349246587686951277607 95280523869881530426916411)
      ·
        refine ⟨142920785804822295640374617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95280523869881530426916411 142920785804822295640374617)
        ·
          refine ⟨107190589353616721730280963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142920785804822295640374617 107190589353616721730280963)
          ·
            refine ⟨160785884030425082595421445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107190589353616721730280963 160785884030425082595421445)
            ·
              refine ⟨30147353255704702986641521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160785884030425082595421445 30147353255704702986641521)
              ·
                refine ⟨22610514941778527239981141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30147353255704702986641521 22610514941778527239981141)
                ·
                  refine ⟨264966971973967116093529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22610514941778527239981141 264966971973967116093529)
                  ·
                    rfl

theorem cell22_2322096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 8].length) (baseStart_2322096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322096 prefixEnd_2322096 := by exact prefixLift 2322096
  have htrace : WordTrace (prefixWord ++ tailWord_2322096) baseStart_2322096 baseEnd_2322096 := by
    simpa [prefixWord, tailWord_2322096, baseEnd_2322096] using wordTrace_append hprefix tailTrace_2322096
  have hstable : (prefixWord ++ tailWord_2322096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322096).length < 2 ^ (prefixWord ++ tailWord_2322096).sum := by decide
  have hdescent : baseEnd_2322096 < baseStart_2322096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322128 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 6, 3]
def baseStart_2322128 : Nat := 118140960795 + 2322128 * 2 ^ 59
def prefixEnd_2322128 : Nat := 4983230072969 + 3 ^ 40 * 2322128 * 2
def baseEnd_2322128 : Nat := 794911870175863931480489

theorem tailTrace_2322128 : CollatzResearch.WordTrace tailWord_2322128 prefixEnd_2322128 794911870175863931480489 := by
  unfold tailWord_2322128
  simp only [CollatzResearch.WordTrace]
  refine ⟨42347483065667159366767519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56463310754222879155690025 42347483065667159366767519)
  ·
    refine ⟨63521224598500739050151279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42347483065667159366767519 63521224598500739050151279)
    ·
      refine ⟨95281836897751108575226919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63521224598500739050151279 95281836897751108575226919)
      ·
        refine ⟨142922755346626662862840379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95281836897751108575226919 142922755346626662862840379)
        ·
          refine ⟨214384133019939994294260569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142922755346626662862840379 214384133019939994294260569)
          ·
            refine ⟨160788099764954995720695427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214384133019939994294260569 160788099764954995720695427)
            ·
              refine ⟨241182149647432493581043141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160788099764954995720695427 241182149647432493581043141)
              ·
                refine ⟨45221653058893592546445589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 241182149647432493581043141 45221653058893592546445589)
                ·
                  refine ⟨2119764987135637150614637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45221653058893592546445589 2119764987135637150614637)
                  ·
                    refine ⟨794911870175863931480489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2119764987135637150614637 794911870175863931480489)
                    ·
                      rfl

theorem cell22_2322128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 6, 3].length) (baseStart_2322128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322128 prefixEnd_2322128 := by exact prefixLift 2322128
  have htrace : WordTrace (prefixWord ++ tailWord_2322128) baseStart_2322128 baseEnd_2322128 := by
    simpa [prefixWord, tailWord_2322128, baseEnd_2322128] using wordTrace_append hprefix tailTrace_2322128
  have hstable : (prefixWord ++ tailWord_2322128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322128).length < 2 ^ (prefixWord ++ tailWord_2322128).sum := by decide
  have hdescent : baseEnd_2322128 < baseStart_2322128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322132 : List Nat := [2, 4, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_2322132 : Nat := 118140960795 + 2322132 * 2 ^ 59
def prefixEnd_2322132 : Nat := 4983230072969 + 3 ^ 40 * 2322132 * 2
def baseEnd_2322132 : Nat := 794913239457609254380477

theorem tailTrace_2322132 : CollatzResearch.WordTrace tailWord_2322132 prefixEnd_2322132 794913239457609254380477 := by
  unfold tailWord_2322132
  simp only [CollatzResearch.WordTrace]
  refine ⟨42347556011659913708340325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56463408015546551611120433 42347556011659913708340325)
  ·
    refine ⟨7940166752186233820313811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42347556011659913708340325 7940166752186233820313811)
    ·
      refine ⟨11910250128279350730470717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7940166752186233820313811 11910250128279350730470717)
      ·
        refine ⟨4466343798104756523926519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11910250128279350730470717 4466343798104756523926519)
        ·
          refine ⟨6699515697157134785889779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4466343798104756523926519 6699515697157134785889779)
          ·
            refine ⟨10049273545735702178834669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6699515697157134785889779 10049273545735702178834669)
            ·
              refine ⟨3768477579650888317063001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10049273545735702178834669 3768477579650888317063001)
              ·
                refine ⟨2826358184738166237797251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3768477579650888317063001 2826358184738166237797251)
                ·
                  refine ⟨4239537277107249356695877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2826358184738166237797251 4239537277107249356695877)
                  ·
                    refine ⟨794913239457609254380477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4239537277107249356695877 794913239457609254380477)
                    ·
                      rfl

theorem cell22_2322132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_2322132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322132 prefixEnd_2322132 := by exact prefixLift 2322132
  have htrace : WordTrace (prefixWord ++ tailWord_2322132) baseStart_2322132 baseEnd_2322132 := by
    simpa [prefixWord, tailWord_2322132, baseEnd_2322132] using wordTrace_append hprefix tailTrace_2322132
  have hstable : (prefixWord ++ tailWord_2322132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322132).length < 2 ^ (prefixWord ++ tailWord_2322132).sum := by decide
  have hdescent : baseEnd_2322132 < baseStart_2322132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322145 : List Nat := [1, 2, 3, 1, 5, 1, 1, 2, 1, 5]
def baseStart_2322145 : Nat := 118140960795 + 2322145 * 2 ^ 59
def prefixEnd_2322145 : Nat := 4983230072969 + 3 ^ 40 * 2322145 * 2
def baseEnd_2322145 : Nat := 794917689623281553805437

theorem tailTrace_2322145 : CollatzResearch.WordTrace tailWord_2322145 prefixEnd_2322145 794917689623281553805437 := by
  unfold tailWord_2322145
  simp only [CollatzResearch.WordTrace]
  refine ⟨84695586172272730636903889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56463724114848487091269259 84695586172272730636903889)
  ·
    refine ⟨63521689629204547977677917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84695586172272730636903889 63521689629204547977677917)
    ·
      refine ⟨23820633610951705491629219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63521689629204547977677917 23820633610951705491629219)
      ·
        refine ⟨35730950416427558237443829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23820633610951705491629219 35730950416427558237443829)
        ·
          refine ⟨3349776601540083584760359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35730950416427558237443829 3349776601540083584760359)
          ·
            refine ⟨5024664902310125377140539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3349776601540083584760359 5024664902310125377140539)
            ·
              refine ⟨7536997353465188065710809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5024664902310125377140539 7536997353465188065710809)
              ·
                refine ⟨5652748015098891049283107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7536997353465188065710809 5652748015098891049283107)
                ·
                  refine ⟨8479122022648336573924661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5652748015098891049283107 8479122022648336573924661)
                  ·
                    refine ⟨794917689623281553805437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8479122022648336573924661 794917689623281553805437)
                    ·
                      rfl

theorem cell22_2322145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_2322145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322145 prefixEnd_2322145 := by exact prefixLift 2322145
  have htrace : WordTrace (prefixWord ++ tailWord_2322145) baseStart_2322145 baseEnd_2322145 := by
    simpa [prefixWord, tailWord_2322145, baseEnd_2322145] using wordTrace_append hprefix tailTrace_2322145
  have hstable : (prefixWord ++ tailWord_2322145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322145).length < 2 ^ (prefixWord ++ tailWord_2322145).sum := by decide
  have hdescent : baseEnd_2322145 < baseStart_2322145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322162 : List Nat := [3, 2, 1, 3, 1, 1, 4, 2, 2, 3]
def baseStart_2322162 : Nat := 118140960795 + 2322162 * 2 ^ 59
def prefixEnd_2322162 : Nat := 4983230072969 + 3 ^ 40 * 2322162 * 2
def baseEnd_2322162 : Nat := 794923509070699176130385

theorem tailTrace_2322162 : CollatzResearch.WordTrace tailWord_2322162 prefixEnd_2322162 794923509070699176130385 := by
  unfold tailWord_2322162
  simp only [CollatzResearch.WordTrace]
  refine ⟨21174051553302785635068185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56464137475474095026848493 21174051553302785635068185)
  ·
    refine ⟨15880538664977089226301139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21174051553302785635068185 15880538664977089226301139)
    ·
      refine ⟨23820807997465633839451709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15880538664977089226301139 23820807997465633839451709)
      ·
        refine ⟨8932802999049612689794391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23820807997465633839451709 8932802999049612689794391)
        ·
          refine ⟨13399204498574419034691587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8932802999049612689794391 13399204498574419034691587)
          ·
            refine ⟨20098806747861628552037381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13399204498574419034691587 20098806747861628552037381)
            ·
              refine ⟨3768526265224055353507009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20098806747861628552037381 3768526265224055353507009)
              ·
                refine ⟨2826394698918041515130257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3768526265224055353507009 2826394698918041515130257)
                ·
                  refine ⟨2119796024188531136347693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2826394698918041515130257 2119796024188531136347693)
                  ·
                    refine ⟨794923509070699176130385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2119796024188531136347693 794923509070699176130385)
                    ·
                      rfl

theorem cell22_2322162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_2322162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322162 prefixEnd_2322162 := by exact prefixLift 2322162
  have htrace : WordTrace (prefixWord ++ tailWord_2322162) baseStart_2322162 baseEnd_2322162 := by
    simpa [prefixWord, tailWord_2322162, baseEnd_2322162] using wordTrace_append hprefix tailTrace_2322162
  have hstable : (prefixWord ++ tailWord_2322162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322162).length < 2 ^ (prefixWord ++ tailWord_2322162).sum := by decide
  have hdescent : baseEnd_2322162 < baseStart_2322162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322190 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 5, 3]
def baseStart_2322190 : Nat := 118140960795 + 2322190 * 2 ^ 59
def prefixEnd_2322190 : Nat := 4983230072969 + 3 ^ 40 * 2322190 * 2
def baseEnd_2322190 : Nat := 794933094042916436430299

theorem tailTrace_2322190 : CollatzResearch.WordTrace tailWord_2322190 prefixEnd_2322190 794933094042916436430299 := by
  unfold tailWord_2322190
  simp only [CollatzResearch.WordTrace]
  refine ⟨10587153432138712915286503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56464818304739802214861349 10587153432138712915286503)
  ·
    refine ⟨15880730148208069372929755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10587153432138712915286503 15880730148208069372929755)
    ·
      refine ⟨23821095222312104059394633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15880730148208069372929755 23821095222312104059394633)
      ·
        refine ⟨17865821416734078044545975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23821095222312104059394633 17865821416734078044545975)
        ·
          refine ⟨26798732125101117066818963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17865821416734078044545975 26798732125101117066818963)
          ·
            refine ⟨40198098187651675600228445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26798732125101117066818963 40198098187651675600228445)
            ·
              refine ⟨15074286820369378350085667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40198098187651675600228445 15074286820369378350085667)
              ·
                refine ⟨22611430230554067525128501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15074286820369378350085667 22611430230554067525128501)
                ·
                  refine ⟨2119821584114443830480797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22611430230554067525128501 2119821584114443830480797)
                  ·
                    refine ⟨794933094042916436430299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2119821584114443830480797 794933094042916436430299)
                    ·
                      rfl

theorem cell22_2322190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_2322190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322190 prefixEnd_2322190 := by exact prefixLift 2322190
  have htrace : WordTrace (prefixWord ++ tailWord_2322190) baseStart_2322190 baseEnd_2322190 := by
    simpa [prefixWord, tailWord_2322190, baseEnd_2322190] using wordTrace_append hprefix tailTrace_2322190
  have hstable : (prefixWord ++ tailWord_2322190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322190).length < 2 ^ (prefixWord ++ tailWord_2322190).sum := by decide
  have hdescent : baseEnd_2322190 < baseStart_2322190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322194 : List Nat := [3, 2, 4, 1, 1, 3, 1, 1, 2, 4]
def baseStart_2322194 : Nat := 118140960795 + 2322194 * 2 ^ 59
def prefixEnd_2322194 : Nat := 4983230072969 + 3 ^ 40 * 2322194 * 2
def baseEnd_2322194 : Nat := 794934463324661759330287

theorem tailTrace_2322194 : CollatzResearch.WordTrace tailWord_2322194 prefixEnd_2322194 794934463324661759330287 := by
  unfold tailWord_2322194
  simp only [CollatzResearch.WordTrace]
  refine ⟨21174343337273803001359409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56464915566063474670291757 21174343337273803001359409)
  ·
    refine ⟨15880757502955352251019557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21174343337273803001359409 15880757502955352251019557)
    ·
      refine ⟨2977642031804128547066167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15880757502955352251019557 2977642031804128547066167)
      ·
        refine ⟨4466463047706192820599251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2977642031804128547066167 4466463047706192820599251)
        ·
          refine ⟨6699694571559289230898877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4466463047706192820599251 6699694571559289230898877)
          ·
            refine ⟨2512385464334733461587079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6699694571559289230898877 2512385464334733461587079)
            ·
              refine ⟨3768578196502100192380619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2512385464334733461587079 3768578196502100192380619)
              ·
                refine ⟨5652867294753150288570929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3768578196502100192380619 5652867294753150288570929)
                ·
                  refine ⟨4239650471064862716428197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5652867294753150288570929 4239650471064862716428197)
                  ·
                    refine ⟨794934463324661759330287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4239650471064862716428197 794934463324661759330287)
                    ·
                      rfl

theorem cell22_2322194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_2322194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322194 prefixEnd_2322194 := by exact prefixLift 2322194
  have htrace : WordTrace (prefixWord ++ tailWord_2322194) baseStart_2322194 baseEnd_2322194 := by
    simpa [prefixWord, tailWord_2322194, baseEnd_2322194] using wordTrace_append hprefix tailTrace_2322194
  have hstable : (prefixWord ++ tailWord_2322194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322194).length < 2 ^ (prefixWord ++ tailWord_2322194).sum := by decide
  have hdescent : baseEnd_2322194 < baseStart_2322194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322220 : List Nat := [2, 2, 1, 1, 1, 5, 3, 2, 5]
def baseStart_2322220 : Nat := 118140960795 + 2322220 * 2 ^ 59
def prefixEnd_2322220 : Nat := 4983230072969 + 3 ^ 40 * 2322220 * 2
def baseEnd_2322220 : Nat := 264981121218668786060069

theorem tailTrace_2322220 : CollatzResearch.WordTrace tailWord_2322220 prefixEnd_2322220 264981121218668786060069 := by
  unfold tailWord_2322220
  simp only [CollatzResearch.WordTrace]
  refine ⟨42349160823500509222942057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56465547764667345630589409 42349160823500509222942057)
  ·
    refine ⟨31761870617625381917206543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42349160823500509222942057 31761870617625381917206543)
    ·
      refine ⟨47642805926438072875809815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31761870617625381917206543 47642805926438072875809815)
      ·
        refine ⟨71464208889657109313714723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47642805926438072875809815 71464208889657109313714723)
        ·
          refine ⟨107196313334485663970572085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71464208889657109313714723 107196313334485663970572085)
          ·
            refine ⟨10049654375108030997241133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107196313334485663970572085 10049654375108030997241133)
            ·
              refine ⟨3768620390665511623965425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10049654375108030997241133 3768620390665511623965425)
              ·
                refine ⟨2826465292999133717974069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3768620390665511623965425 2826465292999133717974069)
                ·
                  refine ⟨264981121218668786060069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2826465292999133717974069 264981121218668786060069)
                  ·
                    rfl

theorem cell22_2322220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_2322220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322220 prefixEnd_2322220 := by exact prefixLift 2322220
  have htrace : WordTrace (prefixWord ++ tailWord_2322220) baseStart_2322220 baseEnd_2322220 := by
    simpa [prefixWord, tailWord_2322220, baseEnd_2322220] using wordTrace_append hprefix tailTrace_2322220
  have hstable : (prefixWord ++ tailWord_2322220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322220).length < 2 ^ (prefixWord ++ tailWord_2322220).sum := by decide
  have hdescent : baseEnd_2322220 < baseStart_2322220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322297 : List Nat := [1, 2, 1, 3, 2, 2, 3, 3, 2, 3]
def baseStart_2322297 : Nat := 118140960795 + 2322297 * 2 ^ 59
def prefixEnd_2322297 : Nat := 4983230072969 + 3 ^ 40 * 2322297 * 2
def baseEnd_2322297 : Nat := 794969722329603824004971

theorem tailTrace_2322297 : CollatzResearch.WordTrace tailWord_2322297 prefixEnd_2322297 794969722329603824004971 := by
  unfold tailWord_2322297
  simp only [CollatzResearch.WordTrace]
  refine ⟨84701130067722060596437145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56467420045148040397624763 84701130067722060596437145)
  ·
    refine ⟨63525847550791545447327859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84701130067722060596437145 63525847550791545447327859)
    ·
      refine ⟨95288771326187318170991789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63525847550791545447327859 95288771326187318170991789)
      ·
        refine ⟨35733289247320244314121921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95288771326187318170991789 35733289247320244314121921)
        ·
          refine ⟨26799966935490183235591441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35733289247320244314121921 26799966935490183235591441)
          ·
            refine ⟨20099975201617637426693581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26799966935490183235591441 20099975201617637426693581)
            ·
              refine ⟨7537490700606614035010093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20099975201617637426693581 7537490700606614035010093)
              ·
                refine ⟨2826559012727480263128785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7537490700606614035010093 2826559012727480263128785)
                ·
                  refine ⟨2119919259545610197346589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2826559012727480263128785 2119919259545610197346589)
                  ·
                    refine ⟨794969722329603824004971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2119919259545610197346589 794969722329603824004971)
                    ·
                      rfl

theorem cell22_2322297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 3].length) (baseStart_2322297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322297 prefixEnd_2322297 := by exact prefixLift 2322297
  have htrace : WordTrace (prefixWord ++ tailWord_2322297) baseStart_2322297 baseEnd_2322297 := by
    simpa [prefixWord, tailWord_2322297, baseEnd_2322297] using wordTrace_append hprefix tailTrace_2322297
  have hstable : (prefixWord ++ tailWord_2322297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322297).length < 2 ^ (prefixWord ++ tailWord_2322297).sum := by decide
  have hdescent : baseEnd_2322297 < baseStart_2322297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322340 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_2322340 : Nat := 118140960795 + 2322340 * 2 ^ 59
def prefixEnd_2322340 : Nat := 4983230072969 + 3 ^ 40 * 2322340 * 2
def baseEnd_2322340 : Nat := 794984442108366045179839

theorem tailTrace_2322340 : CollatzResearch.WordTrace tailWord_2322340 prefixEnd_2322340 794984442108366045179839 := by
  unfold tailWord_2322340
  simp only [CollatzResearch.WordTrace]
  refine ⟨42351349203283139470126237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56468465604377519293501649 42351349203283139470126237)
  ·
    refine ⟨15881755951231177301297339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42351349203283139470126237 15881755951231177301297339)
    ·
      refine ⟨23822633926846765951946009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15881755951231177301297339 23822633926846765951946009)
      ·
        refine ⟨17866975445135074463959507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23822633926846765951946009 17866975445135074463959507)
        ·
          refine ⟨26800463167702611695939261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17866975445135074463959507 26800463167702611695939261)
          ·
            refine ⟨10050173687888479385977223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26800463167702611695939261 10050173687888479385977223)
            ·
              refine ⟨15075260531832719078965835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10050173687888479385977223 15075260531832719078965835)
              ·
                refine ⟨22612890797749078618448753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15075260531832719078965835 22612890797749078618448753)
                ·
                  refine ⟨16959668098311808963836565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22612890797749078618448753 16959668098311808963836565)
                  ·
                    refine ⟨794984442108366045179839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16959668098311808963836565 794984442108366045179839)
                    ·
                      rfl

theorem cell22_2322340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_2322340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322340 prefixEnd_2322340 := by exact prefixLift 2322340
  have htrace : WordTrace (prefixWord ++ tailWord_2322340) baseStart_2322340 baseEnd_2322340 := by
    simpa [prefixWord, tailWord_2322340, baseEnd_2322340] using wordTrace_append hprefix tailTrace_2322340
  have hstable : (prefixWord ++ tailWord_2322340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322340).length < 2 ^ (prefixWord ++ tailWord_2322340).sum := by decide
  have hdescent : baseEnd_2322340 < baseStart_2322340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322355 : List Nat := [1, 1, 1, 2, 3, 1, 3, 5, 5]
def baseStart_2322355 : Nat := 118140960795 + 2322355 * 2 ^ 59
def prefixEnd_2322355 : Nat := 4983230072969 + 3 ^ 40 * 2322355 * 2
def baseEnd_2322355 : Nat := 264996525638303668684931

theorem tailTrace_2322355 : CollatzResearch.WordTrace tailWord_2322355 prefixEnd_2322355 264996525638303668684931 := by
  unfold tailWord_2322355
  simp only [CollatzResearch.WordTrace]
  refine ⟨84703245501511936502048519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56468830334341291001365679 84703245501511936502048519)
  ·
    refine ⟨127054868252267904753072779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84703245501511936502048519 127054868252267904753072779)
    ·
      refine ⟨190582302378401857129609169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127054868252267904753072779 190582302378401857129609169)
      ·
        refine ⟨142936726783801392847206877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190582302378401857129609169 142936726783801392847206877)
        ·
          refine ⟨53601272543925522317702579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142936726783801392847206877 53601272543925522317702579)
          ·
            refine ⟨80401908815888283476553869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53601272543925522317702579 80401908815888283476553869)
            ·
              refine ⟨30150715805958106303707701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80401908815888283476553869 30150715805958106303707701)
              ·
                refine ⟨2826629606808572465972597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30150715805958106303707701 2826629606808572465972597)
                ·
                  refine ⟨264996525638303668684931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2826629606808572465972597 264996525638303668684931)
                  ·
                    rfl

theorem cell22_2322355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 5].length) (baseStart_2322355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322355 prefixEnd_2322355 := by exact prefixLift 2322355
  have htrace : WordTrace (prefixWord ++ tailWord_2322355) baseStart_2322355 baseEnd_2322355 := by
    simpa [prefixWord, tailWord_2322355, baseEnd_2322355] using wordTrace_append hprefix tailTrace_2322355
  have hstable : (prefixWord ++ tailWord_2322355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322355).length < 2 ^ (prefixWord ++ tailWord_2322355).sum := by decide
  have hdescent : baseEnd_2322355 < baseStart_2322355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322376 : List Nat := [2, 1, 3, 1, 4, 2, 2, 3, 1, 3]
def baseStart_2322376 : Nat := 118140960795 + 2322376 * 2 ^ 59
def prefixEnd_2322376 : Nat := 4983230072969 + 3 ^ 40 * 2322376 * 2
def baseEnd_2322376 : Nat := 794996765644073951279729

theorem tailTrace_2322376 : CollatzResearch.WordTrace tailWord_2322376 prefixEnd_2322376 794996765644073951279729 := by
  unfold tailWord_2322376
  simp only [CollatzResearch.WordTrace]
  refine ⟨42352005717217928544281491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56469340956290571392375321 42352005717217928544281491)
  ·
    refine ⟨63528008575826892816422237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42352005717217928544281491 63528008575826892816422237)
    ·
      refine ⟨23823003215935084806158339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63528008575826892816422237 23823003215935084806158339)
      ·
        refine ⟨35734504823902627209237509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23823003215935084806158339 35734504823902627209237509)
        ·
          refine ⟨6700219654481742601732033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35734504823902627209237509 6700219654481742601732033)
          ·
            refine ⟨5025164740861306951299025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6700219654481742601732033 5025164740861306951299025)
            ·
              refine ⟨3768873555645980213474269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5025164740861306951299025 3768873555645980213474269)
              ·
                refine ⟨1413327583367242580052851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3768873555645980213474269 1413327583367242580052851)
                ·
                  refine ⟨2119991375050863870079277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1413327583367242580052851 2119991375050863870079277)
                  ·
                    refine ⟨794996765644073951279729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2119991375050863870079277 794996765644073951279729)
                    ·
                      rfl

theorem cell22_2322376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_2322376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322376 prefixEnd_2322376 := by exact prefixLift 2322376
  have htrace : WordTrace (prefixWord ++ tailWord_2322376) baseStart_2322376 baseEnd_2322376 := by
    simpa [prefixWord, tailWord_2322376, baseEnd_2322376] using wordTrace_append hprefix tailTrace_2322376
  have hstable : (prefixWord ++ tailWord_2322376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322376).length < 2 ^ (prefixWord ++ tailWord_2322376).sum := by decide
  have hdescent : baseEnd_2322376 < baseStart_2322376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322385 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 5, 4]
def baseStart_2322385 : Nat := 118140960795 + 2322385 * 2 ^ 59
def prefixEnd_2322385 : Nat := 4983230072969 + 3 ^ 40 * 2322385 * 2
def baseEnd_2322385 : Nat := 794999846528000927804701

theorem tailTrace_2322385 : CollatzResearch.WordTrace tailWord_2322385 prefixEnd_2322385 794999846528000927804701 := by
  unfold tailWord_2322385
  simp only [CollatzResearch.WordTrace]
  refine ⟨84704339691403251625640609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56469559794268834417093739 84704339691403251625640609)
  ·
    refine ⟨63528254768552438719230457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84704339691403251625640609 63528254768552438719230457)
    ·
      refine ⟨47646191076414329039422843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63528254768552438719230457 47646191076414329039422843)
      ·
        refine ⟨71469286614621493559134265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47646191076414329039422843 71469286614621493559134265)
        ·
          refine ⟨53601964960966120169350699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71469286614621493559134265 53601964960966120169350699)
          ·
            refine ⟨80402947441449180254026049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53601964960966120169350699 80402947441449180254026049)
            ·
              refine ⟨60302210581086885190519537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80402947441449180254026049 60302210581086885190519537)
              ·
                refine ⟨45226657935815163892889653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60302210581086885190519537 45226657935815163892889653)
                ·
                  refine ⟨4239999181482671614958405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45226657935815163892889653 4239999181482671614958405)
                  ·
                    refine ⟨794999846528000927804701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4239999181482671614958405 794999846528000927804701)
                    ·
                      rfl

theorem cell22_2322385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_2322385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322385 prefixEnd_2322385 := by exact prefixLift 2322385
  have htrace : WordTrace (prefixWord ++ tailWord_2322385) baseStart_2322385 baseEnd_2322385 := by
    simpa [prefixWord, tailWord_2322385, baseEnd_2322385] using wordTrace_append hprefix tailTrace_2322385
  have hstable : (prefixWord ++ tailWord_2322385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322385).length < 2 ^ (prefixWord ++ tailWord_2322385).sum := by decide
  have hdescent : baseEnd_2322385 < baseStart_2322385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322389 : List Nat := [1, 3, 2, 3, 2, 3, 1, 2, 5]
def baseStart_2322389 : Nat := 118140960795 + 2322389 * 2 ^ 59
def prefixEnd_2322389 : Nat := 4983230072969 + 3 ^ 40 * 2322389 * 2
def baseEnd_2322389 : Nat := 265000405269915416901563

theorem tailTrace_2322389 : CollatzResearch.WordTrace tailWord_2322389 prefixEnd_2322389 265000405269915416901563 := by
  unfold tailWord_2322389
  simp only [CollatzResearch.WordTrace]
  refine ⟨84704485583388760308786221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56469657055592506872524147 84704485583388760308786221)
  ·
    refine ⟨31764182093770785115794833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84704485583388760308786221 31764182093770785115794833)
    ·
      refine ⟨23823136570328088836846125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31764182093770785115794833 23823136570328088836846125)
      ·
        refine ⟨8933676213873033313817297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23823136570328088836846125 8933676213873033313817297)
        ·
          refine ⟨6700257160404774985362973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8933676213873033313817297 6700257160404774985362973)
          ·
            refine ⟨2512596435151790619511115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6700257160404774985362973 2512596435151790619511115)
            ·
              refine ⟨3768894652727685929266673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2512596435151790619511115 3768894652727685929266673)
              ·
                refine ⟨2826670989545764446950005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3768894652727685929266673 2826670989545764446950005)
                ·
                  refine ⟨265000405269915416901563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2826670989545764446950005 265000405269915416901563)
                  ·
                    rfl

theorem cell22_2322389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_2322389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322389 prefixEnd_2322389 := by exact prefixLift 2322389
  have htrace : WordTrace (prefixWord ++ tailWord_2322389) baseStart_2322389 baseEnd_2322389 := by
    simpa [prefixWord, tailWord_2322389, baseEnd_2322389] using wordTrace_append hprefix tailTrace_2322389
  have hstable : (prefixWord ++ tailWord_2322389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322389).length < 2 ^ (prefixWord ++ tailWord_2322389).sum := by decide
  have hdescent : baseEnd_2322389 < baseStart_2322389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322475 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 4, 6]
def baseStart_2322475 : Nat := 118140960795 + 2322475 * 2 ^ 59
def prefixEnd_2322475 : Nat := 4983230072969 + 3 ^ 40 * 2322475 * 2
def baseEnd_2322475 : Nat := 795030655367270693054425

theorem tailTrace_2322475 : CollatzResearch.WordTrace tailWord_2322475 prefixEnd_2322475 795030655367270693054425 := by
  unfold tailWord_2322475
  simp only [CollatzResearch.WordTrace]
  refine ⟨84707622261077196996416879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56471748174051464664277919 84707622261077196996416879)
  ·
    refine ⟨127061433391615795494625319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84707622261077196996416879 127061433391615795494625319)
    ·
      refine ⟨190592150087423693241937979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127061433391615795494625319 190592150087423693241937979)
      ·
        refine ⟨285888225131135539862906969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190592150087423693241937979 285888225131135539862906969)
        ·
          refine ⟨214416168848351654897180227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285888225131135539862906969 214416168848351654897180227)
          ·
            refine ⟨321624253272527482345770341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214416168848351654897180227 321624253272527482345770341)
            ·
              refine ⟨60304547488598902939831939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 321624253272527482345770341 60304547488598902939831939)
              ·
                refine ⟨90456821232898354409747909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60304547488598902939831939 90456821232898354409747909)
                ·
                  refine ⟨16960653981168441451827733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90456821232898354409747909 16960653981168441451827733)
                  ·
                    refine ⟨795030655367270693054425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16960653981168441451827733 795030655367270693054425)
                    ·
                      rfl

theorem cell22_2322475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 6].length) (baseStart_2322475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322475 prefixEnd_2322475 := by exact prefixLift 2322475
  have htrace : WordTrace (prefixWord ++ tailWord_2322475) baseStart_2322475 baseEnd_2322475 := by
    simpa [prefixWord, tailWord_2322475, baseEnd_2322475] using wordTrace_append hprefix tailTrace_2322475
  have hstable : (prefixWord ++ tailWord_2322475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322475).length < 2 ^ (prefixWord ++ tailWord_2322475).sum := by decide
  have hdescent : baseEnd_2322475 < baseStart_2322475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322522 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 2, 5]
def baseStart_2322522 : Nat := 118140960795 + 2322522 * 2 ^ 59
def prefixEnd_2322522 : Nat := 4983230072969 + 3 ^ 40 * 2322522 * 2
def baseEnd_2322522 : Nat := 795046744427778237129281

theorem tailTrace_2322522 : CollatzResearch.WordTrace tailWord_2322522 prefixEnd_2322522 795046744427778237129281 := by
  unfold tailWord_2322522
  simp only [CollatzResearch.WordTrace]
  refine ⟨21177334122976731005844455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56472890994604616015585213 21177334122976731005844455)
  ·
    refine ⟨31766001184465096508766683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21177334122976731005844455 31766001184465096508766683)
    ·
      refine ⟨47649001776697644763150025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31766001184465096508766683 47649001776697644763150025)
      ·
        refine ⟨35736751332523233572362519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47649001776697644763150025 35736751332523233572362519)
        ·
          refine ⟨53605126998784850358543779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35736751332523233572362519 53605126998784850358543779)
          ·
            refine ⟨80407690498177275537815669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53605126998784850358543779 80407690498177275537815669)
            ·
              refine ⟨7538220984204119581670219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80407690498177275537815669 7538220984204119581670219)
              ·
                refine ⟨11307331476306179372505329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7538220984204119581670219 11307331476306179372505329)
                ·
                  refine ⟨8480498607229634529378997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11307331476306179372505329 8480498607229634529378997)
                  ·
                    refine ⟨795046744427778237129281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8480498607229634529378997 795046744427778237129281)
                    ·
                      rfl

theorem cell22_2322522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_2322522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322522 prefixEnd_2322522 := by exact prefixLift 2322522
  have htrace : WordTrace (prefixWord ++ tailWord_2322522) baseStart_2322522 baseEnd_2322522 := by
    simpa [prefixWord, tailWord_2322522, baseEnd_2322522] using wordTrace_append hprefix tailTrace_2322522
  have hstable : (prefixWord ++ tailWord_2322522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322522).length < 2 ^ (prefixWord ++ tailWord_2322522).sum := by decide
  have hdescent : baseEnd_2322522 < baseStart_2322522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322524 : List Nat := [2, 2, 4, 1, 1, 2, 2, 3, 5]
def baseStart_2322524 : Nat := 118140960795 + 2322524 * 2 ^ 59
def prefixEnd_2322524 : Nat := 4983230072969 + 3 ^ 40 * 2322524 * 2
def baseEnd_2322524 : Nat := 265015809689550299526425

theorem tailTrace_2322524 : CollatzResearch.WordTrace tailWord_2322524 prefixEnd_2322524 265015809689550299526425 := by
  unfold tailWord_2322524
  simp only [CollatzResearch.WordTrace]
  refine ⟨42354704718949839182475313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56472939625266452243300417 42354704718949839182475313)
  ·
    refine ⟨31766028539212379386856485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42354704718949839182475313 31766028539212379386856485)
    ·
      refine ⟨5956130351102321135035591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31766028539212379386856485 5956130351102321135035591)
      ·
        refine ⟨8934195526653481702553387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5956130351102321135035591 8934195526653481702553387)
        ·
          refine ⟨13401293289980222553830081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8934195526653481702553387 13401293289980222553830081)
          ·
            refine ⟨10050969967485166915372561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13401293289980222553830081 10050969967485166915372561)
            ·
              refine ⟨7538227475613875186529421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10050969967485166915372561 7538227475613875186529421)
              ·
                refine ⟨2826835303355203194948533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7538227475613875186529421 2826835303355203194948533)
                ·
                  refine ⟨265015809689550299526425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2826835303355203194948533 265015809689550299526425)
                  ·
                    rfl

theorem cell22_2322524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_2322524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322524 prefixEnd_2322524 := by exact prefixLift 2322524
  have htrace : WordTrace (prefixWord ++ tailWord_2322524) baseStart_2322524 baseEnd_2322524 := by
    simpa [prefixWord, tailWord_2322524, baseEnd_2322524] using wordTrace_append hprefix tailTrace_2322524
  have hstable : (prefixWord ++ tailWord_2322524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322524).length < 2 ^ (prefixWord ++ tailWord_2322524).sum := by decide
  have hdescent : baseEnd_2322524 < baseStart_2322524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322537 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 3, 4]
def baseStart_2322537 : Nat := 118140960795 + 2322537 * 2 ^ 59
def prefixEnd_2322537 : Nat := 4983230072969 + 3 ^ 40 * 2322537 * 2
def baseEnd_2322537 : Nat := 795051879234323198004235

theorem tailTrace_2322537 : CollatzResearch.WordTrace tailWord_2322537 prefixEnd_2322537 795051879234323198004235 := by
  unfold tailWord_2322537
  simp only [CollatzResearch.WordTrace]
  refine ⟨84709883586852581585173865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56473255724568387723449243 84709883586852581585173865)
  ·
    refine ⟨63532412690139436188880399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84709883586852581585173865 63532412690139436188880399)
    ·
      refine ⟨95298619035209154283320599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63532412690139436188880399 95298619035209154283320599)
      ·
        refine ⟨142947928552813731424980899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95298619035209154283320599 142947928552813731424980899)
        ·
          refine ⟨214421892829220597137471349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142947928552813731424980899 214421892829220597137471349)
          ·
            refine ⟨20102052452739430981637939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 214421892829220597137471349 20102052452739430981637939)
            ·
              refine ⟨30153078679109146472456909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20102052452739430981637939 30153078679109146472456909)
              ·
                refine ⟨11307404504665929927171341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30153078679109146472456909 11307404504665929927171341)
                ·
                  refine ⟨4240276689249723722689253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11307404504665929927171341 4240276689249723722689253)
                  ·
                    refine ⟨795051879234323198004235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4240276689249723722689253 795051879234323198004235)
                    ·
                      rfl

theorem cell22_2322537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 4].length) (baseStart_2322537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322537 prefixEnd_2322537 := by exact prefixLift 2322537
  have htrace : WordTrace (prefixWord ++ tailWord_2322537) baseStart_2322537 baseEnd_2322537 := by
    simpa [prefixWord, tailWord_2322537, baseEnd_2322537] using wordTrace_append hprefix tailTrace_2322537
  have hstable : (prefixWord ++ tailWord_2322537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322537).length < 2 ^ (prefixWord ++ tailWord_2322537).sum := by decide
  have hdescent : baseEnd_2322537 < baseStart_2322537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322567 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 3, 5]
def baseStart_2322567 : Nat := 118140960795 + 2322567 * 2 ^ 59
def prefixEnd_2322567 : Nat := 4983230072969 + 3 ^ 40 * 2322567 * 2
def baseEnd_2322567 : Nat := 795062148847413119754143

theorem tailTrace_2322567 : CollatzResearch.WordTrace tailWord_2322567 prefixEnd_2322567 795062148847413119754143 := by
  unfold tailWord_2322567
  simp only [CollatzResearch.WordTrace]
  refine ⟨84710977776743896708765955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56473985184495931139177303 84710977776743896708765955)
  ·
    refine ⟨127066466665115845063148933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84710977776743896708765955 127066466665115845063148933)
    ·
      refine ⟨23824962499709220949340425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127066466665115845063148933 23824962499709220949340425)
      ·
        refine ⟨17868721874781915712005319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23824962499709220949340425 17868721874781915712005319)
        ·
          refine ⟨26803082812172873568007979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17868721874781915712005319 26803082812172873568007979)
          ·
            refine ⟨40204624218259310352011969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26803082812172873568007979 40204624218259310352011969)
            ·
              refine ⟨30153468163694482764008977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40204624218259310352011969 30153468163694482764008977)
              ·
                refine ⟨22615101122770862073006733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30153468163694482764008977 22615101122770862073006733)
                ·
                  refine ⟨8480662921039073277377525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22615101122770862073006733 8480662921039073277377525)
                  ·
                    refine ⟨795062148847413119754143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8480662921039073277377525 795062148847413119754143)
                    ·
                      rfl

theorem cell22_2322567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_2322567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322567 prefixEnd_2322567 := by exact prefixLift 2322567
  have htrace : WordTrace (prefixWord ++ tailWord_2322567) baseStart_2322567 baseEnd_2322567 := by
    simpa [prefixWord, tailWord_2322567, baseEnd_2322567] using wordTrace_append hprefix tailTrace_2322567
  have hstable : (prefixWord ++ tailWord_2322567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322567).length < 2 ^ (prefixWord ++ tailWord_2322567).sum := by decide
  have hdescent : baseEnd_2322567 < baseStart_2322567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322569 : List Nat := [1, 2, 1, 1, 4, 2, 1, 6, 4]
def baseStart_2322569 : Nat := 118140960795 + 2322569 * 2 ^ 59
def prefixEnd_2322569 : Nat := 4983230072969 + 3 ^ 40 * 2322569 * 2
def baseEnd_2322569 : Nat := 265020944496095260401379

theorem tailTrace_2322569 : CollatzResearch.WordTrace tailWord_2322569 prefixEnd_2322569 265020944496095260401379 := by
  unfold tailWord_2322569
  simp only [CollatzResearch.WordTrace]
  refine ⟨84711050722736651050338761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56474033815157767366892507 84711050722736651050338761)
  ·
    refine ⟨63533288042052488287754071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84711050722736651050338761 63533288042052488287754071)
    ·
      refine ⟨95299932063078732431631107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63533288042052488287754071 95299932063078732431631107)
      ·
        refine ⟨142949898094618098647446661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95299932063078732431631107 142949898094618098647446661)
        ·
          refine ⟨26803105892740893496396249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142949898094618098647446661 26803105892740893496396249)
          ·
            refine ⟨20102329419555670122297187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26803105892740893496396249 20102329419555670122297187)
            ·
              refine ⟨30153494129333505183445781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20102329419555670122297187 30153494129333505183445781)
              ·
                refine ⟨1413445037312508055474021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30153494129333505183445781 1413445037312508055474021)
                ·
                  refine ⟨265020944496095260401379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1413445037312508055474021 265020944496095260401379)
                  ·
                    rfl

theorem cell22_2322569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 4].length) (baseStart_2322569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322569 prefixEnd_2322569 := by exact prefixLift 2322569
  have htrace : WordTrace (prefixWord ++ tailWord_2322569) baseStart_2322569 baseEnd_2322569 := by
    simpa [prefixWord, tailWord_2322569, baseEnd_2322569] using wordTrace_append hprefix tailTrace_2322569
  have hstable : (prefixWord ++ tailWord_2322569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322569).length < 2 ^ (prefixWord ++ tailWord_2322569).sum := by decide
  have hdescent : baseEnd_2322569 < baseStart_2322569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322597 : List Nat := [1, 3, 1, 2, 1, 3, 3, 8]
def baseStart_2322597 : Nat := 118140960795 + 2322597 * 2 ^ 59
def prefixEnd_2322597 : Nat := 4983230072969 + 3 ^ 40 * 2322597 * 2
def baseEnd_2322597 : Nat := 88341379828944782389339

theorem tailTrace_2322597 : CollatzResearch.WordTrace tailWord_2322597 prefixEnd_2322597 88341379828944782389339 := by
  unfold tailWord_2322597
  simp only [CollatzResearch.WordTrace]
  refine ⟨84712071966635211832358045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56474714644423474554905363 84712071966635211832358045)
  ·
    refine ⟨31767026987488204437134267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84712071966635211832358045 31767026987488204437134267)
    ·
      refine ⟨47650540481232306655701401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31767026987488204437134267 47650540481232306655701401)
      ·
        refine ⟨35737905360924229991776051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47650540481232306655701401 35737905360924229991776051)
        ·
          refine ⟨53606858041386344987664077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35737905360924229991776051 53606858041386344987664077)
          ·
            refine ⟨20102571765519879370374029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53606858041386344987664077 20102571765519879370374029)
            ·
              refine ⟨7538464412069954763890261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20102571765519879370374029 7538464412069954763890261)
              ·
                refine ⟨88341379828944782389339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7538464412069954763890261 88341379828944782389339)
                ·
                  rfl

theorem cell22_2322597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 8].length) (baseStart_2322597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322597 prefixEnd_2322597 := by exact prefixLift 2322597
  have htrace : WordTrace (prefixWord ++ tailWord_2322597) baseStart_2322597 baseEnd_2322597 := by
    simpa [prefixWord, tailWord_2322597, baseEnd_2322597] using wordTrace_append hprefix tailTrace_2322597
  have hstable : (prefixWord ++ tailWord_2322597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322597).length < 2 ^ (prefixWord ++ tailWord_2322597).sum := by decide
  have hdescent : baseEnd_2322597 < baseStart_2322597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322689 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 5, 4]
def baseStart_2322689 : Nat := 118140960795 + 2322689 * 2 ^ 59
def prefixEnd_2322689 : Nat := 4983230072969 + 3 ^ 40 * 2322689 * 2
def baseEnd_2322689 : Nat := 795103911940645468203769

theorem tailTrace_2322689 : CollatzResearch.WordTrace tailWord_2322689 prefixEnd_2322689 795103911940645468203769 := by
  unfold tailWord_2322689
  simp only [CollatzResearch.WordTrace]
  refine ⟨84715427482301911544707121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56476951654867941029804747 84715427482301911544707121)
  ·
    refine ⟨63536570611726433658530341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84715427482301911544707121 63536570611726433658530341)
    ·
      refine ⟨11913106989698706310974439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63536570611726433658530341 11913106989698706310974439)
      ·
        refine ⟨17869660484548059466461659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11913106989698706310974439 17869660484548059466461659)
        ·
          refine ⟨26804490726822089199692489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17869660484548059466461659 26804490726822089199692489)
          ·
            refine ⟨20103368045116566899769367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26804490726822089199692489 20103368045116566899769367)
            ·
              refine ⟨30155052067674850349654051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20103368045116566899769367 30155052067674850349654051)
              ·
                refine ⟨45232578101512275524481077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30155052067674850349654051 45232578101512275524481077)
                ·
                  refine ⟨4240554197016775830420101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45232578101512275524481077 4240554197016775830420101)
                  ·
                    refine ⟨795103911940645468203769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4240554197016775830420101 795103911940645468203769)
                    ·
                      rfl

theorem cell22_2322689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_2322689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322689 prefixEnd_2322689 := by exact prefixLift 2322689
  have htrace : WordTrace (prefixWord ++ tailWord_2322689) baseStart_2322689 baseEnd_2322689 := by
    simpa [prefixWord, tailWord_2322689, baseEnd_2322689] using wordTrace_append hprefix tailTrace_2322689
  have hstable : (prefixWord ++ tailWord_2322689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322689).length < 2 ^ (prefixWord ++ tailWord_2322689).sum := by decide
  have hdescent : baseEnd_2322689 < baseStart_2322689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322721 : List Nat := [1, 2, 3, 2, 1, 1, 3, 5, 4]
def baseStart_2322721 : Nat := 118140960795 + 2322721 * 2 ^ 59
def prefixEnd_2322721 : Nat := 4983230072969 + 3 ^ 40 * 2322721 * 2
def baseEnd_2322721 : Nat := 265038288731536017134557

theorem tailTrace_2322721 : CollatzResearch.WordTrace tailWord_2322721 prefixEnd_2322721 265038288731536017134557 := by
  unfold tailWord_2322721
  simp only [CollatzResearch.WordTrace]
  refine ⟨84716594618185981009872017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56477729745457320673248011 84716594618185981009872017)
  ·
    refine ⟨63537445963639485757404013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84716594618185981009872017 63537445963639485757404013)
    ·
      refine ⟨23826542236364807159026505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63537445963639485757404013 23826542236364807159026505)
      ·
        refine ⟨17869906677273605369269879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23826542236364807159026505 17869906677273605369269879)
        ·
          refine ⟨26804860015910408053904819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17869906677273605369269879 26804860015910408053904819)
          ·
            refine ⟨40207290023865612080857229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26804860015910408053904819 40207290023865612080857229)
            ·
              refine ⟨15077733758949604530321461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40207290023865612080857229 15077733758949604530321461)
              ·
                refine ⟨1413537539901525424717637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15077733758949604530321461 1413537539901525424717637)
                ·
                  refine ⟨265038288731536017134557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1413537539901525424717637 265038288731536017134557)
                  ·
                    rfl

theorem cell22_2322721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 4].length) (baseStart_2322721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322721 prefixEnd_2322721 := by exact prefixLift 2322721
  have htrace : WordTrace (prefixWord ++ tailWord_2322721) baseStart_2322721 baseEnd_2322721 := by
    simpa [prefixWord, tailWord_2322721, baseEnd_2322721] using wordTrace_append hprefix tailTrace_2322721
  have hstable : (prefixWord ++ tailWord_2322721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322721).length < 2 ^ (prefixWord ++ tailWord_2322721).sum := by decide
  have hdescent : baseEnd_2322721 < baseStart_2322721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322727 : List Nat := [1, 1, 8, 1, 1, 2, 1, 2, 5]
def baseStart_2322727 : Nat := 118140960795 + 2322727 * 2 ^ 59
def prefixEnd_2322727 : Nat := 4983230072969 + 3 ^ 40 * 2322727 * 2
def baseEnd_2322727 : Nat := 265038973372408678584551

theorem tailTrace_2322727 : CollatzResearch.WordTrace tailWord_2322727 prefixEnd_2322727 265038973372408678584551 := by
  unfold tailWord_2322727
  simp only [CollatzResearch.WordTrace]
  refine ⟨84716813456164244034590435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56477875637442829356393623 84716813456164244034590435)
  ·
    refine ⟨127075220184246366051885653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84716813456164244034590435 127075220184246366051885653)
    ·
      refine ⟨1489162736534137102170535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 127075220184246366051885653 1489162736534137102170535)
      ·
        refine ⟨2233744104801205653255803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1489162736534137102170535 2233744104801205653255803)
        ·
          refine ⟨3350616157201808479883705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2233744104801205653255803 3350616157201808479883705)
          ·
            refine ⟨2512962117901356359912779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3350616157201808479883705 2512962117901356359912779)
            ·
              refine ⟨3769443176852034539869169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2512962117901356359912779 3769443176852034539869169)
              ·
                refine ⟨2827082382639025904901877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3769443176852034539869169 2827082382639025904901877)
                ·
                  refine ⟨265038973372408678584551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2827082382639025904901877 265038973372408678584551)
                  ·
                    rfl

theorem cell22_2322727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 5].length) (baseStart_2322727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322727 prefixEnd_2322727 := by exact prefixLift 2322727
  have htrace : WordTrace (prefixWord ++ tailWord_2322727) baseStart_2322727 baseEnd_2322727 := by
    simpa [prefixWord, tailWord_2322727, baseEnd_2322727] using wordTrace_append hprefix tailTrace_2322727
  have hstable : (prefixWord ++ tailWord_2322727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322727).length < 2 ^ (prefixWord ++ tailWord_2322727).sum := by decide
  have hdescent : baseEnd_2322727 < baseStart_2322727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322736 : List Nat := [2, 1, 1, 1, 2, 2, 2, 6, 2, 3]
def baseStart_2322736 : Nat := 118140960795 + 2322736 * 2 ^ 59
def prefixEnd_2322736 : Nat := 4983230072969 + 3 ^ 40 * 2322736 * 2
def baseEnd_2322736 : Nat := 795120001001153012278625

theorem tailTrace_2322736 : CollatzResearch.WordTrace tailWord_2322736 prefixEnd_2322736 795120001001153012278625 := by
  unfold tailWord_2322736
  simp only [CollatzResearch.WordTrace]
  refine ⟨42358570856565819285834031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56478094475421092381112041 42358570856565819285834031)
  ·
    refine ⟨63537856284848728928751047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42358570856565819285834031 63537856284848728928751047)
    ·
      refine ⟨95306784427273093393126571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63537856284848728928751047 95306784427273093393126571)
      ·
        refine ⟨142960176640909640089689857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95306784427273093393126571 142960176640909640089689857)
        ·
          refine ⟨107220132480682230067267393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142960176640909640089689857 107220132480682230067267393)
          ·
            refine ⟨80415099360511672550450545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107220132480682230067267393 80415099360511672550450545)
            ·
              refine ⟨60311324520383754412837909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80415099360511672550450545 60311324520383754412837909)
              ·
                refine ⟨2827093336892988488101777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60311324520383754412837909 2827093336892988488101777)
                ·
                  refine ⟨2120320002669741366076333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2827093336892988488101777 2120320002669741366076333)
                  ·
                    refine ⟨795120001001153012278625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2120320002669741366076333 795120001001153012278625)
                    ·
                      rfl

theorem cell22_2322736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 2, 3].length) (baseStart_2322736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322736 prefixEnd_2322736 := by exact prefixLift 2322736
  have htrace : WordTrace (prefixWord ++ tailWord_2322736) baseStart_2322736 baseEnd_2322736 := by
    simpa [prefixWord, tailWord_2322736, baseEnd_2322736] using wordTrace_append hprefix tailTrace_2322736
  have hstable : (prefixWord ++ tailWord_2322736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322736).length < 2 ^ (prefixWord ++ tailWord_2322736).sum := by decide
  have hdescent : baseEnd_2322736 < baseStart_2322736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322764 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 2, 7]
def baseStart_2322764 : Nat := 118140960795 + 2322764 * 2 ^ 59
def prefixEnd_2322764 : Nat := 4983230072969 + 3 ^ 40 * 2322764 * 2
def baseEnd_2322764 : Nat := 795129585973370272578539

theorem tailTrace_2322764 : CollatzResearch.WordTrace tailWord_2322764 prefixEnd_2322764 795129585973370272578539 := by
  unfold tailWord_2322764
  simp only [CollatzResearch.WordTrace]
  refine ⟨42359081478515099676843673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56478775304686799569124897 42359081478515099676843673)
  ·
    refine ⟨31769311108886324757632755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42359081478515099676843673 31769311108886324757632755)
    ·
      refine ⟨47653966663329487136449133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31769311108886324757632755 47653966663329487136449133)
      ·
        refine ⟨17870237498748557676168425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47653966663329487136449133 17870237498748557676168425)
        ·
          refine ⟨13402678124061418257126319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17870237498748557676168425 13402678124061418257126319)
          ·
            refine ⟨20104017186092127385689479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13402678124061418257126319 20104017186092127385689479)
            ·
              refine ⟨30156025779138191078534219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20104017186092127385689479 30156025779138191078534219)
              ·
                refine ⟨45234038668707286617801329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30156025779138191078534219 45234038668707286617801329)
                ·
                  refine ⟨33925529001530464963350997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45234038668707286617801329 33925529001530464963350997)
                  ·
                    refine ⟨795129585973370272578539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33925529001530464963350997 795129585973370272578539)
                    ·
                      rfl

theorem cell22_2322764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_2322764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322764 prefixEnd_2322764 := by exact prefixLift 2322764
  have htrace : WordTrace (prefixWord ++ tailWord_2322764) baseStart_2322764 baseEnd_2322764 := by
    simpa [prefixWord, tailWord_2322764, baseEnd_2322764] using wordTrace_append hprefix tailTrace_2322764
  have hstable : (prefixWord ++ tailWord_2322764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322764).length < 2 ^ (prefixWord ++ tailWord_2322764).sum := by decide
  have hdescent : baseEnd_2322764 < baseStart_2322764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322809 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 1, 7]
def baseStart_2322809 : Nat := 118140960795 + 2322809 * 2 ^ 59
def prefixEnd_2322809 : Nat := 4983230072969 + 3 ^ 40 * 2322809 * 2
def baseEnd_2322809 : Nat := 795144990393005155203401

theorem tailTrace_2322809 : CollatzResearch.WordTrace tailWord_2322809 prefixEnd_2322809 795144990393005155203401 := by
  unfold tailWord_2322809
  simp only [CollatzResearch.WordTrace]
  refine ⟨84719804241867172039075481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56479869494578114692716987 84719804241867172039075481)
  ·
    refine ⟨63539853181400379029306611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84719804241867172039075481 63539853181400379029306611)
    ·
      refine ⟨95309779772100568543959917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63539853181400379029306611 95309779772100568543959917)
      ·
        refine ⟨35741167414537713203984969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95309779772100568543959917 35741167414537713203984969)
        ·
          refine ⟨26805875560903284902988727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35741167414537713203984969 26805875560903284902988727)
          ·
            refine ⟨40208813341354927354483091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26805875560903284902988727 40208813341354927354483091)
            ·
              refine ⟨60313220012032391031724637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40208813341354927354483091 60313220012032391031724637)
              ·
                refine ⟨22617457504512146636896739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60313220012032391031724637 22617457504512146636896739)
                ·
                  refine ⟨33926186256768219955345109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22617457504512146636896739 33926186256768219955345109)
                  ·
                    refine ⟨795144990393005155203401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33926186256768219955345109 795144990393005155203401)
                    ·
                      rfl

theorem cell22_2322809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_2322809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322809 prefixEnd_2322809 := by exact prefixLift 2322809
  have htrace : WordTrace (prefixWord ++ tailWord_2322809) baseStart_2322809 baseEnd_2322809 := by
    simpa [prefixWord, tailWord_2322809, baseEnd_2322809] using wordTrace_append hprefix tailTrace_2322809
  have hstable : (prefixWord ++ tailWord_2322809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322809).length < 2 ^ (prefixWord ++ tailWord_2322809).sum := by decide
  have hdescent : baseEnd_2322809 < baseStart_2322809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322811 : List Nat := [1, 1, 1, 1, 1, 8, 1, 3, 5]
def baseStart_2322811 : Nat := 118140960795 + 2322811 * 2 ^ 59
def prefixEnd_2322811 : Nat := 4983230072969 + 3 ^ 40 * 2322811 * 2
def baseEnd_2322811 : Nat := 265048558344625938884465

theorem tailTrace_2322811 : CollatzResearch.WordTrace tailWord_2322811 prefixEnd_2322811 265048558344625938884465 := by
  unfold tailWord_2322811
  simp only [CollatzResearch.WordTrace]
  refine ⟨84719877187859926380648287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56479918125239950920432191 84719877187859926380648287)
  ·
    refine ⟨127079815781789889570972431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84719877187859926380648287 127079815781789889570972431)
    ·
      refine ⟨190619723672684834356458647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127079815781789889570972431 190619723672684834356458647)
      ·
        refine ⟨285929585509027251534687971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190619723672684834356458647 285929585509027251534687971)
        ·
          refine ⟨428894378263540877302031957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285929585509027251534687971 428894378263540877302031957)
          ·
            refine ⟨5026105995275869655883187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 428894378263540877302031957 5026105995275869655883187)
            ·
              refine ⟨7539158992913804483824781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5026105995275869655883187 7539158992913804483824781)
              ·
                refine ⟨2827184622342676681434293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7539158992913804483824781 2827184622342676681434293)
                ·
                  refine ⟨265048558344625938884465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2827184622342676681434293 265048558344625938884465)
                  ·
                    rfl

theorem cell22_2322811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 5].length) (baseStart_2322811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322811 prefixEnd_2322811 := by exact prefixLift 2322811
  have htrace : WordTrace (prefixWord ++ tailWord_2322811) baseStart_2322811 baseEnd_2322811 := by
    simpa [prefixWord, tailWord_2322811, baseEnd_2322811] using wordTrace_append hprefix tailTrace_2322811
  have hstable : (prefixWord ++ tailWord_2322811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322811).length < 2 ^ (prefixWord ++ tailWord_2322811).sum := by decide
  have hdescent : baseEnd_2322811 < baseStart_2322811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322871 : List Nat := [1, 1, 3, 1, 3, 3, 1, 3, 1, 5]
def baseStart_2322871 : Nat := 118140960795 + 2322871 * 2 ^ 59
def prefixEnd_2322871 : Nat := 4983230072969 + 3 ^ 40 * 2322871 * 2
def baseEnd_2322871 : Nat := 795166214260057660153211

theorem tailTrace_2322871 : CollatzResearch.WordTrace tailWord_2322871 prefixEnd_2322871 795166214260057660153211 := by
  unfold tailWord_2322871
  simp only [CollatzResearch.WordTrace]
  refine ⟨84722065567642556627832467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56481377045095037751888311 84722065567642556627832467)
  ·
    refine ⟨127083098351463834941748701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84722065567642556627832467 127083098351463834941748701)
    ·
      refine ⟨47656161881798938103155763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127083098351463834941748701 47656161881798938103155763)
      ·
        refine ⟨71484242822698407154733645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47656161881798938103155763 71484242822698407154733645)
        ·
          refine ⟨26806591058511902683025117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71484242822698407154733645 26806591058511902683025117)
          ·
            refine ⟨10052471646941963506134419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26806591058511902683025117 10052471646941963506134419)
            ·
              refine ⟨15078707470412945259201629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10052471646941963506134419 15078707470412945259201629)
              ·
                refine ⟨5654515301404854472200611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15078707470412945259201629 5654515301404854472200611)
                ·
                  refine ⟨8481772952107281708300917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5654515301404854472200611 8481772952107281708300917)
                  ·
                    refine ⟨795166214260057660153211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8481772952107281708300917 795166214260057660153211)
                    ·
                      rfl

theorem cell22_2322871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_2322871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322871 prefixEnd_2322871 := by exact prefixLift 2322871
  have htrace : WordTrace (prefixWord ++ tailWord_2322871) baseStart_2322871 baseEnd_2322871 := by
    simpa [prefixWord, tailWord_2322871, baseEnd_2322871] using wordTrace_append hprefix tailTrace_2322871
  have hstable : (prefixWord ++ tailWord_2322871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322871).length < 2 ^ (prefixWord ++ tailWord_2322871).sum := by decide
  have hdescent : baseEnd_2322871 < baseStart_2322871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322892 : List Nat := [2, 2, 1, 4, 3, 2, 2, 1, 1, 4]
def baseStart_2322892 : Nat := 118140960795 + 2322892 * 2 ^ 59
def prefixEnd_2322892 : Nat := 4983230072969 + 3 ^ 40 * 2322892 * 2
def baseEnd_2322892 : Nat := 795173402989220605378147

theorem tailTrace_2322892 : CollatzResearch.WordTrace tailWord_2322892 prefixEnd_2322892 795173402989220605378147 := by
  unfold tailWord_2322892
  simp only [CollatzResearch.WordTrace]
  refine ⟨42361415750283238607173465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56481887667044318142897953 42361415750283238607173465)
  ·
    refine ⟨31771061812712428955380099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42361415750283238607173465 31771061812712428955380099)
    ·
      refine ⟨47656592719068643433070149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31771061812712428955380099 47656592719068643433070149)
      ·
        refine ⟨8935611134825370643700653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47656592719068643433070149 8935611134825370643700653)
        ·
          refine ⟨3350854175559513991387745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8935611134825370643700653 3350854175559513991387745)
          ·
            refine ⟨2513140631669635493540809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3350854175559513991387745 2513140631669635493540809)
            ·
              refine ⟨1884855473752226620155607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2513140631669635493540809 1884855473752226620155607)
              ·
                refine ⟨2827283210628339930233411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1884855473752226620155607 2827283210628339930233411)
                ·
                  refine ⟨4240924815942509895350117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2827283210628339930233411 4240924815942509895350117)
                  ·
                    refine ⟨795173402989220605378147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4240924815942509895350117 795173402989220605378147)
                    ·
                      rfl

theorem cell22_2322892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 1, 4].length) (baseStart_2322892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322892 prefixEnd_2322892 := by exact prefixLift 2322892
  have htrace : WordTrace (prefixWord ++ tailWord_2322892) baseStart_2322892 baseEnd_2322892 := by
    simpa [prefixWord, tailWord_2322892, baseEnd_2322892] using wordTrace_append hprefix tailTrace_2322892
  have hstable : (prefixWord ++ tailWord_2322892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322892).length < 2 ^ (prefixWord ++ tailWord_2322892).sum := by decide
  have hdescent : baseEnd_2322892 < baseStart_2322892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322901 : List Nat := [1, 3, 2, 3, 1, 3, 9]
def baseStart_2322901 : Nat := 118140960795 + 2322901 * 2 ^ 59
def prefixEnd_2322901 : Nat := 4983230072969 + 3 ^ 40 * 2322901 * 2
def baseEnd_2322901 : Nat := 29450980884190651181597

theorem tailTrace_2322901 : CollatzResearch.WordTrace tailWord_2322901 prefixEnd_2322901 29450980884190651181597 := by
  unfold tailWord_2322901
  simp only [CollatzResearch.WordTrace]
  refine ⟨84723159757533871751424557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56482106505022581167616371 84723159757533871751424557)
  ·
    refine ⟨31771184909075201906784209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84723159757533871751424557 31771184909075201906784209)
    ·
      refine ⟨23828388681806401430088157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31771184909075201906784209 23828388681806401430088157)
      ·
        refine ⟨8935645755677400536283059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23828388681806401430088157 8935645755677400536283059)
        ·
          refine ⟨13403468633516100804424589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8935645755677400536283059 13403468633516100804424589)
          ·
            refine ⟨5026300737568537801659221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13403468633516100804424589 5026300737568537801659221)
            ·
              refine ⟨29450980884190651181597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5026300737568537801659221 29450980884190651181597)
              ·
                rfl

theorem cell22_2322901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 9].length) (baseStart_2322901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322901 prefixEnd_2322901 := by exact prefixLift 2322901
  have htrace : WordTrace (prefixWord ++ tailWord_2322901) baseStart_2322901 baseEnd_2322901 := by
    simpa [prefixWord, tailWord_2322901, baseEnd_2322901] using wordTrace_append hprefix tailTrace_2322901
  have hstable : (prefixWord ++ tailWord_2322901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322901).length < 2 ^ (prefixWord ++ tailWord_2322901).sum := by decide
  have hdescent : baseEnd_2322901 < baseStart_2322901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322922 : List Nat := [3, 1, 3, 1, 3, 2, 3, 1, 2, 3]
def baseStart_2322922 : Nat := 118140960795 + 2322922 * 2 ^ 59
def prefixEnd_2322922 : Nat := 4983230072969 + 3 ^ 40 * 2322922 * 2
def baseEnd_2322922 : Nat := 795183672602310527128055

theorem tailTrace_2322922 : CollatzResearch.WordTrace tailWord_2322922 prefixEnd_2322922 795183672602310527128055 := by
  unfold tailWord_2322922
  simp only [CollatzResearch.WordTrace]
  refine ⟨21180981422614448084484755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56482617126971861558626013 21180981422614448084484755)
  ·
    refine ⟨31771472133921672126727133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21180981422614448084484755 31771472133921672126727133)
    ·
      refine ⟨11914302050220627047522675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31771472133921672126727133 11914302050220627047522675)
      ·
        refine ⟨17871453075330940571284013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11914302050220627047522675 17871453075330940571284013)
        ·
          refine ⟨6701794903249102714231505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17871453075330940571284013 6701794903249102714231505)
          ·
            refine ⟨5026346177436827035673629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6701794903249102714231505 5026346177436827035673629)
            ·
              refine ⟨1884879816538810138377611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5026346177436827035673629 1884879816538810138377611)
              ·
                refine ⟨2827319724808215207566417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1884879816538810138377611 2827319724808215207566417)
                ·
                  refine ⟨2120489793606161405674813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2827319724808215207566417 2120489793606161405674813)
                  ·
                    refine ⟨795183672602310527128055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2120489793606161405674813 795183672602310527128055)
                    ·
                      rfl

theorem cell22_2322922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_2322922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322922 prefixEnd_2322922 := by exact prefixLift 2322922
  have htrace : WordTrace (prefixWord ++ tailWord_2322922) baseStart_2322922 baseEnd_2322922 := by
    simpa [prefixWord, tailWord_2322922, baseEnd_2322922] using wordTrace_append hprefix tailTrace_2322922
  have hstable : (prefixWord ++ tailWord_2322922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322922).length < 2 ^ (prefixWord ++ tailWord_2322922).sum := by decide
  have hdescent : baseEnd_2322922 < baseStart_2322922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322961 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 2, 5]
def baseStart_2322961 : Nat := 118140960795 + 2322961 * 2 ^ 59
def prefixEnd_2322961 : Nat := 4983230072969 + 3 ^ 40 * 2322961 * 2
def baseEnd_2322961 : Nat := 795197023099327425402935

theorem tailTrace_2322961 : CollatzResearch.WordTrace tailWord_2322961 prefixEnd_2322961 795197023099327425402935 := by
  unfold tailWord_2322961
  simp only [CollatzResearch.WordTrace]
  refine ⟨84725348137316501998608737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56483565424877667999072491 84725348137316501998608737)
  ·
    refine ⟨63544011102987376498956553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84725348137316501998608737 63544011102987376498956553)
    ·
      refine ⟨47658008327240532374217415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63544011102987376498956553 47658008327240532374217415)
      ·
        refine ⟨71487012490860798561326123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47658008327240532374217415 71487012490860798561326123)
        ·
          refine ⟨107230518736291197841989185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71487012490860798561326123 107230518736291197841989185)
          ·
            refine ⟨80422889052218398381491889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107230518736291197841989185 80422889052218398381491889)
            ·
              refine ⟨60317166789163798786118917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80422889052218398381491889 60317166789163798786118917)
              ·
                refine ⟨11309468772968212272397297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60317166789163798786118917 11309468772968212272397297)
                ·
                  refine ⟨8482101579726159204297973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11309468772968212272397297 8482101579726159204297973)
                  ·
                    refine ⟨795197023099327425402935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8482101579726159204297973 795197023099327425402935)
                    ·
                      rfl

theorem cell22_2322961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_2322961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2322961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2322961 prefixEnd_2322961 := by exact prefixLift 2322961
  have htrace : WordTrace (prefixWord ++ tailWord_2322961) baseStart_2322961 baseEnd_2322961 := by
    simpa [prefixWord, tailWord_2322961, baseEnd_2322961] using wordTrace_append hprefix tailTrace_2322961
  have hstable : (prefixWord ++ tailWord_2322961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322961).length < 2 ^ (prefixWord ++ tailWord_2322961).sum := by decide
  have hdescent : baseEnd_2322961 < baseStart_2322961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323023 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 4, 3]
def baseStart_2323023 : Nat := 118140960795 + 2323023 * 2 ^ 59
def prefixEnd_2323023 : Nat := 4983230072969 + 3 ^ 40 * 2323023 * 2
def baseEnd_2323023 : Nat := 795218246966379930352745

theorem tailTrace_2323023 : CollatzResearch.WordTrace tailWord_2323023 prefixEnd_2323023 795218246966379930352745 := by
  unfold tailWord_2323023
  simp only [CollatzResearch.WordTrace]
  refine ⟨84727609463091886587365723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56485072975394591058243815 84727609463091886587365723)
  ·
    refine ⟨127091414194637829881048585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84727609463091886587365723 127091414194637829881048585)
    ·
      refine ⟨95318560645978372410786439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127091414194637829881048585 95318560645978372410786439)
      ·
        refine ⟨142977840968967558616179659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95318560645978372410786439 142977840968967558616179659)
        ·
          refine ⟨214466761453451337924269489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142977840968967558616179659 214466761453451337924269489)
          ·
            refine ⟨160850071090088503443202117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214466761453451337924269489 160850071090088503443202117)
            ·
              refine ⟨30159388329391594395600397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160850071090088503443202117 30159388329391594395600397)
              ·
                refine ⟨11309770623521847898350149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30159388329391594395600397 11309770623521847898350149)
                ·
                  refine ⟨2120581991910346480940653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11309770623521847898350149 2120581991910346480940653)
                  ·
                    refine ⟨795218246966379930352745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2120581991910346480940653 795218246966379930352745)
                    ·
                      rfl

theorem cell22_2323023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 3].length) (baseStart_2323023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323023 prefixEnd_2323023 := by exact prefixLift 2323023
  have htrace : WordTrace (prefixWord ++ tailWord_2323023) baseStart_2323023 baseEnd_2323023 := by
    simpa [prefixWord, tailWord_2323023, baseEnd_2323023] using wordTrace_append hprefix tailTrace_2323023
  have hstable : (prefixWord ++ tailWord_2323023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323023).length < 2 ^ (prefixWord ++ tailWord_2323023).sum := by decide
  have hdescent : baseEnd_2323023 < baseStart_2323023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323025 : List Nat := [1, 2, 2, 1, 3, 4, 1, 4, 4]
def baseStart_2323025 : Nat := 118140960795 + 2323025 * 2 ^ 59
def prefixEnd_2323025 : Nat := 4983230072969 + 3 ^ 40 * 2323025 * 2
def baseEnd_2323025 : Nat := 265072977202417530600913

theorem tailTrace_2323025 : CollatzResearch.WordTrace tailWord_2323025 prefixEnd_2323025 265072977202417530600913 := by
  unfold tailWord_2323025
  simp only [CollatzResearch.WordTrace]
  refine ⟨84727682409084640928938529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56485121606056427285959019 84727682409084640928938529)
  ·
    refine ⟨63545761806813480696703897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84727682409084640928938529 63545761806813480696703897)
    ·
      refine ⟨47659321355110110522527923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63545761806813480696703897 47659321355110110522527923)
      ·
        refine ⟨71488982032665165783791885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47659321355110110522527923 71488982032665165783791885)
        ·
          refine ⟨26808368262249437168921957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71488982032665165783791885 26808368262249437168921957)
          ·
            refine ⟨5026569049171769469172867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26808368262249437168921957 5026569049171769469172867)
            ·
              refine ⟨7539853573757654203759301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5026569049171769469172867 7539853573757654203759301)
              ·
                refine ⟨1413722545079560163204869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7539853573757654203759301 1413722545079560163204869)
                ·
                  refine ⟨265072977202417530600913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1413722545079560163204869 265072977202417530600913)
                  ·
                    rfl

theorem cell22_2323025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 4].length) (baseStart_2323025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323025 prefixEnd_2323025 := by exact prefixLift 2323025
  have htrace : WordTrace (prefixWord ++ tailWord_2323025) baseStart_2323025 baseEnd_2323025 := by
    simpa [prefixWord, tailWord_2323025, baseEnd_2323025] using wordTrace_append hprefix tailTrace_2323025
  have hstable : (prefixWord ++ tailWord_2323025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323025).length < 2 ^ (prefixWord ++ tailWord_2323025).sum := by decide
  have hdescent : baseEnd_2323025 < baseStart_2323025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323040 : List Nat := [2, 1, 1, 3, 2, 1, 4, 3, 2, 3]
def baseStart_2323040 : Nat := 118140960795 + 2323040 * 2 ^ 59
def prefixEnd_2323040 : Nat := 4983230072969 + 3 ^ 40 * 2323040 * 2
def baseEnd_2323040 : Nat := 795224066413797552677693

theorem tailTrace_2323040 : CollatzResearch.WordTrace tailWord_2323040 prefixEnd_2323040 795224066413797552677693 := by
  unfold tailWord_2323040
  simp only [CollatzResearch.WordTrace]
  refine ⟨42364114752015149245367287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56485486336020198993823049 42364114752015149245367287)
  ·
    refine ⟨63546172128022723868050931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42364114752015149245367287 63546172128022723868050931)
    ·
      refine ⟨95319258192034085802076397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63546172128022723868050931 95319258192034085802076397)
      ·
        refine ⟨35744721822012782175778649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95319258192034085802076397 35744721822012782175778649)
        ·
          refine ⟨26808541366509586631833987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35744721822012782175778649 26808541366509586631833987)
          ·
            refine ⟨40212812049764379947750981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26808541366509586631833987 40212812049764379947750981)
            ·
              refine ⟨7539902259330821240203309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40212812049764379947750981 7539902259330821240203309)
              ·
                refine ⟨2827463347249057965076241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7539902259330821240203309 2827463347249057965076241)
                ·
                  refine ⟨2120597510436793473807181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2827463347249057965076241 2120597510436793473807181)
                  ·
                    refine ⟨795224066413797552677693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2120597510436793473807181 795224066413797552677693)
                    ·
                      rfl

theorem cell22_2323040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 2, 3].length) (baseStart_2323040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323040 prefixEnd_2323040 := by exact prefixLift 2323040
  have htrace : WordTrace (prefixWord ++ tailWord_2323040) baseStart_2323040 baseEnd_2323040 := by
    simpa [prefixWord, tailWord_2323040, baseEnd_2323040] using wordTrace_append hprefix tailTrace_2323040
  have hstable : (prefixWord ++ tailWord_2323040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323040).length < 2 ^ (prefixWord ++ tailWord_2323040).sum := by decide
  have hdescent : baseEnd_2323040 < baseStart_2323040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323042 : List Nat := [3, 3, 2, 3, 1, 1, 1, 2, 6]
def baseStart_2323042 : Nat := 118140960795 + 2323042 * 2 ^ 59
def prefixEnd_2323042 : Nat := 4983230072969 + 3 ^ 40 * 2323042 * 2
def baseEnd_2323042 : Nat := 265074917018223404709229

theorem tailTrace_2323042 : CollatzResearch.WordTrace tailWord_2323042 prefixEnd_2323042 265074917018223404709229 := by
  unfold tailWord_2323042
  simp only [CollatzResearch.WordTrace]
  refine ⟨21182075612505763208076845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56485534966682035221538253 21182075612505763208076845)
  ·
    refine ⟨7943278354689661203028817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21182075612505763208076845 7943278354689661203028817)
    ·
      refine ⟨5957458766017245902271613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7943278354689661203028817 5957458766017245902271613)
      ·
        refine ⟨2234047037256467213351855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5957458766017245902271613 2234047037256467213351855)
        ·
          refine ⟨3351070555884700820027783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2234047037256467213351855 3351070555884700820027783)
          ·
            refine ⟨5026605833827051230041675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3351070555884700820027783 5026605833827051230041675)
            ·
              refine ⟨7539908750740576845062513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5026605833827051230041675 7539908750740576845062513)
              ·
                refine ⟨5654931563055432633796885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7539908750740576845062513 5654931563055432633796885)
                ·
                  refine ⟨265074917018223404709229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5654931563055432633796885 265074917018223404709229)
                  ·
                    rfl

theorem cell22_2323042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_2323042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323042 prefixEnd_2323042 := by exact prefixLift 2323042
  have htrace : WordTrace (prefixWord ++ tailWord_2323042) baseStart_2323042 baseEnd_2323042 := by
    simpa [prefixWord, tailWord_2323042, baseEnd_2323042] using wordTrace_append hprefix tailTrace_2323042
  have hstable : (prefixWord ++ tailWord_2323042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323042).length < 2 ^ (prefixWord ++ tailWord_2323042).sum := by decide
  have hdescent : baseEnd_2323042 < baseStart_2323042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323051 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 1, 9]
def baseStart_2323051 : Nat := 118140960795 + 2323051 * 2 ^ 59
def prefixEnd_2323051 : Nat := 4983230072969 + 3 ^ 40 * 2323051 * 2
def baseEnd_2323051 : Nat := 795227831938597190652659

theorem tailTrace_2323051 : CollatzResearch.WordTrace tailWord_2323051 prefixEnd_2323051 795227831938597190652659 := by
  unfold tailWord_2323051
  simp only [CollatzResearch.WordTrace]
  refine ⟨84728630706990447369385007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56485753804660298246256671 84728630706990447369385007)
  ·
    refine ⟨127092946060485671054077511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84728630706990447369385007 127092946060485671054077511)
    ·
      refine ⟨190639419090728506581116267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127092946060485671054077511 190639419090728506581116267)
      ·
        refine ⟨285959128636092759871674401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190639419090728506581116267 285959128636092759871674401)
        ·
          refine ⟨214469346477069569903755801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285959128636092759871674401 214469346477069569903755801)
          ·
            refine ⟨160852009857802177427816851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214469346477069569903755801 160852009857802177427816851)
            ·
              refine ⟨241278014786703266141725277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160852009857802177427816851 241278014786703266141725277)
              ·
                refine ⟨90479255545013724803146979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241278014786703266141725277 90479255545013724803146979)
                ·
                  refine ⟨135718883317520587204720469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90479255545013724803146979 135718883317520587204720469)
                  ·
                    refine ⟨795227831938597190652659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 135718883317520587204720469 795227831938597190652659)
                    ·
                      rfl

theorem cell22_2323051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 9].length) (baseStart_2323051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323051 prefixEnd_2323051 := by exact prefixLift 2323051
  have htrace : WordTrace (prefixWord ++ tailWord_2323051) baseStart_2323051 baseEnd_2323051 := by
    simpa [prefixWord, tailWord_2323051, baseEnd_2323051] using wordTrace_append hprefix tailTrace_2323051
  have hstable : (prefixWord ++ tailWord_2323051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323051).length < 2 ^ (prefixWord ++ tailWord_2323051).sum := by decide
  have hdescent : baseEnd_2323051 < baseStart_2323051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323061 : List Nat := [1, 3, 4, 2, 3, 1, 2, 1, 1, 4]
def baseStart_2323061 : Nat := 118140960795 + 2323061 * 2 ^ 59
def prefixEnd_2323061 : Nat := 4983230072969 + 3 ^ 40 * 2323061 * 2
def baseEnd_2323061 : Nat := 795231255142960497902629

theorem tailTrace_2323061 : CollatzResearch.WordTrace tailWord_2323061 prefixEnd_2323061 795231255142960497902629 := by
  unfold tailWord_2323061
  simp only [CollatzResearch.WordTrace]
  refine ⟨84728995436954219077249037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56485996957969479384832691 84728995436954219077249037)
  ·
    refine ⟨31773373288857832153968389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84728995436954219077249037 31773373288857832153968389)
    ·
      refine ⟨5957507491660843528869073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31773373288857832153968389 5957507491660843528869073)
      ·
        refine ⟨4468130618745632646651805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5957507491660843528869073 4468130618745632646651805)
        ·
          refine ⟨1675548982029612242494427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4468130618745632646651805 1675548982029612242494427)
          ·
            refine ⟨2513323473044418363741641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1675548982029612242494427 2513323473044418363741641)
            ·
              refine ⟨1884992604783313772806231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2513323473044418363741641 1884992604783313772806231)
              ·
                refine ⟨2827488907174970659209347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1884992604783313772806231 2827488907174970659209347)
                ·
                  refine ⟨4241233360762455988814021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2827488907174970659209347 4241233360762455988814021)
                  ·
                    refine ⟨795231255142960497902629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4241233360762455988814021 795231255142960497902629)
                    ·
                      rfl

theorem cell22_2323061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_2323061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323061 prefixEnd_2323061 := by exact prefixLift 2323061
  have htrace : WordTrace (prefixWord ++ tailWord_2323061) baseStart_2323061 baseEnd_2323061 := by
    simpa [prefixWord, tailWord_2323061, baseEnd_2323061] using wordTrace_append hprefix tailTrace_2323061
  have hstable : (prefixWord ++ tailWord_2323061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323061).length < 2 ^ (prefixWord ++ tailWord_2323061).sum := by decide
  have hdescent : baseEnd_2323061 < baseStart_2323061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323102 : List Nat := [4, 3, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_2323102 : Nat := 118140960795 + 2323102 * 2 ^ 59
def prefixEnd_2323102 : Nat := 4983230072969 + 3 ^ 40 * 2323102 * 2
def baseEnd_2323102 : Nat := 795245290280850057627503

theorem tailTrace_2323102 : CollatzResearch.WordTrace tailWord_2323102 prefixEnd_2323102 795245290280850057627503 := by
  unfold tailWord_2323102
  simp only [CollatzResearch.WordTrace]
  refine ⟨10591311353725710384936445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56486993886537122052994373 10591311353725710384936445)
  ·
    refine ⟨3971741757647141394351167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10591311353725710384936445 3971741757647141394351167)
    ·
      refine ⟨5957612636470712091526751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3971741757647141394351167 5957612636470712091526751)
      ·
        refine ⟨8936418954706068137290127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5957612636470712091526751 8936418954706068137290127)
        ·
          refine ⟨13404628432059102205935191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8936418954706068137290127 13404628432059102205935191)
          ·
            refine ⟨20106942648088653308902787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13404628432059102205935191 20106942648088653308902787)
            ·
              refine ⟨30160413972132979963354181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20106942648088653308902787 30160413972132979963354181)
              ·
                refine ⟨5655077619774933743128909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30160413972132979963354181 5655077619774933743128909)
                ·
                  refine ⟨2120654107415600153673341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5655077619774933743128909 2120654107415600153673341)
                  ·
                    refine ⟨795245290280850057627503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2120654107415600153673341 795245290280850057627503)
                    ·
                      rfl

theorem cell22_2323102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_2323102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323102 prefixEnd_2323102 := by exact prefixLift 2323102
  have htrace : WordTrace (prefixWord ++ tailWord_2323102) baseStart_2323102 baseEnd_2323102 := by
    simpa [prefixWord, tailWord_2323102, baseEnd_2323102] using wordTrace_append hprefix tailTrace_2323102
  have hstable : (prefixWord ++ tailWord_2323102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323102).length < 2 ^ (prefixWord ++ tailWord_2323102).sum := by decide
  have hdescent : baseEnd_2323102 < baseStart_2323102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323119 : List Nat := [1, 1, 2, 1, 2, 7, 1, 3, 1, 3]
def baseStart_2323119 : Nat := 118140960795 + 2323119 * 2 ^ 59
def prefixEnd_2323119 : Nat := 4983230072969 + 3 ^ 40 * 2323119 * 2
def baseEnd_2323119 : Nat := 795251109728267679952451

theorem tailTrace_2323119 : CollatzResearch.WordTrace tailWord_2323119 prefixEnd_2323119 795251109728267679952451 := by
  unfold tailWord_2323119
  simp only [CollatzResearch.WordTrace]
  refine ⟨84731110870744094982860411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56487407247162729988573607 84731110870744094982860411)
  ·
    refine ⟨127096666306116142474290617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84731110870744094982860411 127096666306116142474290617)
    ·
      refine ⟨95322499729587106855717963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127096666306116142474290617 95322499729587106855717963)
      ·
        refine ⟨142983749594380660283576945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95322499729587106855717963 142983749594380660283576945)
        ·
          refine ⟨107237812195785495212682709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142983749594380660283576945 107237812195785495212682709)
          ·
            refine ⟨2513386223338722544047251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 107237812195785495212682709 2513386223338722544047251)
            ·
              refine ⟨3770079335008083816070877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2513386223338722544047251 3770079335008083816070877)
              ·
                refine ⟨1413779750628031431026579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3770079335008083816070877 1413779750628031431026579)
                ·
                  refine ⟨2120669625942047146539869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1413779750628031431026579 2120669625942047146539869)
                  ·
                    refine ⟨795251109728267679952451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2120669625942047146539869 795251109728267679952451)
                    ·
                      rfl

theorem cell22_2323119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 1, 3].length) (baseStart_2323119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323119 prefixEnd_2323119 := by exact prefixLift 2323119
  have htrace : WordTrace (prefixWord ++ tailWord_2323119) baseStart_2323119 baseEnd_2323119 := by
    simpa [prefixWord, tailWord_2323119, baseEnd_2323119] using wordTrace_append hprefix tailTrace_2323119
  have hstable : (prefixWord ++ tailWord_2323119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323119).length < 2 ^ (prefixWord ++ tailWord_2323119).sum := by decide
  have hdescent : baseEnd_2323119 < baseStart_2323119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323128 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 7, 4]
def baseStart_2323128 : Nat := 118140960795 + 2323128 * 2 ^ 59
def prefixEnd_2323128 : Nat := 4983230072969 + 3 ^ 40 * 2323128 * 2
def baseEnd_2323128 : Nat := 795254190612194656477423

theorem tailTrace_2323128 : CollatzResearch.WordTrace tailWord_2323128 prefixEnd_2323128 795254190612194656477423 := by
  unfold tailWord_2323128
  simp only [CollatzResearch.WordTrace]
  refine ⟨42365719563855744759969019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56487626085140993013292025 42365719563855744759969019)
  ·
    refine ⟨63548579345783617139953529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42365719563855744759969019 63548579345783617139953529)
    ·
      refine ⟨47661434509337712854965147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63548579345783617139953529 47661434509337712854965147)
      ·
        refine ⟨71492151764006569282447721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47661434509337712854965147 71492151764006569282447721)
        ·
          refine ⟨53619113823004926961835791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71492151764006569282447721 53619113823004926961835791)
          ·
            refine ⟨80428670734507390442753687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53619113823004926961835791 80428670734507390442753687)
            ·
              refine ⟨120643006101761085664130531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80428670734507390442753687 120643006101761085664130531)
              ·
                refine ⟨180964509152641628496195797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120643006101761085664130531 180964509152641628496195797)
                ·
                  refine ⟨4241355683265038167879589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 180964509152641628496195797 4241355683265038167879589)
                  ·
                    refine ⟨795254190612194656477423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4241355683265038167879589 795254190612194656477423)
                    ·
                      rfl

theorem cell22_2323128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_2323128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323128 prefixEnd_2323128 := by exact prefixLift 2323128
  have htrace : WordTrace (prefixWord ++ tailWord_2323128) baseStart_2323128 baseEnd_2323128 := by
    simpa [prefixWord, tailWord_2323128, baseEnd_2323128] using wordTrace_append hprefix tailTrace_2323128
  have hstable : (prefixWord ++ tailWord_2323128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323128).length < 2 ^ (prefixWord ++ tailWord_2323128).sum := by decide
  have hdescent : baseEnd_2323128 < baseStart_2323128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323143 : List Nat := [1, 1, 4, 1, 1, 1, 2, 5, 6]
def baseStart_2323143 : Nat := 118140960795 + 2323143 * 2 ^ 59
def prefixEnd_2323143 : Nat := 4983230072969 + 3 ^ 40 * 2323143 * 2
def baseEnd_2323143 : Nat := 265086441806246539117459

theorem tailTrace_2323143 : CollatzResearch.WordTrace tailWord_2323143 prefixEnd_2323143 265086441806246539117459 := by
  unfold tailWord_2323143
  simp only [CollatzResearch.WordTrace]
  refine ⟨84731986222657147081734083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56487990815104764721156055 84731986222657147081734083)
  ·
    refine ⟨127097979333985720622601125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84731986222657147081734083 127097979333985720622601125)
    ·
      refine ⟨23830871125122322616737711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127097979333985720622601125 23830871125122322616737711)
      ·
        refine ⟨35746306687683483925106567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23830871125122322616737711 35746306687683483925106567)
        ·
          refine ⟨53619460031525225887659851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35746306687683483925106567 53619460031525225887659851)
          ·
            refine ⟨80429190047287838831489777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53619460031525225887659851 80429190047287838831489777)
            ·
              refine ⟨60321892535465879123617333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80429190047287838831489777 60321892535465879123617333)
              ·
                refine ⟨5655177425199926167839125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60321892535465879123617333 5655177425199926167839125)
                ·
                  refine ⟨265086441806246539117459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5655177425199926167839125 265086441806246539117459)
                  ·
                    rfl

theorem cell22_2323143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 6].length) (baseStart_2323143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323143 prefixEnd_2323143 := by exact prefixLift 2323143
  have htrace : WordTrace (prefixWord ++ tailWord_2323143) baseStart_2323143 baseEnd_2323143 := by
    simpa [prefixWord, tailWord_2323143, baseEnd_2323143] using wordTrace_append hprefix tailTrace_2323143
  have hstable : (prefixWord ++ tailWord_2323143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323143).length < 2 ^ (prefixWord ++ tailWord_2323143).sum := by decide
  have hdescent : baseEnd_2323143 < baseStart_2323143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323149 : List Nat := [1, 6, 2, 1, 2, 1, 1, 3, 5]
def baseStart_2323149 : Nat := 118140960795 + 2323149 * 2 ^ 59
def prefixEnd_2323149 : Nat := 4983230072969 + 3 ^ 40 * 2323149 * 2
def baseEnd_2323149 : Nat := 265087126447119200567453

theorem tailTrace_2323149 : CollatzResearch.WordTrace tailWord_2323149 prefixEnd_2323149 265087126447119200567453 := by
  unfold tailWord_2323149
  simp only [CollatzResearch.WordTrace]
  refine ⟨84732205060635410106452501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56488136707090273404301667 84732205060635410106452501)
  ·
    refine ⟨3971822112217284848739961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 84732205060635410106452501 3971822112217284848739961)
    ·
      refine ⟨2978866584162963636554971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3971822112217284848739961 2978866584162963636554971)
      ·
        refine ⟨4468299876244445454832457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2978866584162963636554971 4468299876244445454832457)
        ·
          refine ⟨3351224907183334091124343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4468299876244445454832457 3351224907183334091124343)
          ·
            refine ⟨5026837360775001136686515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3351224907183334091124343 5026837360775001136686515)
            ·
              refine ⟨7540256041162501705029773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5026837360775001136686515 7540256041162501705029773)
              ·
                refine ⟨2827596015435938139386165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7540256041162501705029773 2827596015435938139386165)
                ·
                  refine ⟨265087126447119200567453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2827596015435938139386165 265087126447119200567453)
                  ·
                    rfl

theorem cell22_2323149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_2323149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323149 prefixEnd_2323149 := by exact prefixLift 2323149
  have htrace : WordTrace (prefixWord ++ tailWord_2323149) baseStart_2323149 baseEnd_2323149 := by
    simpa [prefixWord, tailWord_2323149, baseEnd_2323149] using wordTrace_append hprefix tailTrace_2323149
  have hstable : (prefixWord ++ tailWord_2323149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323149).length < 2 ^ (prefixWord ++ tailWord_2323149).sum := by decide
  have hdescent : baseEnd_2323149 < baseStart_2323149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323192 : List Nat := [2, 1, 2, 1, 1, 2, 6, 2, 2, 3]
def baseStart_2323192 : Nat := 118140960795 + 2323192 * 2 ^ 59
def prefixEnd_2323192 : Nat := 4983230072969 + 3 ^ 40 * 2323192 * 2
def baseEnd_2323192 : Nat := 795276099120119822877227

theorem tailTrace_2323192 : CollatzResearch.WordTrace tailWord_2323192 prefixEnd_2323192 795276099120119822877227 := by
  unfold tailWord_2323192
  simp only [CollatzResearch.WordTrace]
  refine ⟨42366886699739814225133915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56489182266319752300178553 42366886699739814225133915)
  ·
    refine ⟨63550330049609721337700873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42366886699739814225133915 63550330049609721337700873)
    ·
      refine ⟨47662747537207291003275655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63550330049609721337700873 47662747537207291003275655)
      ·
        refine ⟨71494121305810936504913483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47662747537207291003275655 71494121305810936504913483)
        ·
          refine ⟨107241181958716404757370225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71494121305810936504913483 107241181958716404757370225)
          ·
            refine ⟨80430886469037303568027669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107241181958716404757370225 80430886469037303568027669)
            ·
              refine ⟨3770197803236123604751297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80430886469037303568027669 3770197803236123604751297)
              ·
                refine ⟨2827648352427092703563473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3770197803236123604751297 2827648352427092703563473)
                ·
                  refine ⟨2120736264320319527672605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2827648352427092703563473 2120736264320319527672605)
                  ·
                    refine ⟨795276099120119822877227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2120736264320319527672605 795276099120119822877227)
                    ·
                      rfl

theorem cell22_2323192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_2323192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323192 prefixEnd_2323192 := by exact prefixLift 2323192
  have htrace : WordTrace (prefixWord ++ tailWord_2323192) baseStart_2323192 baseEnd_2323192 := by
    simpa [prefixWord, tailWord_2323192, baseEnd_2323192] using wordTrace_append hprefix tailTrace_2323192
  have hstable : (prefixWord ++ tailWord_2323192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323192).length < 2 ^ (prefixWord ++ tailWord_2323192).sum := by decide
  have hdescent : baseEnd_2323192 < baseStart_2323192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323203 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 2, 7]
def baseStart_2323203 : Nat := 118140960795 + 2323203 * 2 ^ 59
def prefixEnd_2323203 : Nat := 4983230072969 + 3 ^ 40 * 2323203 * 2
def baseEnd_2323203 : Nat := 795279864644919460852193

theorem tailTrace_2323203 : CollatzResearch.WordTrace tailWord_2323203 prefixEnd_2323203 795279864644919460852193 := by
  unfold tailWord_2323203
  simp only [CollatzResearch.WordTrace]
  refine ⟨84734174602439777328918263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56489449734959851552612175 84734174602439777328918263)
  ·
    refine ⟨127101261903659665993377395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84734174602439777328918263 127101261903659665993377395)
    ·
      refine ⟨190651892855489498990066093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127101261903659665993377395 190651892855489498990066093)
      ·
        refine ⟨71494459820808562121274785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190651892855489498990066093 71494459820808562121274785)
        ·
          refine ⟨53620844865606421590956089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71494459820808562121274785 53620844865606421590956089)
          ·
            refine ⟨40215633649204816193217067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53620844865606421590956089 40215633649204816193217067)
            ·
              refine ⟨60323450473807224289825601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40215633649204816193217067 60323450473807224289825601)
              ·
                refine ⟨45242587855355418217369201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60323450473807224289825601 45242587855355418217369201)
                ·
                  refine ⟨33931940891516563663026901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45242587855355418217369201 33931940891516563663026901)
                  ·
                    refine ⟨795279864644919460852193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33931940891516563663026901 795279864644919460852193)
                    ·
                      rfl

theorem cell22_2323203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 7].length) (baseStart_2323203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323203 prefixEnd_2323203 := by exact prefixLift 2323203
  have htrace : WordTrace (prefixWord ++ tailWord_2323203) baseStart_2323203 baseEnd_2323203 := by
    simpa [prefixWord, tailWord_2323203, baseEnd_2323203] using wordTrace_append hprefix tailTrace_2323203
  have hstable : (prefixWord ++ tailWord_2323203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323203).length < 2 ^ (prefixWord ++ tailWord_2323203).sum := by decide
  have hdescent : baseEnd_2323203 < baseStart_2323203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323250 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 7]
def baseStart_2323250 : Nat := 118140960795 + 2323250 * 2 ^ 59
def prefixEnd_2323250 : Nat := 4983230072969 + 3 ^ 40 * 2323250 * 2
def baseEnd_2323250 : Nat := 265098651235142334975683

theorem tailTrace_2323250 : CollatzResearch.WordTrace tailWord_2323250 prefixEnd_2323250 265098651235142334975683 := by
  unfold tailWord_2323250
  simp only [CollatzResearch.WordTrace]
  refine ⟨21183972208317376088969801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56490592555513002903919469 21183972208317376088969801)
  ·
    refine ⟨15887979156238032066727351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21183972208317376088969801 15887979156238032066727351)
    ·
      refine ⟨23831968734357048100091027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15887979156238032066727351 23831968734357048100091027)
      ·
        refine ⟨35747953101535572150136541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23831968734357048100091027 35747953101535572150136541)
        ·
          refine ⟨13405482413075839556301203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35747953101535572150136541 13405482413075839556301203)
          ·
            refine ⟨20108223619613759334451805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13405482413075839556301203 20108223619613759334451805)
            ·
              refine ⟨7540583857355159750419427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20108223619613759334451805 7540583857355159750419427)
              ·
                refine ⟨11310875786032739625629141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7540583857355159750419427 11310875786032739625629141)
                ·
                  refine ⟨265098651235142334975683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11310875786032739625629141 265098651235142334975683)
                  ·
                    rfl

theorem cell22_2323250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_2323250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323250 prefixEnd_2323250 := by exact prefixLift 2323250
  have htrace : WordTrace (prefixWord ++ tailWord_2323250) baseStart_2323250 baseEnd_2323250 := by
    simpa [prefixWord, tailWord_2323250, baseEnd_2323250] using wordTrace_append hprefix tailTrace_2323250
  have hstable : (prefixWord ++ tailWord_2323250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323250).length < 2 ^ (prefixWord ++ tailWord_2323250).sum := by decide
  have hdescent : baseEnd_2323250 < baseStart_2323250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323267 : List Nat := [1, 1, 1, 3, 1, 4, 5, 1, 5]
def baseStart_2323267 : Nat := 118140960795 + 2323267 * 2 ^ 59
def prefixEnd_2323267 : Nat := 4983230072969 + 3 ^ 40 * 2323267 * 2
def baseEnd_2323267 : Nat := 265100591050948209083999

theorem tailTrace_2323267 : CollatzResearch.WordTrace tailWord_2323267 prefixEnd_2323267 265100591050948209083999 := by
  unfold tailWord_2323267
  simp only [CollatzResearch.WordTrace]
  refine ⟨84736508874207916259248055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56491005916138610839498703 84736508874207916259248055)
  ·
    refine ⟨127104763311311874388872083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84736508874207916259248055 127104763311311874388872083)
    ·
      refine ⟨190657144966967811583308125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127104763311311874388872083 190657144966967811583308125)
      ·
        refine ⟨71496429362612929343740547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190657144966967811583308125 71496429362612929343740547)
        ·
          refine ⟨107244644043919394015610821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71496429362612929343740547 107244644043919394015610821)
          ·
            refine ⟨20108370758234886377927029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107244644043919394015610821 20108370758234886377927029)
            ·
              refine ⟨1885159758584520597930659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20108370758234886377927029 1885159758584520597930659)
              ·
                refine ⟨2827739637876780896895989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1885159758584520597930659 2827739637876780896895989)
                ·
                  refine ⟨265100591050948209083999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2827739637876780896895989 265100591050948209083999)
                  ·
                    rfl

theorem cell22_2323267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 5].length) (baseStart_2323267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323267 prefixEnd_2323267 := by exact prefixLift 2323267
  have htrace : WordTrace (prefixWord ++ tailWord_2323267) baseStart_2323267 baseEnd_2323267 := by
    simpa [prefixWord, tailWord_2323267, baseEnd_2323267] using wordTrace_append hprefix tailTrace_2323267
  have hstable : (prefixWord ++ tailWord_2323267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323267).length < 2 ^ (prefixWord ++ tailWord_2323267).sum := by decide
  have hdescent : baseEnd_2323267 < baseStart_2323267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323280 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 3, 4]
def baseStart_2323280 : Nat := 118140960795 + 2323280 * 2 ^ 59
def prefixEnd_2323280 : Nat := 4983230072969 + 3 ^ 40 * 2323280 * 2
def baseEnd_2323280 : Nat := 795306223318516926676957

theorem tailTrace_2323280 : CollatzResearch.WordTrace tailWord_2323280 prefixEnd_2323280 795306223318516926676957 := by
  unfold tailWord_2323280
  simp only [CollatzResearch.WordTrace]
  refine ⟨42368491511580409739735647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56491322015440546319647529 42368491511580409739735647)
  ·
    refine ⟨63552737267370614609603471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42368491511580409739735647 63552737267370614609603471)
    ·
      refine ⟨95329105901055921914405207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63552737267370614609603471 95329105901055921914405207)
      ·
        refine ⟨142993658851583882871607811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95329105901055921914405207 142993658851583882871607811)
        ·
          refine ⟨214490488277375824307411717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142993658851583882871607811 214490488277375824307411717)
          ·
            refine ⟨40216966552007967057639697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 214490488277375824307411717 40216966552007967057639697)
            ·
              refine ⟨30162724914005975293229773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40216966552007967057639697 30162724914005975293229773)
              ·
                refine ⟨11311021842752240734961165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30162724914005975293229773 11311021842752240734961165)
                ·
                  refine ⟨4241633191032090275610437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11311021842752240734961165 4241633191032090275610437)
                  ·
                    refine ⟨795306223318516926676957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4241633191032090275610437 795306223318516926676957)
                    ·
                      rfl

theorem cell22_2323280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 3, 4].length) (baseStart_2323280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323280 prefixEnd_2323280 := by exact prefixLift 2323280
  have htrace : WordTrace (prefixWord ++ tailWord_2323280) baseStart_2323280 baseEnd_2323280 := by
    simpa [prefixWord, tailWord_2323280, baseEnd_2323280] using wordTrace_append hprefix tailTrace_2323280
  have hstable : (prefixWord ++ tailWord_2323280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323280).length < 2 ^ (prefixWord ++ tailWord_2323280).sum := by decide
  have hdescent : baseEnd_2323280 < baseStart_2323280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323312 : List Nat := [2, 1, 1, 1, 4, 1, 2, 6, 4]
def baseStart_2323312 : Nat := 118140960795 + 2323312 * 2 ^ 59
def prefixEnd_2323312 : Nat := 4983230072969 + 3 ^ 40 * 2323312 * 2
def baseEnd_2323312 : Nat := 265105725857493169958953

theorem tailTrace_2323312 : CollatzResearch.WordTrace tailWord_2323312 prefixEnd_2323312 265105725857493169958953 := by
  unfold tailWord_2323312
  simp only [CollatzResearch.WordTrace]
  refine ⟨42369075079522444472318095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56492100106029925963090793 42369075079522444472318095)
  ·
    refine ⟨63553612619283666708477143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42369075079522444472318095 63553612619283666708477143)
    ·
      refine ⟨95330418928925500062715715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63553612619283666708477143 95330418928925500062715715)
      ·
        refine ⟨142995628393388250094073573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95330418928925500062715715 142995628393388250094073573)
        ·
          refine ⟨26811680323760296892638795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142995628393388250094073573 26811680323760296892638795)
          ·
            refine ⟨40217520485640445338958193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26811680323760296892638795 40217520485640445338958193)
            ·
              refine ⟨30163140364230334004218645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40217520485640445338958193 30163140364230334004218645)
              ·
                refine ⟨1413897204573296906447749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30163140364230334004218645 1413897204573296906447749)
                ·
                  refine ⟨265105725857493169958953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1413897204573296906447749 265105725857493169958953)
                  ·
                    rfl

theorem cell22_2323312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 4].length) (baseStart_2323312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323312 prefixEnd_2323312 := by exact prefixLift 2323312
  have htrace : WordTrace (prefixWord ++ tailWord_2323312) baseStart_2323312 baseEnd_2323312 := by
    simpa [prefixWord, tailWord_2323312, baseEnd_2323312] using wordTrace_append hprefix tailTrace_2323312
  have hstable : (prefixWord ++ tailWord_2323312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323312).length < 2 ^ (prefixWord ++ tailWord_2323312).sum := by decide
  have hdescent : baseEnd_2323312 < baseStart_2323312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323325 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_2323325 : Nat := 118140960795 + 2323325 * 2 ^ 59
def prefixEnd_2323325 : Nat := 4983230072969 + 3 ^ 40 * 2323325 * 2
def baseEnd_2323325 : Nat := 795321627738151809301819

theorem tailTrace_2323325 : CollatzResearch.WordTrace tailWord_2323325 prefixEnd_2323325 795321627738151809301819 := by
  unfold tailWord_2323325
  simp only [CollatzResearch.WordTrace]
  refine ⟨84738624307997792164859429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56492416205331861443239619 84738624307997792164859429)
  ·
    refine ⟨15888492057749586030911143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84738624307997792164859429 15888492057749586030911143)
    ·
      refine ⟨23832738086624379046366715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15888492057749586030911143 23832738086624379046366715)
      ·
        refine ⟨35749107129936568569550073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23832738086624379046366715 35749107129936568569550073)
        ·
          refine ⟨26811830347452426427162555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35749107129936568569550073 26811830347452426427162555)
          ·
            refine ⟨40217745521178639640743833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26811830347452426427162555 40217745521178639640743833)
            ·
              refine ⟨30163309140883979730557875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40217745521178639640743833 30163309140883979730557875)
              ·
                refine ⟨45244963711325969595836813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30163309140883979730557875 45244963711325969595836813)
                ·
                  refine ⟨16966861391747238598438805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45244963711325969595836813 16966861391747238598438805)
                  ·
                    refine ⟨795321627738151809301819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16966861391747238598438805 795321627738151809301819)
                    ·
                      rfl

theorem cell22_2323325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_2323325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323325 prefixEnd_2323325 := by exact prefixLift 2323325
  have htrace : WordTrace (prefixWord ++ tailWord_2323325) baseStart_2323325 baseEnd_2323325 := by
    simpa [prefixWord, tailWord_2323325, baseEnd_2323325] using wordTrace_append hprefix tailTrace_2323325
  have hstable : (prefixWord ++ tailWord_2323325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323325).length < 2 ^ (prefixWord ++ tailWord_2323325).sum := by decide
  have hdescent : baseEnd_2323325 < baseStart_2323325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323340 : List Nat := [2, 2, 1, 2, 1, 2, 4, 8]
def baseStart_2323340 : Nat := 118140960795 + 2323340 * 2 ^ 59
def prefixEnd_2323340 : Nat := 4983230072969 + 3 ^ 40 * 2323340 * 2
def baseEnd_2323340 : Nat := 88369640282744085575197

theorem tailTrace_2323340 : CollatzResearch.WordTrace tailWord_2323340 prefixEnd_2323340 88369640282744085575197 := by
  unfold tailWord_2323340
  simp only [CollatzResearch.WordTrace]
  refine ⟨42369585701471724863327737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56492780935295633151103649 42369585701471724863327737)
  ·
    refine ⟨31777189276103793647495803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42369585701471724863327737 31777189276103793647495803)
    ·
      refine ⟨47665783914155690471243705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31777189276103793647495803 47665783914155690471243705)
      ·
        refine ⟨35749337935616767853432779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47665783914155690471243705 35749337935616767853432779)
        ·
          refine ⟨53624006903425151780149169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35749337935616767853432779 53624006903425151780149169)
          ·
            refine ⟨40218005177568863835111877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53624006903425151780149169 40218005177568863835111877)
            ·
              refine ⟨7540875970794161969083477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40218005177568863835111877 7540875970794161969083477)
              ·
                refine ⟨88369640282744085575197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7540875970794161969083477 88369640282744085575197)
                ·
                  rfl

theorem cell22_2323340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 8].length) (baseStart_2323340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323340 prefixEnd_2323340 := by exact prefixLift 2323340
  have htrace : WordTrace (prefixWord ++ tailWord_2323340) baseStart_2323340 baseEnd_2323340 := by
    simpa [prefixWord, tailWord_2323340, baseEnd_2323340] using wordTrace_append hprefix tailTrace_2323340
  have hstable : (prefixWord ++ tailWord_2323340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323340).length < 2 ^ (prefixWord ++ tailWord_2323340).sum := by decide
  have hdescent : baseEnd_2323340 < baseStart_2323340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323361 : List Nat := [1, 2, 3, 4, 1, 2, 2, 2, 2, 3]
def baseStart_2323361 : Nat := 118140960795 + 2323361 * 2 ^ 59
def prefixEnd_2323361 : Nat := 4983230072969 + 3 ^ 40 * 2323361 * 2
def baseEnd_2323361 : Nat := 795333951273859715401709

theorem tailTrace_2323361 : CollatzResearch.WordTrace tailWord_2323361 prefixEnd_2323361 795333951273859715401709 := by
  unfold tailWord_2323361
  simp only [CollatzResearch.WordTrace]
  refine ⟨84739937335867370313169937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56493291557244913542113291 84739937335867370313169937)
  ·
    refine ⟨63554953001900527734877453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84739937335867370313169937 63554953001900527734877453)
    ·
      refine ⟨23833107375712697900579045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63554953001900527734877453 23833107375712697900579045)
      ·
        refine ⟨4468707632946130856358571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23833107375712697900579045 4468707632946130856358571)
        ·
          refine ⟨6703061449419196284537857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4468707632946130856358571 6703061449419196284537857)
          ·
            refine ⟨5027296087064397213403393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6703061449419196284537857 5027296087064397213403393)
            ·
              refine ⟨3770472065298297910052545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5027296087064397213403393 3770472065298297910052545)
              ·
                refine ⟨2827854048973723432539409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3770472065298297910052545 2827854048973723432539409)
                ·
                  refine ⟨2120890536730292574404557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2827854048973723432539409 2120890536730292574404557)
                  ·
                    refine ⟨795333951273859715401709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2120890536730292574404557 795333951273859715401709)
                    ·
                      rfl

theorem cell22_2323361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_2323361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323361 prefixEnd_2323361 := by exact prefixLift 2323361
  have htrace : WordTrace (prefixWord ++ tailWord_2323361) baseStart_2323361 baseEnd_2323361 := by
    simpa [prefixWord, tailWord_2323361, baseEnd_2323361] using wordTrace_append hprefix tailTrace_2323361
  have hstable : (prefixWord ++ tailWord_2323361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323361).length < 2 ^ (prefixWord ++ tailWord_2323361).sum := by decide
  have hdescent : baseEnd_2323361 < baseStart_2323361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323406 : List Nat := [4, 1, 1, 1, 2, 3, 1, 5, 1, 3]
def baseStart_2323406 : Nat := 118140960795 + 2323406 * 2 ^ 59
def prefixEnd_2323406 : Nat := 4983230072969 + 3 ^ 40 * 2323406 * 2
def baseEnd_2323406 : Nat := 795349355693494598026571

theorem tailTrace_2323406 : CollatzResearch.WordTrace tailWord_2323406 prefixEnd_2323406 795349355693494598026571 := by
  unfold tailWord_2323406
  simp only [CollatzResearch.WordTrace]
  refine ⟨10592697327588042874819759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56494385747136228665705381 10592697327588042874819759)
  ·
    refine ⟨15889045991382064312229639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10592697327588042874819759 15889045991382064312229639)
    ·
      refine ⟨23833568987073096468344459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15889045991382064312229639 23833568987073096468344459)
      ·
        refine ⟨35750353480609644702516689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23833568987073096468344459 35750353480609644702516689)
        ·
          refine ⟨26812765110457233526887517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35750353480609644702516689 26812765110457233526887517)
          ·
            refine ⟨10054786916421462572582819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26812765110457233526887517 10054786916421462572582819)
            ·
              refine ⟨15082180374632193858874229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10054786916421462572582819 15082180374632193858874229)
              ·
                refine ⟨1413954410121768174269459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15082180374632193858874229 1413954410121768174269459)
                ·
                  refine ⟨2120931615182652261404189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1413954410121768174269459 2120931615182652261404189)
                  ·
                    refine ⟨795349355693494598026571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2120931615182652261404189 795349355693494598026571)
                    ·
                      rfl

theorem cell22_2323406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_2323406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323406 prefixEnd_2323406 := by exact prefixLift 2323406
  have htrace : WordTrace (prefixWord ++ tailWord_2323406) baseStart_2323406 baseEnd_2323406 := by
    simpa [prefixWord, tailWord_2323406, baseEnd_2323406] using wordTrace_append hprefix tailTrace_2323406
  have hstable : (prefixWord ++ tailWord_2323406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323406).length < 2 ^ (prefixWord ++ tailWord_2323406).sum := by decide
  have hdescent : baseEnd_2323406 < baseStart_2323406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323417 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 2, 5]
def baseStart_2323417 : Nat := 118140960795 + 2323417 * 2 ^ 59
def prefixEnd_2323417 : Nat := 4983230072969 + 3 ^ 40 * 2323417 * 2
def baseEnd_2323417 : Nat := 795353121218294236001537

theorem tailTrace_2323417 : CollatzResearch.WordTrace tailWord_2323417 prefixEnd_2323417 795353121218294236001537 := by
  unfold tailWord_2323417
  simp only [CollatzResearch.WordTrace]
  refine ⟨84741979823664491877208505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56494653215776327918139003 84741979823664491877208505)
  ·
    refine ⟨63556484867748368907906379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84741979823664491877208505 63556484867748368907906379)
    ·
      refine ⟨95334727301622553361859569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63556484867748368907906379 95334727301622553361859569)
      ·
        refine ⟨71501045476216915021394677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95334727301622553361859569 71501045476216915021394677)
        ·
          refine ⟨6703223013395335783255751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71501045476216915021394677 6703223013395335783255751)
          ·
            refine ⟨10054834520093003674883627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6703223013395335783255751 10054834520093003674883627)
            ·
              refine ⟨15082251780139505512325441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10054834520093003674883627 15082251780139505512325441)
              ·
                refine ⟨11311688835104629134244081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15082251780139505512325441 11311688835104629134244081)
                ·
                  refine ⟨8483766626328471850683061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11311688835104629134244081 8483766626328471850683061)
                  ·
                    refine ⟨795353121218294236001537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8483766626328471850683061 795353121218294236001537)
                    ·
                      rfl

theorem cell22_2323417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_2323417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323417 prefixEnd_2323417 := by exact prefixLift 2323417
  have htrace : WordTrace (prefixWord ++ tailWord_2323417) baseStart_2323417 baseEnd_2323417 := by
    simpa [prefixWord, tailWord_2323417, baseEnd_2323417] using wordTrace_append hprefix tailTrace_2323417
  have hstable : (prefixWord ++ tailWord_2323417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323417).length < 2 ^ (prefixWord ++ tailWord_2323417).sum := by decide
  have hdescent : baseEnd_2323417 < baseStart_2323417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323432 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 5, 4]
def baseStart_2323432 : Nat := 118140960795 + 2323432 * 2 ^ 59
def prefixEnd_2323432 : Nat := 4983230072969 + 3 ^ 40 * 2323432 * 2
def baseEnd_2323432 : Nat := 795358256024839196876491

theorem tailTrace_2323432 : CollatzResearch.WordTrace tailWord_2323432 prefixEnd_2323432 795358256024839196876491 := by
  unfold tailWord_2323432
  simp only [CollatzResearch.WordTrace]
  refine ⟨42371263459305074719502275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56495017945740099626003033 42371263459305074719502275)
  ·
    refine ⟨63556895188957612079253413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42371263459305074719502275 63556895188957612079253413)
    ·
      refine ⟨11916917847929552264860015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63556895188957612079253413 11916917847929552264860015)
      ·
        refine ⟨17875376771894328397290023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11916917847929552264860015 17875376771894328397290023)
        ·
          refine ⟨26813065157841492595935035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17875376771894328397290023 26813065157841492595935035)
          ·
            refine ⟨40219597736762238893902553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26813065157841492595935035 40219597736762238893902553)
            ·
              refine ⟨30164698302571679170426915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40219597736762238893902553 30164698302571679170426915)
              ·
                refine ⟨45247047453857518755640373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30164698302571679170426915 45247047453857518755640373)
                ·
                  refine ⟨4241910698799142383341285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45247047453857518755640373 4241910698799142383341285)
                  ·
                    refine ⟨795358256024839196876491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4241910698799142383341285 795358256024839196876491)
                    ·
                      rfl

theorem cell22_2323432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_2323432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323432 prefixEnd_2323432 := by exact prefixLift 2323432
  have htrace : WordTrace (prefixWord ++ tailWord_2323432) baseStart_2323432 baseEnd_2323432 := by
    simpa [prefixWord, tailWord_2323432, baseEnd_2323432] using wordTrace_append hprefix tailTrace_2323432
  have hstable : (prefixWord ++ tailWord_2323432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323432).length < 2 ^ (prefixWord ++ tailWord_2323432).sum := by decide
  have hdescent : baseEnd_2323432 < baseStart_2323432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323449 : List Nat := [1, 2, 1, 3, 1, 3, 4, 2, 1, 4]
def baseStart_2323449 : Nat := 118140960795 + 2323449 * 2 ^ 59
def prefixEnd_2323449 : Nat := 4983230072969 + 3 ^ 40 * 2323449 * 2
def baseEnd_2323449 : Nat := 795364075472256819201439

theorem tailTrace_2323449 : CollatzResearch.WordTrace tailWord_2323449 prefixEnd_2323449 795364075472256819201439 := by
  unfold tailWord_2323449
  simp only [CollatzResearch.WordTrace]
  refine ⟨84743146959548561342373401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56495431306365707561582267 84743146959548561342373401)
  ·
    refine ⟨63557360219661421006780051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84743146959548561342373401 63557360219661421006780051)
    ·
      refine ⟨95336040329492131510170077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63557360219661421006780051 95336040329492131510170077)
      ·
        refine ⟨35751015123559549316313779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95336040329492131510170077 35751015123559549316313779)
        ·
          refine ⟨53626522685339323974470669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35751015123559549316313779 53626522685339323974470669)
          ·
            refine ⟨20109946007002246490426501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53626522685339323974470669 20109946007002246490426501)
            ·
              refine ⟨3770614876312921216954969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20109946007002246490426501 3770614876312921216954969)
              ·
                refine ⟨2827961157234690912716227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3770614876312921216954969 2827961157234690912716227)
                ·
                  refine ⟨4241941735852036369074341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2827961157234690912716227 4241941735852036369074341)
                  ·
                    refine ⟨795364075472256819201439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4241941735852036369074341 795364075472256819201439)
                    ·
                      rfl

theorem cell22_2323449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 4].length) (baseStart_2323449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323449 prefixEnd_2323449 := by exact prefixLift 2323449
  have htrace : WordTrace (prefixWord ++ tailWord_2323449) baseStart_2323449 baseEnd_2323449 := by
    simpa [prefixWord, tailWord_2323449, baseEnd_2323449] using wordTrace_append hprefix tailTrace_2323449
  have hstable : (prefixWord ++ tailWord_2323449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323449).length < 2 ^ (prefixWord ++ tailWord_2323449).sum := by decide
  have hdescent : baseEnd_2323449 < baseStart_2323449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323474 : List Nat := [3, 2, 5, 1, 1, 1, 3, 2, 1, 3]
def baseStart_2323474 : Nat := 118140960795 + 2323474 * 2 ^ 59
def prefixEnd_2323474 : Nat := 4983230072969 + 3 ^ 40 * 2323474 * 2
def baseEnd_2323474 : Nat := 795372633483165087326363

theorem tailTrace_2323474 : CollatzResearch.WordTrace tailWord_2323474 prefixEnd_2323474 795372633483165087326363 := by
  unfold tailWord_2323474
  simp only [CollatzResearch.WordTrace]
  refine ⟨21186014696114497653008369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56496039189638660408022317 21186014696114497653008369)
  ·
    refine ⟨15889511022085873239756277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21186014696114497653008369 15889511022085873239756277)
    ·
      refine ⟨1489641658320550616227151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15889511022085873239756277 1489641658320550616227151)
      ·
        refine ⟨2234462487480825924340727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1489641658320550616227151 2234462487480825924340727)
        ·
          refine ⟨3351693731221238886511091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2234462487480825924340727 3351693731221238886511091)
          ·
            refine ⟨5027540596831858329766637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3351693731221238886511091 5027540596831858329766637)
            ·
              refine ⟨1885327723811946873662489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5027540596831858329766637 1885327723811946873662489)
              ·
                refine ⟨1413995792858960155246867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1885327723811946873662489 1413995792858960155246867)
                ·
                  refine ⟨2120993689288440232870301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1413995792858960155246867 2120993689288440232870301)
                  ·
                    refine ⟨795372633483165087326363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2120993689288440232870301 795372633483165087326363)
                    ·
                      rfl

theorem cell22_2323474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_2323474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323474 prefixEnd_2323474 := by exact prefixLift 2323474
  have htrace : WordTrace (prefixWord ++ tailWord_2323474) baseStart_2323474 baseEnd_2323474 := by
    simpa [prefixWord, tailWord_2323474, baseEnd_2323474] using wordTrace_append hprefix tailTrace_2323474
  have hstable : (prefixWord ++ tailWord_2323474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323474).length < 2 ^ (prefixWord ++ tailWord_2323474).sum := by decide
  have hdescent : baseEnd_2323474 < baseStart_2323474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323537 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 7]
def baseStart_2323537 : Nat := 118140960795 + 2323537 * 2 ^ 59
def prefixEnd_2323537 : Nat := 4983230072969 + 3 ^ 40 * 2323537 * 2
def baseEnd_2323537 : Nat := 265131399890217974333723

theorem tailTrace_2323537 : CollatzResearch.WordTrace tailWord_2323537 prefixEnd_2323537 265131399890217974333723 := by
  unfold tailWord_2323537
  simp only [CollatzResearch.WordTrace]
  refine ⟨84746356583229752371576865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56497571055486501581051243 84746356583229752371576865)
  ·
    refine ⟨63559767437422314278682649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84746356583229752371576865 63559767437422314278682649)
    ·
      refine ⟨47669825578066735709011987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63559767437422314278682649 47669825578066735709011987)
      ·
        refine ⟨71504738367100103563517981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47669825578066735709011987 71504738367100103563517981)
        ·
          refine ⟨26814276887662538836319243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71504738367100103563517981 26814276887662538836319243)
          ·
            refine ⟨40221415331493808254478865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26814276887662538836319243 40221415331493808254478865)
            ·
              refine ⟨30166061498620356190859149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40221415331493808254478865 30166061498620356190859149)
              ·
                refine ⟨11312273061982633571572181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30166061498620356190859149 11312273061982633571572181)
                ·
                  refine ⟨265131399890217974333723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11312273061982633571572181 265131399890217974333723)
                  ·
                    rfl

theorem cell22_2323537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 7].length) (baseStart_2323537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323537 prefixEnd_2323537 := by exact prefixLift 2323537
  have htrace : WordTrace (prefixWord ++ tailWord_2323537) baseStart_2323537 baseEnd_2323537 := by
    simpa [prefixWord, tailWord_2323537, baseEnd_2323537] using wordTrace_append hprefix tailTrace_2323537
  have hstable : (prefixWord ++ tailWord_2323537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323537).length < 2 ^ (prefixWord ++ tailWord_2323537).sum := by decide
  have hdescent : baseEnd_2323537 < baseStart_2323537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323633 : List Nat := [1, 2, 2, 5, 1, 1, 3, 3, 4]
def baseStart_2323633 : Nat := 118140960795 + 2323633 * 2 ^ 59
def prefixEnd_2323633 : Nat := 4983230072969 + 3 ^ 40 * 2323633 * 2
def baseEnd_2323633 : Nat := 265142354144180557533625

theorem tailTrace_2323633 : CollatzResearch.WordTrace tailWord_2323633 prefixEnd_2323633 265142354144180557533625 := by
  unfold tailWord_2323633
  simp only [CollatzResearch.WordTrace]
  refine ⟨84749857990881960767071553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56499905327254640511381035 84749857990881960767071553)
  ·
    refine ⟨63562393493161470575303665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84749857990881960767071553 63562393493161470575303665)
    ·
      refine ⟨47671795119871102931477749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63562393493161470575303665 47671795119871102931477749)
      ·
        refine ⟨4469230792487915899826039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47671795119871102931477749 4469230792487915899826039)
        ·
          refine ⟨6703846188731873849739059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4469230792487915899826039 6703846188731873849739059)
          ·
            refine ⟨10055769283097810774608589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6703846188731873849739059 10055769283097810774608589)
            ·
              refine ⟨3770913481161679040478221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10055769283097810774608589 3770913481161679040478221)
              ·
                refine ⟨1414092555435629640179333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3770913481161679040478221 1414092555435629640179333)
                ·
                  refine ⟨265142354144180557533625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1414092555435629640179333 265142354144180557533625)
                  ·
                    rfl

theorem cell22_2323633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 4].length) (baseStart_2323633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323633 prefixEnd_2323633 := by exact prefixLift 2323633
  have htrace : WordTrace (prefixWord ++ tailWord_2323633) baseStart_2323633 baseEnd_2323633 := by
    simpa [prefixWord, tailWord_2323633, baseEnd_2323633] using wordTrace_append hprefix tailTrace_2323633
  have hstable : (prefixWord ++ tailWord_2323633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323633).length < 2 ^ (prefixWord ++ tailWord_2323633).sum := by decide
  have hdescent : baseEnd_2323633 < baseStart_2323633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323644 : List Nat := [2, 2, 2, 3, 2, 1, 10]
def baseStart_2323644 : Nat := 118140960795 + 2323644 * 2 ^ 59
def prefixEnd_2323644 : Nat := 4983230072969 + 3 ^ 40 * 2323644 * 2
def baseEnd_2323644 : Nat := 29460401035457085576883

theorem tailTrace_2323644 : CollatzResearch.WordTrace tailWord_2323644 prefixEnd_2323644 29460401035457085576883 := by
  unfold tailWord_2323644
  simp only [CollatzResearch.WordTrace]
  refine ⟨42375129596921054822860993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56500172795894739763814657 42375129596921054822860993)
  ·
    refine ⟨31781347197690791117145745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42375129596921054822860993 31781347197690791117145745)
    ·
      refine ⟨23836010398268093337859309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31781347197690791117145745 23836010398268093337859309)
      ·
        refine ⟨8938503899350535001697241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23836010398268093337859309 8938503899350535001697241)
        ·
          refine ⟨6703877924512901251272931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8938503899350535001697241 6703877924512901251272931)
          ·
            refine ⟨10055816886769351876909397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6703877924512901251272931 10055816886769351876909397)
            ·
              refine ⟨29460401035457085576883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10055816886769351876909397 29460401035457085576883)
              ·
                rfl

theorem cell22_2323644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 10].length) (baseStart_2323644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323644 prefixEnd_2323644 := by exact prefixLift 2323644
  have htrace : WordTrace (prefixWord ++ tailWord_2323644) baseStart_2323644 baseEnd_2323644 := by
    simpa [prefixWord, tailWord_2323644, baseEnd_2323644] using wordTrace_append hprefix tailTrace_2323644
  have hstable : (prefixWord ++ tailWord_2323644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323644).length < 2 ^ (prefixWord ++ tailWord_2323644).sum := by decide
  have hdescent : baseEnd_2323644 < baseStart_2323644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323646 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_2323646 : Nat := 118140960795 + 2323646 * 2 ^ 59
def prefixEnd_2323646 : Nat := 4983230072969 + 3 ^ 40 * 2323646 * 2
def baseEnd_2323646 : Nat := 795431512598213972025835

theorem tailTrace_2323646 : CollatzResearch.WordTrace tailWord_2323646 prefixEnd_2323646 795431512598213972025835 := by
  unfold tailWord_2323646
  simp only [CollatzResearch.WordTrace]
  refine ⟨10593791517479357998411849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56500221426556575991529861 10593791517479357998411849)
  ·
    refine ⟨7945343638109518498808887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10593791517479357998411849 7945343638109518498808887)
    ·
      refine ⟨11918015457164277748213331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7945343638109518498808887 11918015457164277748213331)
      ·
        refine ⟨17877023185746416622319997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11918015457164277748213331 17877023185746416622319997)
        ·
          refine ⟨6703883694654906233369999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17877023185746416622319997 6703883694654906233369999)
          ·
            refine ⟨10055825541982359350054999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6703883694654906233369999 10055825541982359350054999)
            ·
              refine ⟨15083738312973539025082499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10055825541982359350054999 15083738312973539025082499)
              ·
                refine ⟨22625607469460308537623749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15083738312973539025082499 22625607469460308537623749)
                ·
                  refine ⟨4242301400523807850804453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22625607469460308537623749 4242301400523807850804453)
                  ·
                    refine ⟨795431512598213972025835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4242301400523807850804453 795431512598213972025835)
                    ·
                      rfl

theorem cell22_2323646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_2323646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323646 prefixEnd_2323646 := by exact prefixLift 2323646
  have htrace : WordTrace (prefixWord ++ tailWord_2323646) baseStart_2323646 baseEnd_2323646 := by
    simpa [prefixWord, tailWord_2323646, baseEnd_2323646] using wordTrace_append hprefix tailTrace_2323646
  have hstable : (prefixWord ++ tailWord_2323646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323646).length < 2 ^ (prefixWord ++ tailWord_2323646).sum := by decide
  have hdescent : baseEnd_2323646 < baseStart_2323646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323706 : List Nat := [3, 1, 1, 1, 1, 4, 4, 2, 5]
def baseStart_2323706 : Nat := 118140960795 + 2323706 * 2 ^ 59
def prefixEnd_2323706 : Nat := 4983230072969 + 3 ^ 40 * 2323706 * 2
def baseEnd_2323706 : Nat := 265150683941464605175217

theorem tailTrace_2323706 : CollatzResearch.WordTrace tailWord_2323706 prefixEnd_2323706 265150683941464605175217 := by
  unfold tailWord_2323706
  simp only [CollatzResearch.WordTrace]
  refine ⟨21188130129904373558619743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56501680346411662822985981 21188130129904373558619743)
  ·
    refine ⟨31782195194856560337929615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21188130129904373558619743 31782195194856560337929615)
    ·
      refine ⟨47673292792284840506894423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31782195194856560337929615 47673292792284840506894423)
      ·
        refine ⟨71509939188427260760341635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47673292792284840506894423 71509939188427260760341635)
        ·
          refine ⟨107264908782640891140512453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71509939188427260760341635 107264908782640891140512453)
          ·
            refine ⟨20112170396745167088846085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107264908782640891140512453 20112170396745167088846085)
            ·
              refine ⟨3771031949389718829158641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20112170396745167088846085 3771031949389718829158641)
              ·
                refine ⟨2828273962042289121868981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3771031949389718829158641 2828273962042289121868981)
                ·
                  refine ⟨265150683941464605175217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2828273962042289121868981 265150683941464605175217)
                  ·
                    rfl

theorem cell22_2323706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_2323706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323706 prefixEnd_2323706 := by exact prefixLift 2323706
  have htrace : WordTrace (prefixWord ++ tailWord_2323706) baseStart_2323706 baseEnd_2323706 := by
    simpa [prefixWord, tailWord_2323706, baseEnd_2323706] using wordTrace_append hprefix tailTrace_2323706
  have hstable : (prefixWord ++ tailWord_2323706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323706).length < 2 ^ (prefixWord ++ tailWord_2323706).sum := by decide
  have hdescent : baseEnd_2323706 < baseStart_2323706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323736 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 3, 4]
def baseStart_2323736 : Nat := 118140960795 + 2323736 * 2 ^ 59
def prefixEnd_2323736 : Nat := 4983230072969 + 3 ^ 40 * 2323736 * 2
def baseEnd_2323736 : Nat := 795462321437483737275559

theorem tailTrace_2323736 : CollatzResearch.WordTrace tailWord_2323736 prefixEnd_2323736 795462321437483737275559 := by
  unfold tailWord_2323736
  simp only [CollatzResearch.WordTrace]
  refine ⟨42376807354754404679035531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56502409806339206238714041 42376807354754404679035531)
  ·
    refine ⟨63565211032131607018553297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42376807354754404679035531 63565211032131607018553297)
    ·
      refine ⟨47673908274098705263914973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63565211032131607018553297 47673908274098705263914973)
      ·
        refine ⟨17877715602787014473968115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47673908274098705263914973 17877715602787014473968115)
        ·
          refine ⟨26816573404180521710952173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17877715602787014473968115 26816573404180521710952173)
          ·
            refine ⟨10056215026567695641607065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26816573404180521710952173 10056215026567695641607065)
            ·
              refine ⟨7542161269925771731205299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10056215026567695641607065 7542161269925771731205299)
              ·
                refine ⟨11313241904888657596807949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7542161269925771731205299 11313241904888657596807949)
                ·
                  refine ⟨4242465714333246598802981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11313241904888657596807949 4242465714333246598802981)
                  ·
                    refine ⟨795462321437483737275559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4242465714333246598802981 795462321437483737275559)
                    ·
                      rfl

theorem cell22_2323736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_2323736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323736 prefixEnd_2323736 := by exact prefixLift 2323736
  have htrace : WordTrace (prefixWord ++ tailWord_2323736) baseStart_2323736 baseEnd_2323736 := by
    simpa [prefixWord, tailWord_2323736, baseEnd_2323736] using wordTrace_append hprefix tailTrace_2323736
  have hstable : (prefixWord ++ tailWord_2323736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323736).length < 2 ^ (prefixWord ++ tailWord_2323736).sum := by decide
  have hdescent : baseEnd_2323736 < baseStart_2323736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323779 : List Nat := [1, 1, 1, 3, 1, 3, 1, 11]
def baseStart_2323779 : Nat := 118140960795 + 2323779 * 2 ^ 59
def prefixEnd_2323779 : Nat := 4983230072969 + 3 ^ 40 * 2323779 * 2
def baseEnd_2323779 : Nat := 88386337912916217605603

theorem tailTrace_2323779 : CollatzResearch.WordTrace tailWord_2323779 prefixEnd_2323779 88386337912916217605603 := by
  unfold tailWord_2323779
  simp only [CollatzResearch.WordTrace]
  refine ⟨84755183048353027701886391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56503455365568685134590927 84755183048353027701886391)
  ·
    refine ⟨127132774572529541552829587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84755183048353027701886391 127132774572529541552829587)
    ·
      refine ⟨190699161858794312329244381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127132774572529541552829587 190699161858794312329244381)
      ·
        refine ⟨71512185697047867123466643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190699161858794312329244381 71512185697047867123466643)
        ·
          refine ⟨107268278545571800685199965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71512185697047867123466643 107268278545571800685199965)
          ·
            refine ⟨40225604454589425256949987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107268278545571800685199965 40225604454589425256949987)
            ·
              refine ⟨60338406681884137885424981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40225604454589425256949987 60338406681884137885424981)
              ·
                refine ⟨88386337912916217605603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 60338406681884137885424981 88386337912916217605603)
                ·
                  rfl

theorem cell22_2323779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 11].length) (baseStart_2323779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323779 prefixEnd_2323779 := by exact prefixLift 2323779
  have htrace : WordTrace (prefixWord ++ tailWord_2323779) baseStart_2323779 baseEnd_2323779 := by
    simpa [prefixWord, tailWord_2323779, baseEnd_2323779] using wordTrace_append hprefix tailTrace_2323779
  have hstable : (prefixWord ++ tailWord_2323779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323779).length < 2 ^ (prefixWord ++ tailWord_2323779).sum := by decide
  have hdescent : baseEnd_2323779 < baseStart_2323779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323783 : List Nat := [1, 1, 4, 1, 2, 5, 1, 1, 1, 5]
def baseStart_2323783 : Nat := 118140960795 + 2323783 * 2 ^ 59
def prefixEnd_2323783 : Nat := 4983230072969 + 3 ^ 40 * 2323783 * 2
def baseEnd_2323783 : Nat := 795478410497991281350415

theorem tailTrace_2323783 : CollatzResearch.WordTrace tailWord_2323783 prefixEnd_2323783 795478410497991281350415 := by
  unfold tailWord_2323783
  simp only [CollatzResearch.WordTrace]
  refine ⟨84755328940338536385032003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56503552626892357590021335 84755328940338536385032003)
  ·
    refine ⟨127132993410507804577548005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84755328940338536385032003 127132993410507804577548005)
    ·
      refine ⟨23837436264470213358290251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127132993410507804577548005 23837436264470213358290251)
      ·
        refine ⟨35756154396705320037435377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23837436264470213358290251 35756154396705320037435377)
        ·
          refine ⟨26817115797528990028076533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35756154396705320037435377 26817115797528990028076533)
          ·
            refine ⟨2514104606018342815132175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26817115797528990028076533 2514104606018342815132175)
            ·
              refine ⟨3771156909027514222698263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2514104606018342815132175 3771156909027514222698263)
              ·
                refine ⟨5656735363541271334047395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3771156909027514222698263 5656735363541271334047395)
                ·
                  refine ⟨8485103045311907001071093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5656735363541271334047395 8485103045311907001071093)
                  ·
                    refine ⟨795478410497991281350415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8485103045311907001071093 795478410497991281350415)
                    ·
                      rfl

theorem cell22_2323783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_2323783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323783 prefixEnd_2323783 := by exact prefixLift 2323783
  have htrace : WordTrace (prefixWord ++ tailWord_2323783) baseStart_2323783 baseEnd_2323783 := by
    simpa [prefixWord, tailWord_2323783, baseEnd_2323783] using wordTrace_append hprefix tailTrace_2323783
  have hstable : (prefixWord ++ tailWord_2323783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323783).length < 2 ^ (prefixWord ++ tailWord_2323783).sum := by decide
  have hdescent : baseEnd_2323783 < baseStart_2323783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323796 : List Nat := [2, 4, 1, 1, 2, 1, 3, 8]
def baseStart_2323796 : Nat := 118140960795 + 2323796 * 2 ^ 59
def prefixEnd_2323796 : Nat := 4983230072969 + 3 ^ 40 * 2323796 * 2
def baseEnd_2323796 : Nat := 88386984518184842308375

theorem tailTrace_2323796 : CollatzResearch.WordTrace tailWord_2323796 prefixEnd_2323796 88386984518184842308375 := by
  unfold tailWord_2323796
  simp only [CollatzResearch.WordTrace]
  refine ⟨42377901544645719802627621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56503868726194293070170161 42377901544645719802627621)
  ·
    refine ⟨7945856539621072462992679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42377901544645719802627621 7945856539621072462992679)
    ·
      refine ⟨11918784809431608694489019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7945856539621072462992679 11918784809431608694489019)
      ·
        refine ⟨17878177214147413041733529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11918784809431608694489019 17878177214147413041733529)
        ·
          refine ⟨13408632910610559781300147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17878177214147413041733529 13408632910610559781300147)
          ·
            refine ⟨20112949365915839671950221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13408632910610559781300147 20112949365915839671950221)
            ·
              refine ⟨7542356012218439876981333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20112949365915839671950221 7542356012218439876981333)
              ·
                refine ⟨88386984518184842308375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7542356012218439876981333 88386984518184842308375)
                ·
                  rfl

theorem cell22_2323796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 8].length) (baseStart_2323796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323796 prefixEnd_2323796 := by exact prefixLift 2323796
  have htrace : WordTrace (prefixWord ++ tailWord_2323796) baseStart_2323796 baseEnd_2323796 := by
    simpa [prefixWord, tailWord_2323796, baseEnd_2323796] using wordTrace_append hprefix tailTrace_2323796
  have hstable : (prefixWord ++ tailWord_2323796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323796).length < 2 ^ (prefixWord ++ tailWord_2323796).sum := by decide
  have hdescent : baseEnd_2323796 < baseStart_2323796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323826 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_2323826 : Nat := 118140960795 + 2323826 * 2 ^ 59
def prefixEnd_2323826 : Nat := 4983230072969 + 3 ^ 40 * 2323826 * 2
def baseEnd_2323826 : Nat := 795493130276753502525283

theorem tailTrace_2323826 : CollatzResearch.WordTrace tailWord_2323826 prefixEnd_2323826 795493130276753502525283 := by
  unfold tailWord_2323826
  simp only [CollatzResearch.WordTrace]
  refine ⟨21189224319795688682211833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56504598186121836485898221 21189224319795688682211833)
  ·
    refine ⟨15891918239846766511658875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21189224319795688682211833 15891918239846766511658875)
    ·
      refine ⟨23837877359770149767488313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15891918239846766511658875 23837877359770149767488313)
      ·
        refine ⟨17878408019827612325616235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23837877359770149767488313 17878408019827612325616235)
        ·
          refine ⟨26817612029741418488424353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17878408019827612325616235 26817612029741418488424353)
          ·
            refine ⟨20113209022306063866318265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26817612029741418488424353 20113209022306063866318265)
            ·
              refine ⟨15084906766729547899738699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20113209022306063866318265 15084906766729547899738699)
              ·
                refine ⟨22627360150094321849608049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15084906766729547899738699 22627360150094321849608049)
                ·
                  refine ⟨16970520112570741387206037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22627360150094321849608049 16970520112570741387206037)
                  ·
                    refine ⟨795493130276753502525283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16970520112570741387206037 795493130276753502525283)
                    ·
                      rfl

theorem cell22_2323826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_2323826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323826 prefixEnd_2323826 := by exact prefixLift 2323826
  have htrace : WordTrace (prefixWord ++ tailWord_2323826) baseStart_2323826 baseEnd_2323826 := by
    simpa [prefixWord, tailWord_2323826, baseEnd_2323826] using wordTrace_append hprefix tailTrace_2323826
  have hstable : (prefixWord ++ tailWord_2323826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323826).length < 2 ^ (prefixWord ++ tailWord_2323826).sum := by decide
  have hdescent : baseEnd_2323826 < baseStart_2323826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323918 : List Nat := [4, 1, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_2323918 : Nat := 118140960795 + 2323918 * 2 ^ 59
def prefixEnd_2323918 : Nat := 4983230072969 + 3 ^ 40 * 2323918 * 2
def baseEnd_2323918 : Nat := 795524623756895929225001

theorem tailTrace_2323918 : CollatzResearch.WordTrace tailWord_2323918 prefixEnd_2323918 795524623756895929225001 := by
  unfold tailWord_2323918
  simp only [CollatzResearch.WordTrace]
  refine ⟨10595031599356181805149551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56506835196566302960797605 10595031599356181805149551)
  ·
    refine ⟨15892547399034272707724327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10595031599356181805149551 15892547399034272707724327)
    ·
      refine ⟨23838821098551409061586491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15892547399034272707724327 23838821098551409061586491)
      ·
        refine ⟨35758231647827113592379737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23838821098551409061586491 35758231647827113592379737)
        ·
          refine ⟨26818673735870335194284803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35758231647827113592379737 26818673735870335194284803)
          ·
            refine ⟨40228010603805502791427205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26818673735870335194284803 40228010603805502791427205)
            ·
              refine ⟨7542751988213531773392601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40228010603805502791427205 7542751988213531773392601)
              ·
                refine ⟨5657063991160148830044451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7542751988213531773392601 5657063991160148830044451)
                ·
                  refine ⟨8485595986740223245066677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5657063991160148830044451 8485595986740223245066677)
                  ·
                    refine ⟨795524623756895929225001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8485595986740223245066677 795524623756895929225001)
                    ·
                      rfl

theorem cell22_2323918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_2323918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323918 prefixEnd_2323918 := by exact prefixLift 2323918
  have htrace : WordTrace (prefixWord ++ tailWord_2323918) baseStart_2323918 baseEnd_2323918 := by
    simpa [prefixWord, tailWord_2323918, baseEnd_2323918] using wordTrace_append hprefix tailTrace_2323918
  have hstable : (prefixWord ++ tailWord_2323918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323918).length < 2 ^ (prefixWord ++ tailWord_2323918).sum := by decide
  have hdescent : baseEnd_2323918 < baseStart_2323918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323952 : List Nat := [2, 1, 1, 1, 3, 5, 3, 1, 2, 3]
def baseStart_2323952 : Nat := 118140960795 + 2323952 * 2 ^ 59
def prefixEnd_2323952 : Nat := 4983230072969 + 3 ^ 40 * 2323952 * 2
def baseEnd_2323952 : Nat := 795536262651731173874897

theorem tailTrace_2323952 : CollatzResearch.WordTrace tailWord_2323952 prefixEnd_2323952 795536262651731173874897 := by
  unfold tailWord_2323952
  simp only [CollatzResearch.WordTrace]
  refine ⟨42380746438363139123967055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56507661917817518831956073 42380746438363139123967055)
  ·
    refine ⟨63571119657544708685950583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42380746438363139123967055 63571119657544708685950583)
    ·
      refine ⟨95356679486317063028925875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63571119657544708685950583 95356679486317063028925875)
      ·
        refine ⟨143035019229475594543388813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95356679486317063028925875 143035019229475594543388813)
        ·
          refine ⟨53638132211053347953770805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143035019229475594543388813 53638132211053347953770805)
          ·
            refine ⟨5028574894786251370666013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53638132211053347953770805 5028574894786251370666013)
            ·
              refine ⟨1885715585544844263999755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5028574894786251370666013 1885715585544844263999755)
              ·
                refine ⟨2828573378317266395999633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1885715585544844263999755 2828573378317266395999633)
                ·
                  refine ⟨2121430033737949796999725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2828573378317266395999633 2121430033737949796999725)
                  ·
                    refine ⟨795536262651731173874897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2121430033737949796999725 795536262651731173874897)
                    ·
                      rfl

theorem cell22_2323952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 2, 3].length) (baseStart_2323952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323952 prefixEnd_2323952 := by exact prefixLift 2323952
  have htrace : WordTrace (prefixWord ++ tailWord_2323952) baseStart_2323952 baseEnd_2323952 := by
    simpa [prefixWord, tailWord_2323952, baseEnd_2323952] using wordTrace_append hprefix tailTrace_2323952
  have hstable : (prefixWord ++ tailWord_2323952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323952).length < 2 ^ (prefixWord ++ tailWord_2323952).sum := by decide
  have hdescent : baseEnd_2323952 < baseStart_2323952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323965 : List Nat := [1, 4, 1, 1, 1, 6, 2, 6]
def baseStart_2323965 : Nat := 118140960795 + 2323965 * 2 ^ 59
def prefixEnd_2323965 : Nat := 4983230072969 + 3 ^ 40 * 2323965 * 2
def baseEnd_2323965 : Nat := 88393412535267052588873

theorem tailTrace_2323965 : CollatzResearch.WordTrace tailWord_2323965 prefixEnd_2323965 88393412535267052588873 := by
  unfold tailWord_2323965
  simp only [CollatzResearch.WordTrace]
  refine ⟨84761967025679181468157349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56507978017119454312104899 84761967025679181468157349)
  ·
    refine ⟨15892868817314846525279503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84761967025679181468157349 15892868817314846525279503)
    ·
      refine ⟨23839303225972269787919255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15892868817314846525279503 23839303225972269787919255)
      ·
        refine ⟨35758954838958404681878883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23839303225972269787919255 35758954838958404681878883)
        ·
          refine ⟨53638432258437607022818325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35758954838958404681878883 53638432258437607022818325)
          ·
            refine ⟨2514301512114262829194609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53638432258437607022818325 2514301512114262829194609)
            ·
              refine ⟨1885726134085697121895957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2514301512114262829194609 1885726134085697121895957)
              ·
                refine ⟨88393412535267052588873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1885726134085697121895957 88393412535267052588873)
                ·
                  rfl

theorem cell22_2323965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 6].length) (baseStart_2323965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2323965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2323965 prefixEnd_2323965 := by exact prefixLift 2323965
  have htrace : WordTrace (prefixWord ++ tailWord_2323965) baseStart_2323965 baseEnd_2323965 := by
    simpa [prefixWord, tailWord_2323965, baseEnd_2323965] using wordTrace_append hprefix tailTrace_2323965
  have hstable : (prefixWord ++ tailWord_2323965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323965).length < 2 ^ (prefixWord ++ tailWord_2323965).sum := by decide
  have hdescent : baseEnd_2323965 < baseStart_2323965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324010 : List Nat := [3, 1, 4, 1, 1, 1, 3, 3, 5]
def baseStart_2324010 : Nat := 118140960795 + 2324010 * 2 ^ 59
def prefixEnd_2324010 : Nat := 4983230072969 + 3 ^ 40 * 2324010 * 2
def baseEnd_2324010 : Nat := 265185372412346118641573

theorem tailTrace_2324010 : CollatzResearch.WordTrace tailWord_2324010 prefixEnd_2324010 265185372412346118641573 := by
  unfold tailWord_2324010
  simp only [CollatzResearch.WordTrace]
  refine ⟨21190902077629038538386371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56509072207010769435696989 21190902077629038538386371)
  ·
    refine ⟨31786353116443557807579557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21190902077629038538386371 31786353116443557807579557)
    ·
      refine ⟨5959941209333167088921167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31786353116443557807579557 5959941209333167088921167)
      ·
        refine ⟨8939911813999750633381751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5959941209333167088921167 8939911813999750633381751)
        ·
          refine ⟨13409867720999625950072627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8939911813999750633381751 13409867720999625950072627)
          ·
            refine ⟨20114801581499438925108941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13409867720999625950072627 20114801581499438925108941)
            ·
              refine ⟨7543050593062289596915853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20114801581499438925108941 7543050593062289596915853)
              ·
                refine ⟨2828643972398358598843445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7543050593062289596915853 2828643972398358598843445)
                ·
                  refine ⟨265185372412346118641573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2828643972398358598843445 265185372412346118641573)
                  ·
                    rfl

theorem cell22_2324010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_2324010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324010 prefixEnd_2324010 := by exact prefixLift 2324010
  have htrace : WordTrace (prefixWord ++ tailWord_2324010) baseStart_2324010 baseEnd_2324010 := by
    simpa [prefixWord, tailWord_2324010, baseEnd_2324010] using wordTrace_append hprefix tailTrace_2324010
  have hstable : (prefixWord ++ tailWord_2324010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324010).length < 2 ^ (prefixWord ++ tailWord_2324010).sum := by decide
  have hdescent : baseEnd_2324010 < baseStart_2324010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324053 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 5, 5]
def baseStart_2324053 : Nat := 118140960795 + 2324053 * 2 ^ 59
def prefixEnd_2324053 : Nat := 4983230072969 + 3 ^ 40 * 2324053 * 2
def baseEnd_2324053 : Nat := 795570837015800577099587

theorem tailTrace_2324053 : CollatzResearch.WordTrace tailWord_2324053 prefixEnd_2324053 795570837015800577099587 := by
  unfold tailWord_2324053
  simp only [CollatzResearch.WordTrace]
  refine ⟨84765176649360372497360813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56510117766240248331573875 84765176649360372497360813)
  ·
    refine ⟨31786941243510139686510305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84765176649360372497360813 31786941243510139686510305)
    ·
      refine ⟨23840205932632604764882729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31786941243510139686510305 23840205932632604764882729)
      ·
        refine ⟨17880154449474453573662047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23840205932632604764882729 17880154449474453573662047)
        ·
          refine ⟨26820231674211680360493071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17880154449474453573662047 26820231674211680360493071)
          ·
            refine ⟨40230347511317520540739607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26820231674211680360493071 40230347511317520540739607)
            ·
              refine ⟨60345521266976280811109411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40230347511317520540739607 60345521266976280811109411)
              ·
                refine ⟨90518281900464421216664117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60345521266976280811109411 90518281900464421216664117)
                ·
                  refine ⟨8486088928168539489062261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90518281900464421216664117 8486088928168539489062261)
                  ·
                    refine ⟨795570837015800577099587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8486088928168539489062261 795570837015800577099587)
                    ·
                      rfl

theorem cell22_2324053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_2324053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324053 prefixEnd_2324053 := by exact prefixLift 2324053
  have htrace : WordTrace (prefixWord ++ tailWord_2324053) baseStart_2324053 baseEnd_2324053 := by
    simpa [prefixWord, tailWord_2324053, baseEnd_2324053] using wordTrace_append hprefix tailTrace_2324053
  have hstable : (prefixWord ++ tailWord_2324053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324053).length < 2 ^ (prefixWord ++ tailWord_2324053).sum := by decide
  have hdescent : baseEnd_2324053 < baseStart_2324053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324100 : List Nat := [2, 3, 2, 1, 4, 1, 9]
def baseStart_2324100 : Nat := 118140960795 + 2324100 * 2 ^ 59
def prefixEnd_2324100 : Nat := 4983230072969 + 3 ^ 40 * 2324100 * 2
def baseEnd_2324100 : Nat := 29466182447270671154609

theorem tailTrace_2324100 : CollatzResearch.WordTrace tailWord_2324100 prefixEnd_2324100 29466182447270671154609 := by
  unfold tailWord_2324100
  simp only [CollatzResearch.WordTrace]
  refine ⟨42383445440095049762160877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56511260586793399682881169 42383445440095049762160877)
  ·
    refine ⟨15893792040035643660810329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42383445440095049762160877 15893792040035643660810329)
    ·
      refine ⟨11920344030026732745607747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15893792040035643660810329 11920344030026732745607747)
      ·
        refine ⟨17880516045040099118411621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11920344030026732745607747 17880516045040099118411621)
        ·
          refine ⟨3352596758445018584702179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17880516045040099118411621 3352596758445018584702179)
          ·
            refine ⟨5028895137667527877053269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3352596758445018584702179 5028895137667527877053269)
            ·
              refine ⟨29466182447270671154609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5028895137667527877053269 29466182447270671154609)
              ·
                rfl

theorem cell22_2324100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 9].length) (baseStart_2324100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324100 prefixEnd_2324100 := by exact prefixLift 2324100
  have htrace : WordTrace (prefixWord ++ tailWord_2324100) baseStart_2324100 baseEnd_2324100 := by
    simpa [prefixWord, tailWord_2324100, baseEnd_2324100] using wordTrace_append hprefix tailTrace_2324100
  have hstable : (prefixWord ++ tailWord_2324100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324100).length < 2 ^ (prefixWord ++ tailWord_2324100).sum := by decide
  have hdescent : baseEnd_2324100 < baseStart_2324100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324104 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 4, 3]
def baseStart_2324104 : Nat := 118140960795 + 2324104 * 2 ^ 59
def prefixEnd_2324104 : Nat := 4983230072969 + 3 ^ 40 * 2324104 * 2
def baseEnd_2324104 : Nat := 795588295358053444074431

theorem tailTrace_2324104 : CollatzResearch.WordTrace tailWord_2324104 prefixEnd_2324104 795588295358053444074431 := by
  unfold tailWord_2324104
  simp only [CollatzResearch.WordTrace]
  refine ⟨42383518386087804103733683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56511357848117072138311577 42383518386087804103733683)
  ·
    refine ⟨63575277579131706155600525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42383518386087804103733683 63575277579131706155600525)
    ·
      refine ⟨23840729092174389808350197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63575277579131706155600525 23840729092174389808350197)
      ·
        refine ⟨2235068352391349044532831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23840729092174389808350197 2235068352391349044532831)
        ·
          refine ⟨3352602528587023566799247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2235068352391349044532831 3352602528587023566799247)
          ·
            refine ⟨5028903792880535350198871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3352602528587023566799247 5028903792880535350198871)
            ·
              refine ⟨7543355689320803025298307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5028903792880535350198871 7543355689320803025298307)
              ·
                refine ⟨11315033533981204537947461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7543355689320803025298307 11315033533981204537947461)
                ·
                  refine ⟨2121568787621475850865149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11315033533981204537947461 2121568787621475850865149)
                  ·
                    refine ⟨795588295358053444074431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2121568787621475850865149 795588295358053444074431)
                    ·
                      rfl

theorem cell22_2324104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_2324104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324104 prefixEnd_2324104 := by exact prefixLift 2324104
  have htrace : WordTrace (prefixWord ++ tailWord_2324104) baseStart_2324104 baseEnd_2324104 := by
    simpa [prefixWord, tailWord_2324104, baseEnd_2324104] using wordTrace_append hprefix tailTrace_2324104
  have hstable : (prefixWord ++ tailWord_2324104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324104).length < 2 ^ (prefixWord ++ tailWord_2324104).sum := by decide
  have hdescent : baseEnd_2324104 < baseStart_2324104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324113 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 2, 6]
def baseStart_2324113 : Nat := 118140960795 + 2324113 * 2 ^ 59
def prefixEnd_2324113 : Nat := 4983230072969 + 3 ^ 40 * 2324113 * 2
def baseEnd_2324113 : Nat := 795591376241980420599403

theorem tailTrace_2324113 : CollatzResearch.WordTrace tailWord_2324113 prefixEnd_2324113 795591376241980420599403 := by
  unfold tailWord_2324113
  simp only [CollatzResearch.WordTrace]
  refine ⟨84767365029143002744544993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56511576686095335163029995 84767365029143002744544993)
  ·
    refine ⟨63575523771857252058408745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84767365029143002744544993 63575523771857252058408745)
    ·
      refine ⟨47681642828892939043806559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63575523771857252058408745 47681642828892939043806559)
      ·
        refine ⟨71522464243339408565709839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47681642828892939043806559 71522464243339408565709839)
        ·
          refine ⟨107283696365009112848564759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71522464243339408565709839 107283696365009112848564759)
          ·
            refine ⟨160925544547513669272847139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107283696365009112848564759 160925544547513669272847139)
            ·
              refine ⟨241388316821270503909270709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160925544547513669272847139 241388316821270503909270709)
              ·
                refine ⟨22630154701994109741494129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 241388316821270503909270709 22630154701994109741494129)
                ·
                  refine ⟨16972616026495582306120597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22630154701994109741494129 16972616026495582306120597)
                  ·
                    refine ⟨795591376241980420599403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16972616026495582306120597 795591376241980420599403)
                    ·
                      rfl

theorem cell22_2324113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_2324113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324113 prefixEnd_2324113 := by exact prefixLift 2324113
  have htrace : WordTrace (prefixWord ++ tailWord_2324113) baseStart_2324113 baseEnd_2324113 := by
    simpa [prefixWord, tailWord_2324113, baseEnd_2324113] using wordTrace_append hprefix tailTrace_2324113
  have hstable : (prefixWord ++ tailWord_2324113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324113).length < 2 ^ (prefixWord ++ tailWord_2324113).sum := by decide
  have hdescent : baseEnd_2324113 < baseStart_2324113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324132 : List Nat := [2, 3, 1, 2, 2, 2, 2, 2, 3, 3]
def baseStart_2324132 : Nat := 118140960795 + 2324132 * 2 ^ 59
def prefixEnd_2324132 : Nat := 4983230072969 + 3 ^ 40 * 2324132 * 2
def baseEnd_2324132 : Nat := 795597880330270704374345

theorem tailTrace_2324132 : CollatzResearch.WordTrace tailWord_2324132 prefixEnd_2324132 795597880330270704374345 := by
  unfold tailWord_2324132
  simp only [CollatzResearch.WordTrace]
  refine ⟨42384029008037084494743325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56512038677382779326324433 42384029008037084494743325)
  ·
    refine ⟨15894010878013906685528747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42384029008037084494743325 15894010878013906685528747)
    ·
      refine ⟨23841016317020860028293121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15894010878013906685528747 23841016317020860028293121)
      ·
        refine ⟨17880762237765645021219841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23841016317020860028293121 17880762237765645021219841)
        ·
          refine ⟨13410571678324233765914881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17880762237765645021219841 13410571678324233765914881)
          ·
            refine ⟨10057928758743175324436161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13410571678324233765914881 10057928758743175324436161)
            ·
              refine ⟨7543446569057381493327121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10057928758743175324436161 7543446569057381493327121)
              ·
                refine ⟨5657584926793036119995341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7543446569057381493327121 5657584926793036119995341)
                ·
                  refine ⟨2121594347547388544998253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5657584926793036119995341 2121594347547388544998253)
                  ·
                    refine ⟨795597880330270704374345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2121594347547388544998253 795597880330270704374345)
                    ·
                      rfl

theorem cell22_2324132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_2324132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324132 prefixEnd_2324132 := by exact prefixLift 2324132
  have htrace : WordTrace (prefixWord ++ tailWord_2324132) baseStart_2324132 baseEnd_2324132 := by
    simpa [prefixWord, tailWord_2324132, baseEnd_2324132] using wordTrace_append hprefix tailTrace_2324132
  have hstable : (prefixWord ++ tailWord_2324132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324132).length < 2 ^ (prefixWord ++ tailWord_2324132).sum := by decide
  have hdescent : baseEnd_2324132 < baseStart_2324132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324192 : List Nat := [2, 1, 1, 3, 1, 2, 5, 2, 1, 4]
def baseStart_2324192 : Nat := 118140960795 + 2324192 * 2 ^ 59
def prefixEnd_2324192 : Nat := 4983230072969 + 3 ^ 40 * 2324192 * 2
def baseEnd_2324192 : Nat := 795618419556450547874161

theorem tailTrace_2324192 : CollatzResearch.WordTrace tailWord_2324192 prefixEnd_2324192 795618419556450547874161 := by
  unfold tailWord_2324192
  simp only [CollatzResearch.WordTrace]
  refine ⟨42385123197928399618335415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56513497597237866157780553 42385123197928399618335415)
  ·
    refine ⟨63577684796892599427503123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42385123197928399618335415 63577684796892599427503123)
    ·
      refine ⟨95366527195338899141254685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63577684796892599427503123 95366527195338899141254685)
      ·
        refine ⟨35762447698252087177970507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95366527195338899141254685 35762447698252087177970507)
        ·
          refine ⟨53643671547378130766955761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35762447698252087177970507 53643671547378130766955761)
          ·
            refine ⟨40232753660533598075216821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53643671547378130766955761 40232753660533598075216821)
            ·
              refine ⟨3771820655675024819551577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40232753660533598075216821 3771820655675024819551577)
              ·
                refine ⟨2828865491756268614663683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3771820655675024819551577 2828865491756268614663683)
                ·
                  refine ⟨4243298237634402921995525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2828865491756268614663683 4243298237634402921995525)
                  ·
                    refine ⟨795618419556450547874161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4243298237634402921995525 795618419556450547874161)
                    ·
                      rfl

theorem cell22_2324192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 1, 4].length) (baseStart_2324192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324192 prefixEnd_2324192 := by exact prefixLift 2324192
  have htrace : WordTrace (prefixWord ++ tailWord_2324192) baseStart_2324192 baseEnd_2324192 := by
    simpa [prefixWord, tailWord_2324192, baseEnd_2324192] using wordTrace_append hprefix tailTrace_2324192
  have hstable : (prefixWord ++ tailWord_2324192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324192).length < 2 ^ (prefixWord ++ tailWord_2324192).sum := by decide
  have hdescent : baseEnd_2324192 < baseStart_2324192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324207 : List Nat := [1, 1, 2, 1, 5, 1, 2, 5, 4]
def baseStart_2324207 : Nat := 118140960795 + 2324207 * 2 ^ 59
def prefixEnd_2324207 : Nat := 4983230072969 + 3 ^ 40 * 2324207 * 2
def baseEnd_2324207 : Nat := 265207851454331836249705

theorem tailTrace_2324207 : CollatzResearch.WordTrace tailWord_2324207 prefixEnd_2324207 265207851454331836249705 := by
  unfold tailWord_2324207
  simp only [CollatzResearch.WordTrace]
  refine ⟨84770793490802456798466875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56513862327201637865644583 84770793490802456798466875)
  ·
    refine ⟨127156190236203685197700313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84770793490802456798466875 127156190236203685197700313)
    ·
      refine ⟨95367142677152763898275235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127156190236203685197700313 95367142677152763898275235)
      ·
        refine ⟨143050714015729145847412853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95367142677152763898275235 143050714015729145847412853)
        ·
          refine ⟨13411004438974607423194955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 143050714015729145847412853 13411004438974607423194955)
          ·
            refine ⟨20116506658461911134792433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13411004438974607423194955 20116506658461911134792433)
            ·
              refine ⟨15087379993846433351094325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20116506658461911134792433 15087379993846433351094325)
              ·
                refine ⟨1414441874423103126665093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15087379993846433351094325 1414441874423103126665093)
                ·
                  refine ⟨265207851454331836249705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1414441874423103126665093 265207851454331836249705)
                  ·
                    rfl

theorem cell22_2324207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 4].length) (baseStart_2324207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324207 prefixEnd_2324207 := by exact prefixLift 2324207
  have htrace : WordTrace (prefixWord ++ tailWord_2324207) baseStart_2324207 baseEnd_2324207 := by
    simpa [prefixWord, tailWord_2324207, baseEnd_2324207] using wordTrace_append hprefix tailTrace_2324207
  have hstable : (prefixWord ++ tailWord_2324207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324207).length < 2 ^ (prefixWord ++ tailWord_2324207).sum := by decide
  have hdescent : baseEnd_2324207 < baseStart_2324207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324209 : List Nat := [1, 2, 2, 2, 2, 4, 3, 1, 1, 4]
def baseStart_2324209 : Nat := 118140960795 + 2324209 * 2 ^ 59
def prefixEnd_2324209 : Nat := 4983230072969 + 3 ^ 40 * 2324209 * 2
def baseEnd_2324209 : Nat := 795624239003868170199109

theorem tailTrace_2324209 : CollatzResearch.WordTrace tailWord_2324209 prefixEnd_2324209 795624239003868170199109 := by
  unfold tailWord_2324209
  simp only [CollatzResearch.WordTrace]
  refine ⟨84770866436795211140039681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56513910957863474093359787 84770866436795211140039681)
  ·
    refine ⟨63578149827596408355029761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84770866436795211140039681 63578149827596408355029761)
    ·
      refine ⟨47683612370697306266272321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63578149827596408355029761 47683612370697306266272321)
      ·
        refine ⟨35762709278022979699704241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47683612370697306266272321 35762709278022979699704241)
        ·
          refine ⟨26822031958517234774778181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35762709278022979699704241 26822031958517234774778181)
          ·
            refine ⟨5029130992221981520270909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26822031958517234774778181 5029130992221981520270909)
            ·
              refine ⟨1885924122083243070101591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5029130992221981520270909 1885924122083243070101591)
              ·
                refine ⟨2828886183124864605152387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1885924122083243070101591 2828886183124864605152387)
                ·
                  refine ⟨4243329274687296907728581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2828886183124864605152387 4243329274687296907728581)
                  ·
                    refine ⟨795624239003868170199109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4243329274687296907728581 795624239003868170199109)
                    ·
                      rfl

theorem cell22_2324209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 1, 4].length) (baseStart_2324209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324209 prefixEnd_2324209 := by exact prefixLift 2324209
  have htrace : WordTrace (prefixWord ++ tailWord_2324209) baseStart_2324209 baseEnd_2324209 := by
    simpa [prefixWord, tailWord_2324209, baseEnd_2324209] using wordTrace_append hprefix tailTrace_2324209
  have hstable : (prefixWord ++ tailWord_2324209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324209).length < 2 ^ (prefixWord ++ tailWord_2324209).sum := by decide
  have hdescent : baseEnd_2324209 < baseStart_2324209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324235 : List Nat := [1, 1, 1, 1, 5, 1, 5, 7]
def baseStart_2324235 : Nat := 118140960795 + 2324235 * 2 ^ 59
def prefixEnd_2324235 : Nat := 4983230072969 + 3 ^ 40 * 2324235 * 2
def baseEnd_2324235 : Nat := 88403682148356974338781

theorem tailTrace_2324235 : CollatzResearch.WordTrace tailWord_2324235 prefixEnd_2324235 88403682148356974338781 := by
  unfold tailWord_2324235
  simp only [CollatzResearch.WordTrace]
  refine ⟨84771814734701017580486159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56514543156467345053657439 84771814734701017580486159)
  ·
    refine ⟨127157722102051526370729239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84771814734701017580486159 127157722102051526370729239)
    ·
      refine ⟨190736583153077289556093859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127157722102051526370729239 190736583153077289556093859)
      ·
        refine ⟨286104874729615934334140789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190736583153077289556093859 286104874729615934334140789)
        ·
          refine ⟨26822332005901493843825699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 286104874729615934334140789 26822332005901493843825699)
          ·
            refine ⟨40233498008852240765738549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26822332005901493843825699 40233498008852240765738549)
            ·
              refine ⟨3771890438329897571787989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40233498008852240765738549 3771890438329897571787989)
              ·
                refine ⟨88403682148356974338781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3771890438329897571787989 88403682148356974338781)
                ·
                  rfl

theorem cell22_2324235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 7].length) (baseStart_2324235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324235 prefixEnd_2324235 := by exact prefixLift 2324235
  have htrace : WordTrace (prefixWord ++ tailWord_2324235) baseStart_2324235 baseEnd_2324235 := by
    simpa [prefixWord, tailWord_2324235, baseEnd_2324235] using wordTrace_append hprefix tailTrace_2324235
  have hstable : (prefixWord ++ tailWord_2324235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324235).length < 2 ^ (prefixWord ++ tailWord_2324235).sum := by decide
  have hdescent : baseEnd_2324235 < baseStart_2324235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324252 : List Nat := [2, 2, 3, 1, 1, 2, 5, 6]
def baseStart_2324252 : Nat := 118140960795 + 2324252 * 2 ^ 59
def prefixEnd_2324252 : Nat := 4983230072969 + 3 ^ 40 * 2324252 * 2
def baseEnd_2324252 : Nat := 88404328753625599041553

theorem tailTrace_2324252 : CollatzResearch.WordTrace tailWord_2324252 prefixEnd_2324252 88404328753625599041553 := by
  unfold tailWord_2324252
  simp only [CollatzResearch.WordTrace]
  refine ⟨42386217387819714741927505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56514956517092952989236673 42386217387819714741927505)
  ·
    refine ⟨31789663040864786056445629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42386217387819714741927505 31789663040864786056445629)
    ·
      refine ⟨11921123640324294771167111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31789663040864786056445629 11921123640324294771167111)
      ·
        refine ⟨17881685460486442156750667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11921123640324294771167111 17881685460486442156750667)
        ·
          refine ⟨26822528190729663235126001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17881685460486442156750667 26822528190729663235126001)
          ·
            refine ⟨20116896143047247426344501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26822528190729663235126001 20116896143047247426344501)
            ·
              refine ⟨1885959013410679446219797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20116896143047247426344501 1885959013410679446219797)
              ·
                refine ⟨88404328753625599041553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1885959013410679446219797 88404328753625599041553)
                ·
                  rfl

theorem cell22_2324252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 6].length) (baseStart_2324252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324252 prefixEnd_2324252 := by exact prefixLift 2324252
  have htrace : WordTrace (prefixWord ++ tailWord_2324252) baseStart_2324252 baseEnd_2324252 := by
    simpa [prefixWord, tailWord_2324252, baseEnd_2324252] using wordTrace_append hprefix tailTrace_2324252
  have hstable : (prefixWord ++ tailWord_2324252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324252).length < 2 ^ (prefixWord ++ tailWord_2324252).sum := by decide
  have hdescent : baseEnd_2324252 < baseStart_2324252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324301 : List Nat := [1, 6, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_2324301 : Nat := 118140960795 + 2324301 * 2 ^ 59
def prefixEnd_2324301 : Nat := 4983230072969 + 3 ^ 40 * 2324301 * 2
def baseEnd_2324301 : Nat := 795655732484010596898827

theorem tailTrace_2324301 : CollatzResearch.WordTrace tailWord_2324301 prefixEnd_2324301 795655732484010596898827 := by
  unfold tailWord_2324301
  simp only [CollatzResearch.WordTrace]
  refine ⟨84774221952461910852388757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56516147968307940568259171 84774221952461910852388757)
  ·
    refine ⟨3973791654021652071205723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 84774221952461910852388757 3973791654021652071205723)
    ·
      refine ⟨5960687481032478106808585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3973791654021652071205723 5960687481032478106808585)
      ·
        refine ⟨4470515610774358580106439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5960687481032478106808585 4470515610774358580106439)
        ·
          refine ⟨6705773416161537870159659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4470515610774358580106439 6705773416161537870159659)
          ·
            refine ⟨10058660124242306805239489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6705773416161537870159659 10058660124242306805239489)
            ·
              refine ⟨7543995093181730103929617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10058660124242306805239489 7543995093181730103929617)
              ·
                refine ⟨5657996319886297577947213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7543995093181730103929617 5657996319886297577947213)
                ·
                  refine ⟨2121748619957361591730205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5657996319886297577947213 2121748619957361591730205)
                  ·
                    refine ⟨795655732484010596898827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2121748619957361591730205 795655732484010596898827)
                    ·
                      rfl

theorem cell22_2324301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_2324301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324301 prefixEnd_2324301 := by exact prefixLift 2324301
  have htrace : WordTrace (prefixWord ++ tailWord_2324301) baseStart_2324301 baseEnd_2324301 := by
    simpa [prefixWord, tailWord_2324301, baseEnd_2324301] using wordTrace_append hprefix tailTrace_2324301
  have hstable : (prefixWord ++ tailWord_2324301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324301).length < 2 ^ (prefixWord ++ tailWord_2324301).sum := by decide
  have hdescent : baseEnd_2324301 < baseStart_2324301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324357 : List Nat := [1, 3, 1, 1, 3, 2, 2, 3, 1, 5]
def baseStart_2324357 : Nat := 118140960795 + 2324357 * 2 ^ 59
def prefixEnd_2324357 : Nat := 4983230072969 + 3 ^ 40 * 2324357 * 2
def baseEnd_2324357 : Nat := 795674902428445117498655

theorem tailTrace_2324357 : CollatzResearch.WordTrace tailWord_2324357 prefixEnd_2324357 795674902428445117498655 := by
  unfold tailWord_2324357
  simp only [CollatzResearch.WordTrace]
  refine ⟨84776264440259032416427325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56517509626839354944284883 84776264440259032416427325)
  ·
    refine ⟨31791099165097137156160247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84776264440259032416427325 31791099165097137156160247)
    ·
      refine ⟨47686648747645705734240371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31791099165097137156160247 47686648747645705734240371)
      ·
        refine ⟨71529973121468558601360557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47686648747645705734240371 71529973121468558601360557)
        ·
          refine ⟨26823739920550709475510209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71529973121468558601360557 26823739920550709475510209)
          ·
            refine ⟨20117804940413032106632657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26823739920550709475510209 20117804940413032106632657)
            ·
              refine ⟨15088353705309774079974493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20117804940413032106632657 15088353705309774079974493)
              ·
                refine ⟨5658132639491165279990435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15088353705309774079974493 5658132639491165279990435)
                ·
                  refine ⟨8487198959236747919985653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5658132639491165279990435 8487198959236747919985653)
                  ·
                    refine ⟨795674902428445117498655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8487198959236747919985653 795674902428445117498655)
                    ·
                      rfl

theorem cell22_2324357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_2324357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324357 prefixEnd_2324357 := by exact prefixLift 2324357
  have htrace : WordTrace (prefixWord ++ tailWord_2324357) baseStart_2324357 baseEnd_2324357 := by
    simpa [prefixWord, tailWord_2324357, baseEnd_2324357] using wordTrace_append hprefix tailTrace_2324357
  have hstable : (prefixWord ++ tailWord_2324357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324357).length < 2 ^ (prefixWord ++ tailWord_2324357).sum := by decide
  have hdescent : baseEnd_2324357 < baseStart_2324357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324391 : List Nat := [1, 1, 6, 1, 2, 1, 1, 4, 2, 3]
def baseStart_2324391 : Nat := 118140960795 + 2324391 * 2 ^ 59
def prefixEnd_2324391 : Nat := 4983230072969 + 3 ^ 40 * 2324391 * 2
def baseEnd_2324391 : Nat := 795686541323280362148551

theorem tailTrace_2324391 : CollatzResearch.WordTrace tailWord_2324391 prefixEnd_2324391 795686541323280362148551 := by
  unfold tailWord_2324391
  simp only [CollatzResearch.WordTrace]
  refine ⟨84777504522135856223165027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56518336348090570815443351 84777504522135856223165027)
  ·
    refine ⟨127166256783203784334747541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84777504522135856223165027 127166256783203784334747541)
    ·
      refine ⟨5960918286712677390691291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 127166256783203784334747541 5960918286712677390691291)
      ·
        refine ⟨8941377430069016086036937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5960918286712677390691291 8941377430069016086036937)
        ·
          refine ⟨6706033072551762064527703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8941377430069016086036937 6706033072551762064527703)
          ·
            refine ⟨10059049608827643096791555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6706033072551762064527703 10059049608827643096791555)
            ·
              refine ⟨15088574413241464645187333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10059049608827643096791555 15088574413241464645187333)
              ·
                refine ⟨2829107702482774620972625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15088574413241464645187333 2829107702482774620972625)
                ·
                  refine ⟨2121830776862080965729469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2829107702482774620972625 2121830776862080965729469)
                  ·
                    refine ⟨795686541323280362148551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2121830776862080965729469 795686541323280362148551)
                    ·
                      rfl

theorem cell22_2324391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_2324391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324391 prefixEnd_2324391 := by exact prefixLift 2324391
  have htrace : WordTrace (prefixWord ++ tailWord_2324391) baseStart_2324391 baseEnd_2324391 := by
    simpa [prefixWord, tailWord_2324391, baseEnd_2324391] using wordTrace_append hprefix tailTrace_2324391
  have hstable : (prefixWord ++ tailWord_2324391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324391).length < 2 ^ (prefixWord ++ tailWord_2324391).sum := by decide
  have hdescent : baseEnd_2324391 < baseStart_2324391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324449 : List Nat := [1, 2, 3, 1, 2, 1, 5, 2, 5]
def baseStart_2324449 : Nat := 118140960795 + 2324449 * 2 ^ 59
def prefixEnd_2324449 : Nat := 4983230072969 + 3 ^ 40 * 2324449 * 2
def baseEnd_2324449 : Nat := 265235465302862514732791

theorem tailTrace_2324449 : CollatzResearch.WordTrace tailWord_2324449 prefixEnd_2324449 265235465302862514732791 := by
  unfold tailWord_2324449
  simp only [CollatzResearch.WordTrace]
  refine ⟨84779619955925732128776401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56519746637283821419184267 84779619955925732128776401)
  ·
    refine ⟨63584714966944299096582301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84779619955925732128776401 63584714966944299096582301)
    ·
      refine ⟨23844268112604112161218363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63584714966944299096582301 23844268112604112161218363)
      ·
        refine ⟨35766402168906168241827545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23844268112604112161218363 35766402168906168241827545)
        ·
          refine ⟨26824801626679626181370659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35766402168906168241827545 26824801626679626181370659)
          ·
            refine ⟨40237202440019439272055989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26824801626679626181370659 40237202440019439272055989)
            ·
              refine ⟨3772237728751822431755249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40237202440019439272055989 3772237728751822431755249)
              ·
                refine ⟨2829178296563866823816437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3772237728751822431755249 2829178296563866823816437)
                ·
                  refine ⟨265235465302862514732791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2829178296563866823816437 265235465302862514732791)
                  ·
                    rfl

theorem cell22_2324449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 5].length) (baseStart_2324449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324449 prefixEnd_2324449 := by exact prefixLift 2324449
  have htrace : WordTrace (prefixWord ++ tailWord_2324449) baseStart_2324449 baseEnd_2324449 := by
    simpa [prefixWord, tailWord_2324449, baseEnd_2324449] using wordTrace_append hprefix tailTrace_2324449
  have hstable : (prefixWord ++ tailWord_2324449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324449).length < 2 ^ (prefixWord ++ tailWord_2324449).sum := by decide
  have hdescent : baseEnd_2324449 < baseStart_2324449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324507 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 3, 6]
def baseStart_2324507 : Nat := 118140960795 + 2324507 * 2 ^ 59
def prefixEnd_2324507 : Nat := 4983230072969 + 3 ^ 40 * 2324507 * 2
def baseEnd_2324507 : Nat := 795726250493894726248195

theorem tailTrace_2324507 : CollatzResearch.WordTrace tailWord_2324507 prefixEnd_2324507 795726250493894726248195 := by
  unfold tailWord_2324507
  simp only [CollatzResearch.WordTrace]
  refine ⟨84781735389715608034387775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56521156926477072022925183 84781735389715608034387775)
  ·
    refine ⟨127172603084573412051581663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84781735389715608034387775 127172603084573412051581663)
    ·
      refine ⟨190758904626860118077372495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127172603084573412051581663 190758904626860118077372495)
      ·
        refine ⟨286138356940290177116058743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190758904626860118077372495 286138356940290177116058743)
        ·
          refine ⟨429207535410435265674088115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286138356940290177116058743 429207535410435265674088115)
          ·
            refine ⟨643811303115652898511132173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429207535410435265674088115 643811303115652898511132173)
            ·
              refine ⟨241429238668369836941674565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 643811303115652898511132173 241429238668369836941674565)
              ·
                refine ⟨45267982250319344426563981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 241429238668369836941674565 45267982250319344426563981)
                ·
                  refine ⟨16975493343869754159961493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45267982250319344426563981 16975493343869754159961493)
                  ·
                    refine ⟨795726250493894726248195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16975493343869754159961493 795726250493894726248195)
                    ·
                      rfl

theorem cell22_2324507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 6].length) (baseStart_2324507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324507 prefixEnd_2324507 := by exact prefixLift 2324507
  have htrace : WordTrace (prefixWord ++ tailWord_2324507) baseStart_2324507 baseEnd_2324507 := by
    simpa [prefixWord, tailWord_2324507, baseEnd_2324507] using wordTrace_append hprefix tailTrace_2324507
  have hstable : (prefixWord ++ tailWord_2324507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324507).length < 2 ^ (prefixWord ++ tailWord_2324507).sum := by decide
  have hdescent : baseEnd_2324507 < baseStart_2324507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324541 : List Nat := [1, 4, 1, 3, 1, 1, 4, 1, 2, 4]
def baseStart_2324541 : Nat := 118140960795 + 2324541 * 2 ^ 59
def prefixEnd_2324541 : Nat := 4983230072969 + 3 ^ 40 * 2324541 * 2
def baseEnd_2324541 : Nat := 795737889388729970898091

theorem tailTrace_2324541 : CollatzResearch.WordTrace tailWord_2324541 prefixEnd_2324541 795737889388729970898091 := by
  unfold tailWord_2324541
  simp only [CollatzResearch.WordTrace]
  refine ⟨84782975471592431841125477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56521983647728287894083651 84782975471592431841125477)
  ·
    refine ⟨15896807900923580970211027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84782975471592431841125477 15896807900923580970211027)
    ·
      refine ⟨23845211851385371455316541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15896807900923580970211027 23845211851385371455316541)
      ·
        refine ⟨8941954444269514295743703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23845211851385371455316541 8941954444269514295743703)
        ·
          refine ⟨13412931666404271443615555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8941954444269514295743703 13412931666404271443615555)
          ·
            refine ⟨20119397499606407165423333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13412931666404271443615555 20119397499606407165423333)
            ·
              refine ⟨3772387031176201343516875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20119397499606407165423333 3772387031176201343516875)
              ·
                refine ⟨5658580546764302015275313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3772387031176201343516875 5658580546764302015275313)
                ·
                  refine ⟨4243935410073226511456485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5658580546764302015275313 4243935410073226511456485)
                  ·
                    refine ⟨795737889388729970898091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4243935410073226511456485 795737889388729970898091)
                    ·
                      rfl

theorem cell22_2324541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_2324541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324541 prefixEnd_2324541 := by exact prefixLift 2324541
  have htrace : WordTrace (prefixWord ++ tailWord_2324541) baseStart_2324541 baseEnd_2324541 := by
    simpa [prefixWord, tailWord_2324541, baseEnd_2324541] using wordTrace_append hprefix tailTrace_2324541
  have hstable : (prefixWord ++ tailWord_2324541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324541).length < 2 ^ (prefixWord ++ tailWord_2324541).sum := by decide
  have hdescent : baseEnd_2324541 < baseStart_2324541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324562 : List Nat := [3, 2, 2, 1, 5, 1, 2, 2, 4]
def baseStart_2324562 : Nat := 118140960795 + 2324562 * 2 ^ 59
def prefixEnd_2324562 : Nat := 4983230072969 + 3 ^ 40 * 2324562 * 2
def baseEnd_2324562 : Nat := 265248359372630972041009

theorem tailTrace_2324562 : CollatzResearch.WordTrace tailWord_2324562 prefixEnd_2324562 265248359372630972041009 := by
  unfold tailWord_2324562
  simp only [CollatzResearch.WordTrace]
  refine ⟨21195935351129088106909985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56522494269677568285093293 21195935351129088106909985)
  ·
    refine ⟨15896951513346816080182489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21195935351129088106909985 15896951513346816080182489)
    ·
      refine ⟨11922713635010112060136867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15896951513346816080182489 11922713635010112060136867)
      ·
        refine ⟨17884070452515168090205301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11922713635010112060136867 17884070452515168090205301)
        ·
          refine ⟨1676631604923297008456747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17884070452515168090205301 1676631604923297008456747)
          ·
            refine ⟨2514947407384945512685121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1676631604923297008456747 2514947407384945512685121)
            ·
              refine ⟨1886210555538709134513841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2514947407384945512685121 1886210555538709134513841)
              ·
                refine ⟨1414657916654031850885381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1886210555538709134513841 1414657916654031850885381)
                ·
                  refine ⟨265248359372630972041009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1414657916654031850885381 265248359372630972041009)
                  ·
                    rfl

theorem cell22_2324562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_2324562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324562 prefixEnd_2324562 := by exact prefixLift 2324562
  have htrace : WordTrace (prefixWord ++ tailWord_2324562) baseStart_2324562 baseEnd_2324562 := by
    simpa [prefixWord, tailWord_2324562, baseEnd_2324562] using wordTrace_append hprefix tailTrace_2324562
  have hstable : (prefixWord ++ tailWord_2324562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324562).length < 2 ^ (prefixWord ++ tailWord_2324562).sum := by decide
  have hdescent : baseEnd_2324562 < baseStart_2324562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324573 : List Nat := [1, 4, 4, 1, 1, 3, 1, 7]
def baseStart_2324573 : Nat := 118140960795 + 2324573 * 2 ^ 59
def prefixEnd_2324573 : Nat := 4983230072969 + 3 ^ 40 * 2324573 * 2
def baseEnd_2324573 : Nat := 88416538182521394899777

theorem tailTrace_2324573 : CollatzResearch.WordTrace tailWord_2324573 prefixEnd_2324573 88416538182521394899777 := by
  unfold tailWord_2324573
  simp only [CollatzResearch.WordTrace]
  refine ⟨84784142607476501306290373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56522761738317667537526915 84784142607476501306290373)
  ·
    refine ⟨15897026738901843994929445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84784142607476501306290373 15897026738901843994929445)
    ·
      refine ⟨2980692513544095749049271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15897026738901843994929445 2980692513544095749049271)
      ·
        refine ⟨4471038770316143623573907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2980692513544095749049271 4471038770316143623573907)
        ·
          refine ⟨6706558155474215435360861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4471038770316143623573907 6706558155474215435360861)
          ·
            refine ⟨2514959308302830788260323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6706558155474215435360861 2514959308302830788260323)
            ·
              refine ⟨3772438962454246182390485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2514959308302830788260323 3772438962454246182390485)
              ·
                refine ⟨88416538182521394899777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3772438962454246182390485 88416538182521394899777)
                ·
                  rfl

theorem cell22_2324573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 7].length) (baseStart_2324573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324573 prefixEnd_2324573 := by exact prefixLift 2324573
  have htrace : WordTrace (prefixWord ++ tailWord_2324573) baseStart_2324573 baseEnd_2324573 := by
    simpa [prefixWord, tailWord_2324573, baseEnd_2324573] using wordTrace_append hprefix tailTrace_2324573
  have hstable : (prefixWord ++ tailWord_2324573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324573).length < 2 ^ (prefixWord ++ tailWord_2324573).sum := by decide
  have hdescent : baseEnd_2324573 < baseStart_2324573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324605 : List Nat := [1, 4, 1, 1, 3, 3, 2, 3, 1, 3]
def baseStart_2324605 : Nat := 118140960795 + 2324605 * 2 ^ 59
def prefixEnd_2324605 : Nat := 4983230072969 + 3 ^ 40 * 2324605 * 2
def baseEnd_2324605 : Nat := 795759797896655137297895

theorem tailTrace_2324605 : CollatzResearch.WordTrace tailWord_2324605 prefixEnd_2324605 795759797896655137297895 := by
  unfold tailWord_2324605
  simp only [CollatzResearch.WordTrace]
  refine ⟨84785309743360570771455269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56523539828907047180970179 84785309743360570771455269)
  ·
    refine ⟨15897245576880107019647863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84785309743360570771455269 15897245576880107019647863)
    ·
      refine ⟨23845868365320160529471795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15897245576880107019647863 23845868365320160529471795)
      ·
        refine ⟨35768802547980240794207693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23845868365320160529471795 35768802547980240794207693)
        ·
          refine ⟨13413300955492590297827885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35768802547980240794207693 13413300955492590297827885)
          ·
            refine ⟨5029987858309721361685457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13413300955492590297827885 5029987858309721361685457)
            ·
              refine ⟨3772490893732291021264093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5029987858309721361685457 3772490893732291021264093)
              ·
                refine ⟨1414684085149609132974035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3772490893732291021264093 1414684085149609132974035)
                ·
                  refine ⟨2122026127724413699461053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1414684085149609132974035 2122026127724413699461053)
                  ·
                    refine ⟨795759797896655137297895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2122026127724413699461053 795759797896655137297895)
                    ·
                      rfl

theorem cell22_2324605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_2324605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324605 prefixEnd_2324605 := by exact prefixLift 2324605
  have htrace : WordTrace (prefixWord ++ tailWord_2324605) baseStart_2324605 baseEnd_2324605 := by
    simpa [prefixWord, tailWord_2324605, baseEnd_2324605] using wordTrace_append hprefix tailTrace_2324605
  have hstable : (prefixWord ++ tailWord_2324605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324605).length < 2 ^ (prefixWord ++ tailWord_2324605).sum := by decide
  have hdescent : baseEnd_2324605 < baseStart_2324605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324616 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 2, 5]
def baseStart_2324616 : Nat := 118140960795 + 2324616 * 2 ^ 59
def prefixEnd_2324616 : Nat := 4983230072969 + 3 ^ 40 * 2324616 * 2
def baseEnd_2324616 : Nat := 795763563421454775272861

theorem tailTrace_2324616 : CollatzResearch.WordTrace tailWord_2324616 prefixEnd_2324616 795763563421454775272861 := by
  unfold tailWord_2324616
  simp only [CollatzResearch.WordTrace]
  refine ⟨42392855473160359825052851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56523807297547146433403801 42392855473160359825052851)
  ·
    refine ⟨63589283209740539737579277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42392855473160359825052851 63589283209740539737579277)
    ·
      refine ⟨23845981203652702401592229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63589283209740539737579277 23845981203652702401592229)
      ·
        refine ⟨4471121475684881700298543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23845981203652702401592229 4471121475684881700298543)
        ·
          refine ⟨6706682213527322550447815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4471121475684881700298543 6706682213527322550447815)
          ·
            refine ⟨10060023320290983825671723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6706682213527322550447815 10060023320290983825671723)
            ·
              refine ⟨15090034980436475738507585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10060023320290983825671723 15090034980436475738507585)
              ·
                refine ⟨11317526235327356803880689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15090034980436475738507585 11317526235327356803880689)
                ·
                  refine ⟨8488144676495517602910517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11317526235327356803880689 8488144676495517602910517)
                  ·
                    refine ⟨795763563421454775272861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8488144676495517602910517 795763563421454775272861)
                    ·
                      rfl

theorem cell22_2324616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_2324616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324616 prefixEnd_2324616 := by exact prefixLift 2324616
  have htrace : WordTrace (prefixWord ++ tailWord_2324616) baseStart_2324616 baseEnd_2324616 := by
    simpa [prefixWord, tailWord_2324616, baseEnd_2324616] using wordTrace_append hprefix tailTrace_2324616
  have hstable : (prefixWord ++ tailWord_2324616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324616).length < 2 ^ (prefixWord ++ tailWord_2324616).sum := by decide
  have hdescent : baseEnd_2324616 < baseStart_2324616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324618 : List Nat := [3, 1, 2, 3, 1, 4, 1, 2, 5]
def baseStart_2324618 : Nat := 118140960795 + 2324618 * 2 ^ 59
def prefixEnd_2324618 : Nat := 4983230072969 + 3 ^ 40 * 2324618 * 2
def baseEnd_2324618 : Nat := 265254749354109145574285

theorem tailTrace_2324618 : CollatzResearch.WordTrace tailWord_2324618 prefixEnd_2324618 265254749354109145574285 := by
  unfold tailWord_2324618
  simp only [CollatzResearch.WordTrace]
  refine ⟨21196445973078368497919627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56523855928208982661119005 21196445973078368497919627)
  ·
    refine ⟨31794668959617552746879441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21196445973078368497919627 31794668959617552746879441)
    ·
      refine ⟨23846001719713164560159581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31794668959617552746879441 23846001719713164560159581)
      ·
        refine ⟨8942250644892436710059843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23846001719713164560159581 8942250644892436710059843)
        ·
          refine ⟨13413375967338655065089765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8942250644892436710059843 13413375967338655065089765)
          ·
            refine ⟨2515007993875997824704331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13413375967338655065089765 2515007993875997824704331)
            ·
              refine ⟨3772511990813996737056497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2515007993875997824704331 3772511990813996737056497)
              ·
                refine ⟨2829383993110497552792373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3772511990813996737056497 2829383993110497552792373)
                ·
                  refine ⟨265254749354109145574285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2829383993110497552792373 265254749354109145574285)
                  ·
                    rfl

theorem cell22_2324618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_2324618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324618 prefixEnd_2324618 := by exact prefixLift 2324618
  have htrace : WordTrace (prefixWord ++ tailWord_2324618) baseStart_2324618 baseEnd_2324618 := by
    simpa [prefixWord, tailWord_2324618, baseEnd_2324618] using wordTrace_append hprefix tailTrace_2324618
  have hstable : (prefixWord ++ tailWord_2324618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324618).length < 2 ^ (prefixWord ++ tailWord_2324618).sum := by decide
  have hdescent : baseEnd_2324618 < baseStart_2324618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324663 : List Nat := [1, 1, 3, 1, 4, 2, 3, 3, 4]
def baseStart_2324663 : Nat := 118140960795 + 2324663 * 2 ^ 59
def prefixEnd_2324663 : Nat := 4983230072969 + 3 ^ 40 * 2324663 * 2
def baseEnd_2324663 : Nat := 265259884160654106449239

theorem tailTrace_2324663 : CollatzResearch.WordTrace tailWord_2324663 prefixEnd_2324663 265259884160654106449239 := by
  unfold tailWord_2324663
  simp only [CollatzResearch.WordTrace]
  refine ⟨84787425177150446677066643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56524950118100297784711095 84787425177150446677066643)
  ·
    refine ⟨127181137765725670015599965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84787425177150446677066643 127181137765725670015599965)
    ·
      refine ⟨47692926662147126255849987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127181137765725670015599965 47692926662147126255849987)
      ·
        refine ⟨71539389993220689383774981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47692926662147126255849987 71539389993220689383774981)
        ·
          refine ⟨13413635623728879259457809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71539389993220689383774981 13413635623728879259457809)
          ·
            refine ⟨10060226717796659444593357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13413635623728879259457809 10060226717796659444593357)
            ·
              refine ⟨3772585019173747291722509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10060226717796659444593357 3772585019173747291722509)
              ·
                refine ⟨1414719382190155234395941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3772585019173747291722509 1414719382190155234395941)
                ·
                  refine ⟨265259884160654106449239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1414719382190155234395941 265259884160654106449239)
                  ·
                    rfl

theorem cell22_2324663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 4].length) (baseStart_2324663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324663 prefixEnd_2324663 := by exact prefixLift 2324663
  have htrace : WordTrace (prefixWord ++ tailWord_2324663) baseStart_2324663 baseEnd_2324663 := by
    simpa [prefixWord, tailWord_2324663, baseEnd_2324663] using wordTrace_append hprefix tailTrace_2324663
  have hstable : (prefixWord ++ tailWord_2324663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324663).length < 2 ^ (prefixWord ++ tailWord_2324663).sum := by decide
  have hdescent : baseEnd_2324663 < baseStart_2324663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324736 : List Nat := [2, 1, 1, 2, 1, 1, 5, 4, 5]
def baseStart_2324736 : Nat := 118140960795 + 2324736 * 2 ^ 59
def prefixEnd_2324736 : Nat := 4983230072969 + 3 ^ 40 * 2324736 * 2
def baseEnd_2324736 : Nat := 265268213957938154090831

theorem tailTrace_2324736 : CollatzResearch.WordTrace tailWord_2324736 prefixEnd_2324736 265268213957938154090831 := by
  unfold tailWord_2324736
  simp only [CollatzResearch.WordTrace]
  refine ⟨42395043852942990072237031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56526725137257320096316041 42395043852942990072237031)
  ·
    refine ⟨63592565779414485108355547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42395043852942990072237031 63592565779414485108355547)
    ·
      refine ⟨95388848669121727662533321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63592565779414485108355547 95388848669121727662533321)
      ·
        refine ⟨71541636501841295746899991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95388848669121727662533321 71541636501841295746899991)
        ·
          refine ⟨107312454752761943620349987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71541636501841295746899991 107312454752761943620349987)
          ·
            refine ⟨160968682129142915430524981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107312454752761943620349987 160968682129142915430524981)
            ·
              refine ⟨15090813949607148321611717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 160968682129142915430524981 15090813949607148321611717)
              ·
                refine ⟨2829527615551340310302197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15090813949607148321611717 2829527615551340310302197)
                ·
                  refine ⟨265268213957938154090831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2829527615551340310302197 265268213957938154090831)
                  ·
                    rfl

theorem cell22_2324736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 5].length) (baseStart_2324736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324736 prefixEnd_2324736 := by exact prefixLift 2324736
  have htrace : WordTrace (prefixWord ++ tailWord_2324736) baseStart_2324736 baseEnd_2324736 := by
    simpa [prefixWord, tailWord_2324736, baseEnd_2324736] using wordTrace_append hprefix tailTrace_2324736
  have hstable : (prefixWord ++ tailWord_2324736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324736).length < 2 ^ (prefixWord ++ tailWord_2324736).sum := by decide
  have hdescent : baseEnd_2324736 < baseStart_2324736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324738 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_2324738 : Nat := 118140960795 + 2324738 * 2 ^ 59
def prefixEnd_2324738 : Nat := 4983230072969 + 3 ^ 40 * 2324738 * 2
def baseEnd_2324738 : Nat := 795805326514687123722487

theorem tailTrace_2324738 : CollatzResearch.WordTrace tailWord_2324738 prefixEnd_2324738 795805326514687123722487 := by
  unfold tailWord_2324738
  simp only [CollatzResearch.WordTrace]
  refine ⟨21197540162969683621511717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56526773767919156324031245 21197540162969683621511717)
  ·
    refine ⟨3974538780556815679033447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21197540162969683621511717 3974538780556815679033447)
    ·
      refine ⟨5961808170835223518550171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3974538780556815679033447 5961808170835223518550171)
      ·
        refine ⟨8942712256252835277825257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5961808170835223518550171 8942712256252835277825257)
        ·
          refine ⟨6707034192189626458368943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8942712256252835277825257 6707034192189626458368943)
          ·
            refine ⟨10060551288284439687553415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6707034192189626458368943 10060551288284439687553415)
            ·
              refine ⟨15090826932426659531330123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10060551288284439687553415 15090826932426659531330123)
              ·
                refine ⟨22636240398639989296995185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15090826932426659531330123 22636240398639989296995185)
                ·
                  refine ⟨16977180298979991972746389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22636240398639989296995185 16977180298979991972746389)
                  ·
                    refine ⟨795805326514687123722487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16977180298979991972746389 795805326514687123722487)
                    ·
                      rfl

theorem cell22_2324738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_2324738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324738 prefixEnd_2324738 := by exact prefixLift 2324738
  have htrace : WordTrace (prefixWord ++ tailWord_2324738) baseStart_2324738 baseEnd_2324738 := by
    simpa [prefixWord, tailWord_2324738, baseEnd_2324738] using wordTrace_append hprefix tailTrace_2324738
  have hstable : (prefixWord ++ tailWord_2324738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324738).length < 2 ^ (prefixWord ++ tailWord_2324738).sum := by decide
  have hdescent : baseEnd_2324738 < baseStart_2324738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324798 : List Nat := [4, 2, 1, 2, 1, 2, 1, 3, 6]
def baseStart_2324798 : Nat := 118140960795 + 2324798 * 2 ^ 59
def prefixEnd_2324798 : Nat := 4983230072969 + 3 ^ 40 * 2324798 * 2
def baseEnd_2324798 : Nat := 265275288580288989074101

theorem tailTrace_2324798 : CollatzResearch.WordTrace tailWord_2324798 prefixEnd_2324798 265275288580288989074101 := by
  unfold tailWord_2324798
  simp only [CollatzResearch.WordTrace]
  refine ⟨10599043628957670591653881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56528232687774243155487365 10599043628957670591653881)
  ·
    refine ⟨7949282721718252943740411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10599043628957670591653881 7949282721718252943740411)
    ·
      refine ⟨11923924082577379415610617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7949282721718252943740411 11923924082577379415610617)
      ·
        refine ⟨8942943061933034561707963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11923924082577379415610617 8942943061933034561707963)
        ·
          refine ⟨13414414592899551842561945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8942943061933034561707963 13414414592899551842561945)
          ·
            refine ⟨10060810944674663881921459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13414414592899551842561945 10060810944674663881921459)
            ·
              refine ⟨15091216417011995822882189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10060810944674663881921459 15091216417011995822882189)
              ·
                refine ⟨5659206156379498433580821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15091216417011995822882189 5659206156379498433580821)
                ·
                  refine ⟨265275288580288989074101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5659206156379498433580821 265275288580288989074101)
                  ·
                    rfl

theorem cell22_2324798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_2324798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324798 prefixEnd_2324798 := by exact prefixLift 2324798
  have htrace : WordTrace (prefixWord ++ tailWord_2324798) baseStart_2324798 baseEnd_2324798 := by
    simpa [prefixWord, tailWord_2324798, baseEnd_2324798] using wordTrace_append hprefix tailTrace_2324798
  have hstable : (prefixWord ++ tailWord_2324798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324798).length < 2 ^ (prefixWord ++ tailWord_2324798).sum := by decide
  have hdescent : baseEnd_2324798 < baseStart_2324798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324811 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 6, 4]
def baseStart_2324811 : Nat := 118140960795 + 2324811 * 2 ^ 59
def prefixEnd_2324811 : Nat := 4983230072969 + 3 ^ 40 * 2324811 * 2
def baseEnd_2324811 : Nat := 795830315906539266647263

theorem tailTrace_2324811 : CollatzResearch.WordTrace tailWord_2324811 prefixEnd_2324811 795830315906539266647263 := by
  unfold tailWord_2324811
  simp only [CollatzResearch.WordTrace]
  refine ⟨84792823180614267953454287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56528548787076178635636191 84792823180614267953454287)
  ·
    refine ⟨127189234770921401930181431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84792823180614267953454287 127189234770921401930181431)
    ·
      refine ⟨190783852156382102895272147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127189234770921401930181431 190783852156382102895272147)
      ·
        refine ⟨286175778234573154342908221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190783852156382102895272147 286175778234573154342908221)
        ·
          refine ⟨107315916837964932878590583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 286175778234573154342908221 107315916837964932878590583)
          ·
            refine ⟨160973875256947399317885875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107315916837964932878590583 160973875256947399317885875)
            ·
              refine ⟨241460812885421098976828813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160973875256947399317885875 241460812885421098976828813)
              ·
                refine ⟨90547804832032912116310805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241460812885421098976828813 90547804832032912116310805)
                ·
                  refine ⟨4244428351501542755452069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90547804832032912116310805 4244428351501542755452069)
                  ·
                    refine ⟨795830315906539266647263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4244428351501542755452069 795830315906539266647263)
                    ·
                      rfl

theorem cell22_2324811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 4].length) (baseStart_2324811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324811 prefixEnd_2324811 := by exact prefixLift 2324811
  have htrace : WordTrace (prefixWord ++ tailWord_2324811) baseStart_2324811 baseEnd_2324811 := by
    simpa [prefixWord, tailWord_2324811, baseEnd_2324811] using wordTrace_append hprefix tailTrace_2324811
  have hstable : (prefixWord ++ tailWord_2324811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324811).length < 2 ^ (prefixWord ++ tailWord_2324811).sum := by decide
  have hdescent : baseEnd_2324811 < baseStart_2324811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324832 : List Nat := [2, 1, 1, 3, 5, 2, 1, 3, 4]
def baseStart_2324832 : Nat := 118140960795 + 2324832 * 2 ^ 59
def prefixEnd_2324832 : Nat := 4983230072969 + 3 ^ 40 * 2324832 * 2
def baseEnd_2324832 : Nat := 265279168211900737290733

theorem tailTrace_2324832 : CollatzResearch.WordTrace tailWord_2324832 prefixEnd_2324832 265279168211900737290733 := by
  unfold tailWord_2324832
  simp only [CollatzResearch.WordTrace]
  refine ⟨42396794556769094269984375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56529059409025459026645833 42396794556769094269984375)
  ·
    refine ⟨63595191835153641404976563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42396794556769094269984375 63595191835153641404976563)
    ·
      refine ⟨95392787752730462107464845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63595191835153641404976563 95392787752730462107464845)
      ·
        refine ⟨35772295407273923290299317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95392787752730462107464845 35772295407273923290299317)
        ·
          refine ⟨3353652694431930308465561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35772295407273923290299317 3353652694431930308465561)
          ·
            refine ⟨2515239520823947731349171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3353652694431930308465561 2515239520823947731349171)
            ·
              refine ⟨3772859281235921597023757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2515239520823947731349171 3772859281235921597023757)
              ·
                refine ⟨1414822230463470598883909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3772859281235921597023757 1414822230463470598883909)
                ·
                  refine ⟨265279168211900737290733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1414822230463470598883909 265279168211900737290733)
                  ·
                    rfl

theorem cell22_2324832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 4].length) (baseStart_2324832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324832 prefixEnd_2324832 := by exact prefixLift 2324832
  have htrace : WordTrace (prefixWord ++ tailWord_2324832) baseStart_2324832 baseEnd_2324832 := by
    simpa [prefixWord, tailWord_2324832, baseEnd_2324832] using wordTrace_append hprefix tailTrace_2324832
  have hstable : (prefixWord ++ tailWord_2324832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324832).length < 2 ^ (prefixWord ++ tailWord_2324832).sum := by decide
  have hdescent : baseEnd_2324832 < baseStart_2324832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324950 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_2324950 : Nat := 118140960795 + 2324950 * 2 ^ 59
def prefixEnd_2324950 : Nat := 4983230072969 + 3 ^ 40 * 2324950 * 2
def baseEnd_2324950 : Nat := 265292632815729745807279

theorem tailTrace_2324950 : CollatzResearch.WordTrace tailWord_2324950 prefixEnd_2324950 265292632815729745807279 := by
  unfold tailWord_2324950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5299868307944418418297769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56531928618073796461842869 5299868307944418418297769)
  ·
    refine ⟨3974901230958313813723327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5299868307944418418297769 3974901230958313813723327)
    ·
      refine ⟨5962351846437470720584991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3974901230958313813723327 5962351846437470720584991)
      ·
        refine ⟨8943527769656206080877487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5962351846437470720584991 8943527769656206080877487)
        ·
          refine ⟨13415291654484309121316231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8943527769656206080877487 13415291654484309121316231)
          ·
            refine ⟨20122937481726463681974347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13415291654484309121316231 20122937481726463681974347)
            ·
              refine ⟨30184406222589695522961521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20122937481726463681974347 30184406222589695522961521)
              ·
                refine ⟨22638304666942271642221141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30184406222589695522961521 22638304666942271642221141)
                ·
                  refine ⟨265292632815729745807279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22638304666942271642221141 265292632815729745807279)
                  ·
                    rfl

theorem cell22_2324950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_2324950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2324950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2324950 prefixEnd_2324950 := by exact prefixLift 2324950
  have htrace : WordTrace (prefixWord ++ tailWord_2324950) baseStart_2324950 baseEnd_2324950 := by
    simpa [prefixWord, tailWord_2324950, baseEnd_2324950] using wordTrace_append hprefix tailTrace_2324950
  have hstable : (prefixWord ++ tailWord_2324950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324950).length < 2 ^ (prefixWord ++ tailWord_2324950).sum := by decide
  have hdescent : baseEnd_2324950 < baseStart_2324950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325012 : List Nat := [2, 4, 3, 1, 1, 3, 8]
def baseStart_2325012 : Nat := 118140960795 + 2325012 * 2 ^ 59
def prefixEnd_2325012 : Nat := 4983230072969 + 3 ^ 40 * 2325012 * 2
def baseEnd_2325012 : Nat := 29477745270897842310061

theorem tailTrace_2325012 : CollatzResearch.WordTrace tailWord_2325012 prefixEnd_2325012 29477745270897842310061 := by
  unfold tailWord_2325012
  simp only [CollatzResearch.WordTrace]
  refine ⟨42400077126443039640760645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56533436168590719521014193 42400077126443039640760645)
  ·
    refine ⟨7950014461208069932642621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42400077126443039640760645 7950014461208069932642621)
    ·
      refine ⟨2981255422953026224740983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7950014461208069932642621 2981255422953026224740983)
      ·
        refine ⟨4471883134429539337111475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2981255422953026224740983 4471883134429539337111475)
        ·
          refine ⟨6707824701644309005667213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4471883134429539337111475 6707824701644309005667213)
          ·
            refine ⟨2515434263116615877125205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6707824701644309005667213 2515434263116615877125205)
            ·
              refine ⟨29477745270897842310061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2515434263116615877125205 29477745270897842310061)
              ·
                rfl

theorem cell22_2325012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 8].length) (baseStart_2325012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2325012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2325012 prefixEnd_2325012 := by exact prefixLift 2325012
  have htrace : WordTrace (prefixWord ++ tailWord_2325012) baseStart_2325012 baseEnd_2325012 := by
    simpa [prefixWord, tailWord_2325012, baseEnd_2325012] using wordTrace_append hprefix tailTrace_2325012
  have hstable : (prefixWord ++ tailWord_2325012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325012).length < 2 ^ (prefixWord ++ tailWord_2325012).sum := by decide
  have hdescent : baseEnd_2325012 < baseStart_2325012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325027 : List Nat := [1, 1, 1, 4, 4, 1, 3, 1, 3, 3]
def baseStart_2325027 : Nat := 118140960795 + 2325027 * 2 ^ 59
def prefixEnd_2325027 : Nat := 4983230072969 + 3 ^ 40 * 2325027 * 2
def baseEnd_2325027 : Nat := 795904257120786703246601

theorem tailTrace_2325027 : CollatzResearch.WordTrace tailWord_2325027 prefixEnd_2325027 795904257120786703246601 := by
  unfold tailWord_2325027
  simp only [CollatzResearch.WordTrace]
  refine ⟨84800701347831736843317335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56533800898554491228878223 84800701347831736843317335)
  ·
    refine ⟨127201052021747605264976003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84800701347831736843317335 127201052021747605264976003)
    ·
      refine ⟨190801578032621407897464005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127201052021747605264976003 190801578032621407897464005)
      ·
        refine ⟨35775295881116513980774501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190801578032621407897464005 35775295881116513980774501)
        ·
          refine ⟨6707867977709346371395219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35775295881116513980774501 6707867977709346371395219)
          ·
            refine ⟨10061801966564019557092829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6707867977709346371395219 10061801966564019557092829)
            ·
              refine ⟨3773175737461507333909811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10061801966564019557092829 3773175737461507333909811)
              ·
                refine ⟨5659763606192261000864717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3773175737461507333909811 5659763606192261000864717)
                ·
                  refine ⟨2122411352322097875324269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5659763606192261000864717 2122411352322097875324269)
                  ·
                    refine ⟨795904257120786703246601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2122411352322097875324269 795904257120786703246601)
                    ·
                      rfl

theorem cell22_2325027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 3].length) (baseStart_2325027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2325027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2325027 prefixEnd_2325027 := by exact prefixLift 2325027
  have htrace : WordTrace (prefixWord ++ tailWord_2325027) baseStart_2325027 baseEnd_2325027 := by
    simpa [prefixWord, tailWord_2325027, baseEnd_2325027] using wordTrace_append hprefix tailTrace_2325027
  have hstable : (prefixWord ++ tailWord_2325027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325027).length < 2 ^ (prefixWord ++ tailWord_2325027).sum := by decide
  have hdescent : baseEnd_2325027 < baseStart_2325027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325100 : List Nat := [2, 2, 1, 1, 3, 1, 3, 3, 1, 5]
def baseStart_2325100 : Nat := 118140960795 + 2325100 * 2 ^ 59
def prefixEnd_2325100 : Nat := 4983230072969 + 3 ^ 40 * 2325100 * 2
def baseEnd_2325100 : Nat := 795929246512638846171377

theorem tailTrace_2325100 : CollatzResearch.WordTrace tailWord_2325100 prefixEnd_2325100 795929246512638846171377 := by
  unfold tailWord_2325100
  simp only [CollatzResearch.WordTrace]
  refine ⟨42401681938283635155362377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56535575917711513540483169 42401681938283635155362377)
  ·
    refine ⟨31801261453712726366521783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42401681938283635155362377 31801261453712726366521783)
    ·
      refine ⟨47701892180569089549782675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31801261453712726366521783 47701892180569089549782675)
      ·
        refine ⟨71552838270853634324674013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47701892180569089549782675 71552838270853634324674013)
        ·
          refine ⟨26832314351570112871752755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71552838270853634324674013 26832314351570112871752755)
          ·
            refine ⟨40248471527355169307629133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26832314351570112871752755 40248471527355169307629133)
            ·
              refine ⟨15093176822758188490360925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40248471527355169307629133 15093176822758188490360925)
              ·
                refine ⟨5659941308534320683885347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15093176822758188490360925 5659941308534320683885347)
                ·
                  refine ⟨8489911962801481025828021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5659941308534320683885347 8489911962801481025828021)
                  ·
                    refine ⟨795929246512638846171377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8489911962801481025828021 795929246512638846171377)
                    ·
                      rfl

theorem cell22_2325100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_2325100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2325100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2325100 prefixEnd_2325100 := by exact prefixLift 2325100
  have htrace : WordTrace (prefixWord ++ tailWord_2325100) baseStart_2325100 baseEnd_2325100 := by
    simpa [prefixWord, tailWord_2325100, baseEnd_2325100] using wordTrace_append hprefix tailTrace_2325100
  have hstable : (prefixWord ++ tailWord_2325100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325100).length < 2 ^ (prefixWord ++ tailWord_2325100).sum := by decide
  have hdescent : baseEnd_2325100 < baseStart_2325100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325102 : List Nat := [4, 1, 2, 2, 2, 2, 1, 2, 6]
def baseStart_2325102 : Nat := 118140960795 + 2325102 * 2 ^ 59
def prefixEnd_2325102 : Nat := 4983230072969 + 3 ^ 40 * 2325102 * 2
def baseEnd_2325102 : Nat := 265309977051170502540457

theorem tailTrace_2325102 : CollatzResearch.WordTrace tailWord_2325102 prefixEnd_2325102 265309977051170502540457 := by
  unfold tailWord_2325102
  simp only [CollatzResearch.WordTrace]
  refine ⟨10600429602820003081537195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56535624548373349768198373 10600429602820003081537195)
  ·
    refine ⟨15900644404230004622305793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10600429602820003081537195 15900644404230004622305793)
    ·
      refine ⟨11925483303172503466729345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15900644404230004622305793 11925483303172503466729345)
      ·
        refine ⟨8944112477379377600047009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11925483303172503466729345 8944112477379377600047009)
        ·
          refine ⟨6708084358034533200035257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8944112477379377600047009 6708084358034533200035257)
          ·
            refine ⟨5031063268525899900026443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6708084358034533200035257 5031063268525899900026443)
            ·
              refine ⟨7546594902788849850039665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5031063268525899900026443 7546594902788849850039665)
              ·
                refine ⟨5659946177091637387529749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7546594902788849850039665 5659946177091637387529749)
                ·
                  refine ⟨265309977051170502540457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5659946177091637387529749 265309977051170502540457)
                  ·
                    rfl

theorem cell22_2325102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_2325102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2325102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2325102 prefixEnd_2325102 := by exact prefixLift 2325102
  have htrace : WordTrace (prefixWord ++ tailWord_2325102) baseStart_2325102 baseEnd_2325102 := by
    simpa [prefixWord, tailWord_2325102, baseEnd_2325102] using wordTrace_append hprefix tailTrace_2325102
  have hstable : (prefixWord ++ tailWord_2325102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325102).length < 2 ^ (prefixWord ++ tailWord_2325102).sum := by decide
  have hdescent : baseEnd_2325102 < baseStart_2325102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325115 : List Nat := [1, 1, 1, 1, 1, 4, 2, 5, 2, 4]
def baseStart_2325115 : Nat := 118140960795 + 2325115 * 2 ^ 59
def prefixEnd_2325115 : Nat := 4983230072969 + 3 ^ 40 * 2325115 * 2
def baseEnd_2325115 : Nat := 795934381319183807046331

theorem tailTrace_2325115 : CollatzResearch.WordTrace tailWord_2325115 prefixEnd_2325115 795934381319183807046331 := by
  unfold tailWord_2325115
  simp only [CollatzResearch.WordTrace]
  refine ⟨84803910971512927872520799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56535940647675285248347199 84803910971512927872520799)
  ·
    refine ⟨127205866457269391808781199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84803910971512927872520799 127205866457269391808781199)
    ·
      refine ⟨190808799685904087713171799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127205866457269391808781199 190808799685904087713171799)
      ·
        refine ⟨286213199528856131569757699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190808799685904087713171799 286213199528856131569757699)
        ·
          refine ⟨429319799293284197354636549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286213199528856131569757699 429319799293284197354636549)
          ·
            refine ⟨80497462367490787003994353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 429319799293284197354636549 80497462367490787003994353)
            ·
              refine ⟨60373096775618090252995765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80497462367490787003994353 60373096775618090252995765)
              ·
                refine ⟨5659977822714195961218353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60373096775618090252995765 5659977822714195961218353)
                ·
                  refine ⟨4244983367035646970913765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5659977822714195961218353 4244983367035646970913765)
                  ·
                    refine ⟨795934381319183807046331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4244983367035646970913765 795934381319183807046331)
                    ·
                      rfl

theorem cell22_2325115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 4].length) (baseStart_2325115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2325115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2325115 prefixEnd_2325115 := by exact prefixLift 2325115
  have htrace : WordTrace (prefixWord ++ tailWord_2325115) baseStart_2325115 baseEnd_2325115 := by
    simpa [prefixWord, tailWord_2325115, baseEnd_2325115] using wordTrace_append hprefix tailTrace_2325115
  have hstable : (prefixWord ++ tailWord_2325115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325115).length < 2 ^ (prefixWord ++ tailWord_2325115).sum := by decide
  have hdescent : baseEnd_2325115 < baseStart_2325115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325196 : List Nat := [2, 2, 1, 5, 1, 3, 1, 1, 3, 3]
def baseStart_2325196 : Nat := 118140960795 + 2325196 * 2 ^ 59
def prefixEnd_2325196 : Nat := 4983230072969 + 3 ^ 40 * 2325196 * 2
def baseEnd_2325196 : Nat := 795962109274526595771083

theorem tailTrace_2325196 : CollatzResearch.WordTrace tailWord_2325196 prefixEnd_2325196 795962109274526595771083 := by
  unfold tailWord_2325196
  simp only [CollatzResearch.WordTrace]
  refine ⟨42403432642109739353109721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56537910189479652470812961 42403432642109739353109721)
  ·
    refine ⟨31802574481582304514832291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42403432642109739353109721 31802574481582304514832291)
    ·
      refine ⟨47703861722373456772248437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31802574481582304514832291 47703861722373456772248437)
      ·
        refine ⟨4472237036472511572398291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47703861722373456772248437 4472237036472511572398291)
        ·
          refine ⟨6708355554708767358597437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4472237036472511572398291 6708355554708767358597437)
          ·
            refine ⟨2515633333015787759474039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6708355554708767358597437 2515633333015787759474039)
            ·
              refine ⟨3773449999523681639211059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2515633333015787759474039 3773449999523681639211059)
              ·
                refine ⟨5660174999285522458816589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3773449999523681639211059 5660174999285522458816589)
                ·
                  refine ⟨2122565624732070922056221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5660174999285522458816589 2122565624732070922056221)
                  ·
                    refine ⟨795962109274526595771083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2122565624732070922056221 795962109274526595771083)
                    ·
                      rfl

theorem cell22_2325196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_2325196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2325196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2325196 prefixEnd_2325196 := by exact prefixLift 2325196
  have htrace : WordTrace (prefixWord ++ tailWord_2325196) baseStart_2325196 baseEnd_2325196 := by
    simpa [prefixWord, tailWord_2325196, baseEnd_2325196] using wordTrace_append hprefix tailTrace_2325196
  have hstable : (prefixWord ++ tailWord_2325196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325196).length < 2 ^ (prefixWord ++ tailWord_2325196).sum := by decide
  have hdescent : baseEnd_2325196 < baseStart_2325196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325252 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_2325252 : Nat := 118140960795 + 2325252 * 2 ^ 59
def prefixEnd_2325252 : Nat := 4983230072969 + 3 ^ 40 * 2325252 * 2
def baseEnd_2325252 : Nat := 795981279218961116370911

theorem tailTrace_2325252 : CollatzResearch.WordTrace tailWord_2325252 prefixEnd_2325252 795981279218961116370911 := by
  unfold tailWord_2325252
  simp only [CollatzResearch.WordTrace]
  refine ⟨42404453886008300135129005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56539271848011066846838673 42404453886008300135129005)
  ·
    refine ⟨15901670207253112550673377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42404453886008300135129005 15901670207253112550673377)
    ·
      refine ⟨11926252655439834413005033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15901670207253112550673377 11926252655439834413005033)
      ·
        refine ⟨8944689491579875809753775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11926252655439834413005033 8944689491579875809753775)
        ·
          refine ⟨13417034237369813714630663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8944689491579875809753775 13417034237369813714630663)
          ·
            refine ⟨20125551356054720571945995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13417034237369813714630663 20125551356054720571945995)
            ·
              refine ⟨30188327034082080857918993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20125551356054720571945995 30188327034082080857918993)
              ·
                refine ⟨22641245275561560643439245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30188327034082080857918993 22641245275561560643439245)
                ·
                  refine ⟨8490466978335585241289717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22641245275561560643439245 8490466978335585241289717)
                  ·
                    refine ⟨795981279218961116370911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8490466978335585241289717 795981279218961116370911)
                    ·
                      rfl

theorem cell22_2325252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_2325252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2325252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2325252 prefixEnd_2325252 := by exact prefixLift 2325252
  have htrace : WordTrace (prefixWord ++ tailWord_2325252) baseStart_2325252 baseEnd_2325252 := by
    simpa [prefixWord, tailWord_2325252, baseEnd_2325252] using wordTrace_append hprefix tailTrace_2325252
  have hstable : (prefixWord ++ tailWord_2325252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325252).length < 2 ^ (prefixWord ++ tailWord_2325252).sum := by decide
  have hdescent : baseEnd_2325252 < baseStart_2325252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325269 : List Nat := [1, 3, 2, 1, 2, 2, 1, 5, 2, 3]
def baseStart_2325269 : Nat := 118140960795 + 2325269 * 2 ^ 59
def prefixEnd_2325269 : Nat := 4983230072969 + 3 ^ 40 * 2325269 * 2
def baseEnd_2325269 : Nat := 795987098666378738695859

theorem tailTrace_2325269 : CollatzResearch.WordTrace tailWord_2325269 prefixEnd_2325269 795987098666378738695859 := by
  unfold tailWord_2325269
  simp only [CollatzResearch.WordTrace]
  refine ⟨84809527812955012173626861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56539685208636674782417907 84809527812955012173626861)
  ·
    refine ⟨31803572929858129565110073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84809527812955012173626861 31803572929858129565110073)
    ·
      refine ⟨23852679697393597173832555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31803572929858129565110073 23852679697393597173832555)
      ·
        refine ⟨35779019546090395760748833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23852679697393597173832555 35779019546090395760748833)
        ·
          refine ⟨26834264659567796820561625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35779019546090395760748833 26834264659567796820561625)
          ·
            refine ⟨20125698494675847615421219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26834264659567796820561625 20125698494675847615421219)
            ·
              refine ⟨30188547742013771423131829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20125698494675847615421219 30188547742013771423131829)
              ·
                refine ⟨2830176350813791070918609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30188547742013771423131829 2830176350813791070918609)
                ·
                  refine ⟨2122632263110343303188957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2830176350813791070918609 2122632263110343303188957)
                  ·
                    refine ⟨795987098666378738695859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2122632263110343303188957 795987098666378738695859)
                    ·
                      rfl

theorem cell22_2325269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_2325269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2325269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2325269 prefixEnd_2325269 := by exact prefixLift 2325269
  have htrace : WordTrace (prefixWord ++ tailWord_2325269) baseStart_2325269 baseEnd_2325269 := by
    simpa [prefixWord, tailWord_2325269, baseEnd_2325269] using wordTrace_append hprefix tailTrace_2325269
  have hstable : (prefixWord ++ tailWord_2325269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325269).length < 2 ^ (prefixWord ++ tailWord_2325269).sum := by decide
  have hdescent : baseEnd_2325269 < baseStart_2325269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325284 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 1, 6]
def baseStart_2325284 : Nat := 118140960795 + 2325284 * 2 ^ 59
def prefixEnd_2325284 : Nat := 4983230072969 + 3 ^ 40 * 2325284 * 2
def baseEnd_2325284 : Nat := 795992233472923699570813

theorem tailTrace_2325284 : CollatzResearch.WordTrace tailWord_2325284 prefixEnd_2325284 795992233472923699570813 := by
  unfold tailWord_2325284
  simp only [CollatzResearch.WordTrace]
  refine ⟨42405037453950334867711453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56540049938600446490281937 42405037453950334867711453)
  ·
    refine ⟨15901889045231375575391795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42405037453950334867711453 15901889045231375575391795)
    ·
      refine ⟨23852833567847063363087693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15901889045231375575391795 23852833567847063363087693)
      ·
        refine ⟨8944812587942648761157885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23852833567847063363087693 8944812587942648761157885)
        ·
          refine ⟨3354304720478493285434207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8944812587942648761157885 3354304720478493285434207)
          ·
            refine ⟨5031457080717739928151311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3354304720478493285434207 5031457080717739928151311)
            ·
              refine ⟨7547185621076609892226967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5031457080717739928151311 7547185621076609892226967)
              ·
                refine ⟨11320778431614914838340451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7547185621076609892226967 11320778431614914838340451)
                ·
                  refine ⟨16981167647422372257510677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11320778431614914838340451 16981167647422372257510677)
                  ·
                    refine ⟨795992233472923699570813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16981167647422372257510677 795992233472923699570813)
                    ·
                      rfl

theorem cell22_2325284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_2325284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2325284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2325284 prefixEnd_2325284 := by exact prefixLift 2325284
  have htrace : WordTrace (prefixWord ++ tailWord_2325284) baseStart_2325284 baseEnd_2325284 := by
    simpa [prefixWord, tailWord_2325284, baseEnd_2325284] using wordTrace_append hprefix tailTrace_2325284
  have hstable : (prefixWord ++ tailWord_2325284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325284).length < 2 ^ (prefixWord ++ tailWord_2325284).sum := by decide
  have hdescent : baseEnd_2325284 < baseStart_2325284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325290 : List Nat := [3, 1, 4, 3, 1, 2, 2, 1, 1, 4]
def baseStart_2325290 : Nat := 118140960795 + 2325290 * 2 ^ 59
def prefixEnd_2325290 : Nat := 4983230072969 + 3 ^ 40 * 2325290 * 2
def baseEnd_2325290 : Nat := 795994287395541683920795

theorem tailTrace_2325290 : CollatzResearch.WordTrace tailWord_2325290 prefixEnd_2325290 795994287395541683920795 := by
  unfold tailWord_2325290
  simp only [CollatzResearch.WordTrace]
  refine ⟨21202573436469733190035331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56540195830585955173427549 21202573436469733190035331)
  ·
    refine ⟨31803860154704599785052997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21202573436469733190035331 31803860154704599785052997)
    ·
      refine ⟨5963223779007112459697437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31803860154704599785052997 5963223779007112459697437)
      ·
        refine ⟨2236208917127667172386539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5963223779007112459697437 2236208917127667172386539)
        ·
          refine ⟨3354313375691500758579809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2236208917127667172386539 3354313375691500758579809)
          ·
            refine ⟨2515735031768625568934857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3354313375691500758579809 2515735031768625568934857)
            ·
              refine ⟨1886801273826469176701143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2515735031768625568934857 1886801273826469176701143)
              ·
                refine ⟨2830201910739703765051715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1886801273826469176701143 2830201910739703765051715)
                ·
                  refine ⟨4245302866109555647577573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2830201910739703765051715 4245302866109555647577573)
                  ·
                    refine ⟨795994287395541683920795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4245302866109555647577573 795994287395541683920795)
                    ·
                      rfl

theorem cell22_2325290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_2325290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2325290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2325290 prefixEnd_2325290 := by exact prefixLift 2325290
  have htrace : WordTrace (prefixWord ++ tailWord_2325290) baseStart_2325290 baseEnd_2325290 := by
    simpa [prefixWord, tailWord_2325290, baseEnd_2325290] using wordTrace_append hprefix tailTrace_2325290
  have hstable : (prefixWord ++ tailWord_2325290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325290).length < 2 ^ (prefixWord ++ tailWord_2325290).sum := by decide
  have hdescent : baseEnd_2325290 < baseStart_2325290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325348 : List Nat := [2, 3, 1, 1, 4, 1, 3, 3, 1, 3]
def baseStart_2325348 : Nat := 118140960795 + 2325348 * 2 ^ 59
def prefixEnd_2325348 : Nat := 4983230072969 + 3 ^ 40 * 2325348 * 2
def baseEnd_2325348 : Nat := 796014141980848865970617

theorem tailTrace_2325348 : CollatzResearch.WordTrace tailWord_2325348 prefixEnd_2325348 796014141980848865970617 := by
  unfold tailWord_2325348
  simp only [CollatzResearch.WordTrace]
  refine ⟨42406204589834404332876349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56541606119779205777168465 42406204589834404332876349)
  ·
    refine ⟨15902326721187901624828631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42406204589834404332876349 15902326721187901624828631)
    ·
      refine ⟨23853490081781852437242947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15902326721187901624828631 23853490081781852437242947)
      ·
        refine ⟨35780235122672778655864421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23853490081781852437242947 35780235122672778655864421)
        ·
          refine ⟨6708794085501145997974579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35780235122672778655864421 6708794085501145997974579)
          ·
            refine ⟨10063191128251718996961869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6708794085501145997974579 10063191128251718996961869)
            ·
              refine ⟨3773696673094394623860701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10063191128251718996961869 3773696673094394623860701)
              ·
                refine ⟨1415136252410397983947763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3773696673094394623860701 1415136252410397983947763)
                ·
                  refine ⟨2122704378615596975921645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1415136252410397983947763 2122704378615596975921645)
                  ·
                    refine ⟨796014141980848865970617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2122704378615596975921645 796014141980848865970617)
                    ·
                      rfl

theorem cell22_2325348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_2325348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2325348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2325348 prefixEnd_2325348 := by exact prefixLift 2325348
  have htrace : WordTrace (prefixWord ++ tailWord_2325348) baseStart_2325348 baseEnd_2325348 := by
    simpa [prefixWord, tailWord_2325348, baseEnd_2325348] using wordTrace_append hprefix tailTrace_2325348
  have hstable : (prefixWord ++ tailWord_2325348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325348).length < 2 ^ (prefixWord ++ tailWord_2325348).sum := by decide
  have hdescent : baseEnd_2325348 < baseStart_2325348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325365 : List Nat := [1, 3, 4, 1, 1, 3, 3, 2, 1, 3]
def baseStart_2325365 : Nat := 118140960795 + 2325365 * 2 ^ 59
def prefixEnd_2325365 : Nat := 4983230072969 + 3 ^ 40 * 2325365 * 2
def baseEnd_2325365 : Nat := 796019961428266488295565

theorem tailTrace_2325365 : CollatzResearch.WordTrace tailWord_2325365 prefixEnd_2325365 796019961428266488295565 := by
  unfold tailWord_2325365
  simp only [CollatzResearch.WordTrace]
  refine ⟨84813029220607220569121549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56542019480404813712747699 84813029220607220569121549)
  ·
    refine ⟨31804885957727707713420581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84813029220607220569121549 31804885957727707713420581)
    ·
      refine ⟨5963416117073945196266359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31804885957727707713420581 5963416117073945196266359)
      ·
        refine ⟨8945124175610917794399539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5963416117073945196266359 8945124175610917794399539)
        ·
          refine ⟨13417686263416376691599309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8945124175610917794399539 13417686263416376691599309)
          ·
            refine ⟨5031632348781141259349741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13417686263416376691599309 5031632348781141259349741)
            ·
              refine ⟨1886862130792927972256153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5031632348781141259349741 1886862130792927972256153)
              ·
                refine ⟨1415146598094695979192115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1886862130792927972256153 1415146598094695979192115)
                ·
                  refine ⟨2122719897142043968788173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1415146598094695979192115 2122719897142043968788173)
                  ·
                    refine ⟨796019961428266488295565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2122719897142043968788173 796019961428266488295565)
                    ·
                      rfl

theorem cell22_2325365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_2325365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2325365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2325365 prefixEnd_2325365 := by exact prefixLift 2325365
  have htrace : WordTrace (prefixWord ++ tailWord_2325365) baseStart_2325365 baseEnd_2325365 := by
    simpa [prefixWord, tailWord_2325365, baseEnd_2325365] using wordTrace_append hprefix tailTrace_2325365
  have hstable : (prefixWord ++ tailWord_2325365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325365).length < 2 ^ (prefixWord ++ tailWord_2325365).sum := by decide
  have hdescent : baseEnd_2325365 < baseStart_2325365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325571 : List Nat := [1, 1, 1, 3, 1, 2, 6, 1, 2, 4]
def baseStart_2325571 : Nat := 118140960795 + 2325571 * 2 ^ 59
def prefixEnd_2325571 : Nat := 4983230072969 + 3 ^ 40 * 2325571 * 2
def baseEnd_2325571 : Nat := 796090479438150617644933

theorem tailTrace_2325571 : CollatzResearch.WordTrace tailWord_2325571 prefixEnd_2325571 796090479438150617644933 := by
  unfold tailWord_2325571
  simp only [CollatzResearch.WordTrace]
  refine ⟨84820542657860917751120567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56547028438573945167413711 84820542657860917751120567)
  ·
    refine ⟨127230813986791376626680851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84820542657860917751120567 127230813986791376626680851)
    ·
      refine ⟨190846220980187064940021277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127230813986791376626680851 190846220980187064940021277)
      ·
        refine ⟨71567332867570149352507979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190846220980187064940021277 71567332867570149352507979)
        ·
          refine ⟨107350999301355224028761969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71567332867570149352507979 107350999301355224028761969)
          ·
            refine ⟨80513249476016418021571477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107350999301355224028761969 80513249476016418021571477)
            ·
              refine ⟨3774058569188269594761163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80513249476016418021571477 3774058569188269594761163)
              ·
                refine ⟨5661087853782404392141745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3774058569188269594761163 5661087853782404392141745)
                ·
                  refine ⟨4245815890336803294106309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5661087853782404392141745 4245815890336803294106309)
                  ·
                    refine ⟨796090479438150617644933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4245815890336803294106309 796090479438150617644933)
                    ·
                      rfl

theorem cell22_2325571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 4].length) (baseStart_2325571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2325571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2325571 prefixEnd_2325571 := by exact prefixLift 2325571
  have htrace : WordTrace (prefixWord ++ tailWord_2325571) baseStart_2325571 baseEnd_2325571 := by
    simpa [prefixWord, tailWord_2325571, baseEnd_2325571] using wordTrace_append hprefix tailTrace_2325571
  have hstable : (prefixWord ++ tailWord_2325571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325571).length < 2 ^ (prefixWord ++ tailWord_2325571).sum := by decide
  have hdescent : baseEnd_2325571 < baseStart_2325571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325599 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 1, 8]
def baseStart_2325599 : Nat := 118140960795 + 2325599 * 2 ^ 59
def prefixEnd_2325599 : Nat := 4983230072969 + 3 ^ 40 * 2325599 * 2
def baseEnd_2325599 : Nat := 796100064410367877944847

theorem tailTrace_2325599 : CollatzResearch.WordTrace tailWord_2325599 prefixEnd_2325599 796100064410367877944847 := by
  unfold tailWord_2325599
  simp only [CollatzResearch.WordTrace]
  refine ⟨84821563901759478533139851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56547709267839652355426567 84821563901759478533139851)
  ·
    refine ⟨127232345852639217799709777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84821563901759478533139851 127232345852639217799709777)
    ·
      refine ⟨95424259389479413349782333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127232345852639217799709777 95424259389479413349782333)
      ·
        refine ⟨35784097271054780006168375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95424259389479413349782333 35784097271054780006168375)
        ·
          refine ⟨53676145906582170009252563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35784097271054780006168375 53676145906582170009252563)
          ·
            refine ⟨80514218859873255013878845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53676145906582170009252563 80514218859873255013878845)
            ·
              refine ⟨30192832072452470630204567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80514218859873255013878845 30192832072452470630204567)
              ·
                refine ⟨45289248108678705945306851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30192832072452470630204567 45289248108678705945306851)
                ·
                  refine ⟨67933872163018058917960277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45289248108678705945306851 67933872163018058917960277)
                  ·
                    refine ⟨796100064410367877944847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67933872163018058917960277 796100064410367877944847)
                    ·
                      rfl

theorem cell22_2325599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_2325599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2325599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2325599 prefixEnd_2325599 := by exact prefixLift 2325599
  have htrace : WordTrace (prefixWord ++ tailWord_2325599) baseStart_2325599 baseEnd_2325599 := by
    simpa [prefixWord, tailWord_2325599, baseEnd_2325599] using wordTrace_append hprefix tailTrace_2325599
  have hstable : (prefixWord ++ tailWord_2325599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325599).length < 2 ^ (prefixWord ++ tailWord_2325599).sum := by decide
  have hdescent : baseEnd_2325599 < baseStart_2325599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325618 : List Nat := [3, 2, 1, 2, 2, 1, 3, 2, 3, 3]
def baseStart_2325618 : Nat := 118140960795 + 2325618 * 2 ^ 59
def prefixEnd_2325618 : Nat := 4983230072969 + 3 ^ 40 * 2325618 * 2
def baseEnd_2325618 : Nat := 796106568498658161719789

theorem tailTrace_2325618 : CollatzResearch.WordTrace tailWord_2325618 prefixEnd_2325618 796106568498658161719789 := by
  unfold tailWord_2325618
  simp only [CollatzResearch.WordTrace]
  refine ⟨21205564222172661194520377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56548171259127096518721005 21205564222172661194520377)
  ·
    refine ⟨15904173166629495895890283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21205564222172661194520377 15904173166629495895890283)
    ·
      refine ⟨23856259749944243843835425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15904173166629495895890283 23856259749944243843835425)
      ·
        refine ⟨17892194812458182882876569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23856259749944243843835425 17892194812458182882876569)
        ·
          refine ⟨13419146109343637162157427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17892194812458182882876569 13419146109343637162157427)
          ·
            refine ⟨20128719164015455743236141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13419146109343637162157427 20128719164015455743236141)
            ·
              refine ⟨7548269686505795903713553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20128719164015455743236141 7548269686505795903713553)
              ·
                refine ⟨5661202264879346927785165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7548269686505795903713553 5661202264879346927785165)
                ·
                  refine ⟨2122950849329755097919437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5661202264879346927785165 2122950849329755097919437)
                  ·
                    refine ⟨796106568498658161719789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2122950849329755097919437 796106568498658161719789)
                    ·
                      rfl

theorem cell22_2325618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_2325618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2325618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2325618 prefixEnd_2325618 := by exact prefixLift 2325618
  have htrace : WordTrace (prefixWord ++ tailWord_2325618) baseStart_2325618 baseEnd_2325618 := by
    simpa [prefixWord, tailWord_2325618, baseEnd_2325618] using wordTrace_append hprefix tailTrace_2325618
  have hstable : (prefixWord ++ tailWord_2325618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325618).length < 2 ^ (prefixWord ++ tailWord_2325618).sum := by decide
  have hdescent : baseEnd_2325618 < baseStart_2325618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325635 : List Nat := [1, 1, 1, 3, 3, 2, 4, 3, 1, 3]
def baseStart_2325635 : Nat := 118140960795 + 2325635 * 2 ^ 59
def prefixEnd_2325635 : Nat := 4983230072969 + 3 ^ 40 * 2325635 * 2
def baseEnd_2325635 : Nat := 796112387946075784044737

theorem tailTrace_2325635 : CollatzResearch.WordTrace tailWord_2325635 prefixEnd_2325635 796112387946075784044737 := by
  unfold tailWord_2325635
  simp only [CollatzResearch.WordTrace]
  refine ⟨84822876929629056681450359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56548584619752704454300239 84822876929629056681450359)
  ·
    refine ⟨127234315394443585022175539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84822876929629056681450359 127234315394443585022175539)
    ·
      refine ⟨190851473091665377533263309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127234315394443585022175539 190851473091665377533263309)
      ·
        refine ⟨71569302409374516574973741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190851473091665377533263309 71569302409374516574973741)
        ·
          refine ⟨26838488403515443715615153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71569302409374516574973741 26838488403515443715615153)
          ·
            refine ⟨20128866302636582786711365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26838488403515443715615153 20128866302636582786711365)
            ·
              refine ⟨3774162431744359272508381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20128866302636582786711365 3774162431744359272508381)
              ·
                refine ⟨1415310911904134727190643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3774162431744359272508381 1415310911904134727190643)
                ·
                  refine ⟨2122966367856202090785965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1415310911904134727190643 2122966367856202090785965)
                  ·
                    refine ⟨796112387946075784044737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2122966367856202090785965 796112387946075784044737)
                    ·
                      rfl

theorem cell22_2325635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 1, 3].length) (baseStart_2325635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2325635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2325635 prefixEnd_2325635 := by exact prefixLift 2325635
  have htrace : WordTrace (prefixWord ++ tailWord_2325635) baseStart_2325635 baseEnd_2325635 := by
    simpa [prefixWord, tailWord_2325635, baseEnd_2325635] using wordTrace_append hprefix tailTrace_2325635
  have hstable : (prefixWord ++ tailWord_2325635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325635).length < 2 ^ (prefixWord ++ tailWord_2325635).sum := by decide
  have hdescent : baseEnd_2325635 < baseStart_2325635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325710 : List Nat := [4, 1, 1, 1, 5, 2, 1, 1, 6]
def baseStart_2325710 : Nat := 118140960795 + 2325710 * 2 ^ 59
def prefixEnd_2325710 : Nat := 4983230072969 + 3 ^ 40 * 2325710 * 2
def baseEnd_2325710 : Nat := 265379353992933529473169

theorem tailTrace_2325710 : CollatzResearch.WordTrace tailWord_2325710 prefixEnd_2325710 265379353992933529473169 := by
  unfold tailWord_2325710
  simp only [CollatzResearch.WordTrace]
  refine ⟨10603201550544668061303823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56550408269571562993620389 10603201550544668061303823)
  ·
    refine ⟨15904802325817002091955735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10603201550544668061303823 15904802325817002091955735)
    ·
      refine ⟨23857203488725503137933603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15904802325817002091955735 23857203488725503137933603)
      ·
        refine ⟨35785805233088254706900405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23857203488725503137933603 35785805233088254706900405)
        ·
          refine ⟨3354919240602023878771913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35785805233088254706900405 3354919240602023878771913)
          ·
            refine ⟨2516189430451517909078935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3354919240602023878771913 2516189430451517909078935)
            ·
              refine ⟨3774284145677276863618403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2516189430451517909078935 3774284145677276863618403)
              ·
                refine ⟨5661426218515915295427605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3774284145677276863618403 5661426218515915295427605)
                ·
                  refine ⟨265379353992933529473169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5661426218515915295427605 265379353992933529473169)
                  ·
                    rfl

theorem cell22_2325710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_2325710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2325710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2325710 prefixEnd_2325710 := by exact prefixLift 2325710
  have htrace : WordTrace (prefixWord ++ tailWord_2325710) baseStart_2325710 baseEnd_2325710 := by
    simpa [prefixWord, tailWord_2325710, baseEnd_2325710] using wordTrace_append hprefix tailTrace_2325710
  have hstable : (prefixWord ++ tailWord_2325710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325710).length < 2 ^ (prefixWord ++ tailWord_2325710).sum := by decide
  have hdescent : baseEnd_2325710 < baseStart_2325710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325783 : List Nat := [1, 1, 3, 4, 1, 1, 1, 5, 5]
def baseStart_2325783 : Nat := 118140960795 + 2325783 * 2 ^ 59
def prefixEnd_2325783 : Nat := 4983230072969 + 3 ^ 40 * 2325783 * 2
def baseEnd_2325783 : Nat := 265387683790217577114761

theorem tailTrace_2325783 : CollatzResearch.WordTrace tailWord_2325783 prefixEnd_2325783 265387683790217577114761 := by
  unfold tailWord_2325783
  simp only [CollatzResearch.WordTrace]
  refine ⟨84828274933092877957838003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56552183288728585305225335 84828274933092877957838003)
  ·
    refine ⟨127242412399639316936757005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84828274933092877957838003 127242412399639316936757005)
    ·
      refine ⟨47715904649864743851283877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127242412399639316936757005 47715904649864743851283877)
      ·
        refine ⟨8946732121849639472115727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47715904649864743851283877 8946732121849639472115727)
        ·
          refine ⟨13420098182774459208173591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8946732121849639472115727 13420098182774459208173591)
          ·
            refine ⟨20130147274161688812260387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13420098182774459208173591 20130147274161688812260387)
            ·
              refine ⟨30195220911242533218390581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20130147274161688812260387 30195220911242533218390581)
              ·
                refine ⟨2830801960428987489224117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30195220911242533218390581 2830801960428987489224117)
                ·
                  refine ⟨265387683790217577114761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2830801960428987489224117 265387683790217577114761)
                  ·
                    rfl

theorem cell22_2325783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 5].length) (baseStart_2325783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2325783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2325783 prefixEnd_2325783 := by exact prefixLift 2325783
  have htrace : WordTrace (prefixWord ++ tailWord_2325783) baseStart_2325783 baseEnd_2325783 := by
    simpa [prefixWord, tailWord_2325783, baseEnd_2325783] using wordTrace_append hprefix tailTrace_2325783
  have hstable : (prefixWord ++ tailWord_2325783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325783).length < 2 ^ (prefixWord ++ tailWord_2325783).sum := by decide
  have hdescent : baseEnd_2325783 < baseStart_2325783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325817 : List Nat := [1, 2, 1, 6, 2, 2, 1, 2, 5]
def baseStart_2325817 : Nat := 118140960795 + 2325817 * 2 ^ 59
def prefixEnd_2325817 : Nat := 4983230072969 + 3 ^ 40 * 2325817 * 2
def baseEnd_2325817 : Nat := 265391563421829325331393

theorem tailTrace_2325817 : CollatzResearch.WordTrace tailWord_2325817 prefixEnd_2325817 265391563421829325331393 := by
  unfold tailWord_2325817
  simp only [CollatzResearch.WordTrace]
  refine ⟨84829515014969701764575705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56553010009979801176383803 84829515014969701764575705)
  ·
    refine ⟨63622136261227276323431779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84829515014969701764575705 63622136261227276323431779)
    ·
      refine ⟨95433204391840914485147669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63622136261227276323431779 95433204391840914485147669)
      ·
        refine ⟨4473431455867542866491297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 95433204391840914485147669 4473431455867542866491297)
        ·
          refine ⟨3355073591900657149868473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4473431455867542866491297 3355073591900657149868473)
          ·
            refine ⟨2516305193925492862401355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3355073591900657149868473 2516305193925492862401355)
            ·
              refine ⟨3774457790888239293602033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2516305193925492862401355 3774457790888239293602033)
              ·
                refine ⟨2830843343166179470201525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3774457790888239293602033 2830843343166179470201525)
                ·
                  refine ⟨265391563421829325331393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2830843343166179470201525 265391563421829325331393)
                  ·
                    rfl

theorem cell22_2325817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 5].length) (baseStart_2325817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2325817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2325817 prefixEnd_2325817 := by exact prefixLift 2325817
  have htrace : WordTrace (prefixWord ++ tailWord_2325817) baseStart_2325817 baseEnd_2325817 := by
    simpa [prefixWord, tailWord_2325817, baseEnd_2325817] using wordTrace_append hprefix tailTrace_2325817
  have hstable : (prefixWord ++ tailWord_2325817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325817).length < 2 ^ (prefixWord ++ tailWord_2325817).sum := by decide
  have hdescent : baseEnd_2325817 < baseStart_2325817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325860 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 4, 3]
def baseStart_2325860 : Nat := 118140960795 + 2325860 * 2 ^ 59
def prefixEnd_2325860 : Nat := 4983230072969 + 3 ^ 40 * 2325860 * 2
def baseEnd_2325860 : Nat := 796189410044250197169047

theorem tailTrace_2325860 : CollatzResearch.WordTrace tailWord_2325860 prefixEnd_2325860 796189410044250197169047 := by
  unfold tailWord_2325860
  simp only [CollatzResearch.WordTrace]
  refine ⟨42415541676906960054195517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56554055569209280072260689 42415541676906960054195517)
  ·
    refine ⟨15905828128840110020323319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42415541676906960054195517 15905828128840110020323319)
    ·
      refine ⟨23858742193260165030484979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15905828128840110020323319 23858742193260165030484979)
      ·
        refine ⟨35788113289890247545727469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23858742193260165030484979 35788113289890247545727469)
        ·
          refine ⟨13420542483708842829647801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35788113289890247545727469 13420542483708842829647801)
          ·
            refine ⟨10065406862781632122235851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13420542483708842829647801 10065406862781632122235851)
            ·
              refine ⟨15098110294172448183353777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10065406862781632122235851 15098110294172448183353777)
              ·
                refine ⟨11323582720629336137515333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15098110294172448183353777 11323582720629336137515333)
                ·
                  refine ⟨2123171760118000525784125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11323582720629336137515333 2123171760118000525784125)
                  ·
                    refine ⟨796189410044250197169047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2123171760118000525784125 796189410044250197169047)
                    ·
                      rfl

theorem cell22_2325860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_2325860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2325860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2325860 prefixEnd_2325860 := by exact prefixLift 2325860
  have htrace : WordTrace (prefixWord ++ tailWord_2325860) baseStart_2325860 baseEnd_2325860 := by
    simpa [prefixWord, tailWord_2325860, baseEnd_2325860] using wordTrace_append hprefix tailTrace_2325860
  have hstable : (prefixWord ++ tailWord_2325860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325860).length < 2 ^ (prefixWord ++ tailWord_2325860).sum := by decide
  have hdescent : baseEnd_2325860 < baseStart_2325860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325963 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 8]
def baseStart_2325963 : Nat := 118140960795 + 2325963 * 2 ^ 59
def prefixEnd_2325963 : Nat := 4983230072969 + 3 ^ 40 * 2325963 * 2
def baseEnd_2325963 : Nat := 265408223016397420614577

theorem tailTrace_2325963 : CollatzResearch.WordTrace tailWord_2325963 prefixEnd_2325963 265408223016397420614577 := by
  unfold tailWord_2325963
  simp only [CollatzResearch.WordTrace]
  refine ⟨84834840072440768699390543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56556560048293845799593695 84834840072440768699390543)
  ·
    refine ⟨127252260108661153049085815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84834840072440768699390543 127252260108661153049085815)
    ·
      refine ⟨190878390162991729573628723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127252260108661153049085815 190878390162991729573628723)
      ·
        refine ⟨286317585244487594360443085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190878390162991729573628723 286317585244487594360443085)
        ·
          refine ⟨107369094466682847885166157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 286317585244487594360443085 107369094466682847885166157)
          ·
            refine ⟨40263410425006067956937309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107369094466682847885166157 40263410425006067956937309)
            ·
              refine ⟨15098778909377275483851491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40263410425006067956937309 15098778909377275483851491)
              ·
                refine ⟨22648168364065913225777237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15098778909377275483851491 22648168364065913225777237)
                ·
                  refine ⟨265408223016397420614577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22648168364065913225777237 265408223016397420614577)
                  ·
                    rfl

theorem cell22_2325963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 8].length) (baseStart_2325963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2325963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2325963 prefixEnd_2325963 := by exact prefixLift 2325963
  have htrace : WordTrace (prefixWord ++ tailWord_2325963) baseStart_2325963 baseEnd_2325963 := by
    simpa [prefixWord, tailWord_2325963, baseEnd_2325963] using wordTrace_append hprefix tailTrace_2325963
  have hstable : (prefixWord ++ tailWord_2325963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325963).length < 2 ^ (prefixWord ++ tailWord_2325963).sum := by decide
  have hdescent : baseEnd_2325963 < baseStart_2325963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326012 : List Nat := [2, 2, 2, 1, 2, 1, 2, 5, 2, 3]
def baseStart_2326012 : Nat := 118140960795 + 2326012 * 2 ^ 59
def prefixEnd_2326012 : Nat := 4983230072969 + 3 ^ 40 * 2326012 * 2
def baseEnd_2326012 : Nat := 796241442750572467368581

theorem tailTrace_2326012 : CollatzResearch.WordTrace tailWord_2326012 prefixEnd_2326012 796241442750572467368581 := by
  unfold tailWord_2326012
  simp only [CollatzResearch.WordTrace]
  refine ⟨42418313624631625033962145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56557751499508833378616193 42418313624631625033962145)
  ·
    refine ⟨31813735218473718775471609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42418313624631625033962145 31813735218473718775471609)
    ·
      refine ⟨23860301413855289081603707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31813735218473718775471609 23860301413855289081603707)
      ·
        refine ⟨35790452120782933622405561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23860301413855289081603707 35790452120782933622405561)
        ·
          refine ⟨26842839090587200216804171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35790452120782933622405561 26842839090587200216804171)
          ·
            refine ⟨40264258635880800325206257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26842839090587200216804171 40264258635880800325206257)
            ·
              refine ⟨30198193976910600243904693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40264258635880800325206257 30198193976910600243904693)
              ·
                refine ⟨2831080685335368772866065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30198193976910600243904693 2831080685335368772866065)
                ·
                  refine ⟨2123310514001526579649549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2831080685335368772866065 2123310514001526579649549)
                  ·
                    refine ⟨796241442750572467368581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2123310514001526579649549 796241442750572467368581)
                    ·
                      rfl

theorem cell22_2326012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_2326012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326012 prefixEnd_2326012 := by exact prefixLift 2326012
  have htrace : WordTrace (prefixWord ++ tailWord_2326012) baseStart_2326012 baseEnd_2326012 := by
    simpa [prefixWord, tailWord_2326012, baseEnd_2326012] using wordTrace_append hprefix tailTrace_2326012
  have hstable : (prefixWord ++ tailWord_2326012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326012).length < 2 ^ (prefixWord ++ tailWord_2326012).sum := by decide
  have hdescent : baseEnd_2326012 < baseStart_2326012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326108 : List Nat := [2, 2, 4, 1, 2, 1, 4, 2, 1, 3]
def baseStart_2326108 : Nat := 118140960795 + 2326108 * 2 ^ 59
def prefixEnd_2326108 : Nat := 4983230072969 + 3 ^ 40 * 2326108 * 2
def baseEnd_2326108 : Nat := 796274305512460216968287

theorem tailTrace_2326108 : CollatzResearch.WordTrace tailWord_2326108 prefixEnd_2326108 796274305512460216968287 := by
  unfold tailWord_2326108
  simp only [CollatzResearch.WordTrace]
  refine ⟨42420064328457729231709489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56560085771276972308945985 42420064328457729231709489)
  ·
    refine ⟨31815048246343296923782117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42420064328457729231709489 31815048246343296923782117)
    ·
      refine ⟨5965321546189368173209147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31815048246343296923782117 5965321546189368173209147)
      ·
        refine ⟨8947982319284052259813721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5965321546189368173209147 8947982319284052259813721)
        ·
          refine ⟨6710986739463039194860291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8947982319284052259813721 6710986739463039194860291)
          ·
            refine ⟨10066480109194558792290437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6710986739463039194860291 10066480109194558792290437)
            ·
              refine ⟨1887465020473979773554457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10066480109194558792290437 1887465020473979773554457)
              ·
                refine ⟨1415598765355484830165843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1887465020473979773554457 1415598765355484830165843)
                ·
                  refine ⟨2123398148033227245248765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1415598765355484830165843 2123398148033227245248765)
                  ·
                    refine ⟨796274305512460216968287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2123398148033227245248765 796274305512460216968287)
                    ·
                      rfl

theorem cell22_2326108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_2326108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326108 prefixEnd_2326108 := by exact prefixLift 2326108
  have htrace : WordTrace (prefixWord ++ tailWord_2326108) baseStart_2326108 baseEnd_2326108 := by
    simpa [prefixWord, tailWord_2326108, baseEnd_2326108] using wordTrace_append hprefix tailTrace_2326108
  have hstable : (prefixWord ++ tailWord_2326108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326108).length < 2 ^ (prefixWord ++ tailWord_2326108).sum := by decide
  have hdescent : baseEnd_2326108 < baseStart_2326108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326117 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 3, 4]
def baseStart_2326117 : Nat := 118140960795 + 2326117 * 2 ^ 59
def prefixEnd_2326117 : Nat := 4983230072969 + 3 ^ 40 * 2326117 * 2
def baseEnd_2326117 : Nat := 796277386396387193493259

theorem tailTrace_2326117 : CollatzResearch.WordTrace tailWord_2326117 prefixEnd_2326117 796277386396387193493259 := by
  unfold tailWord_2326117
  simp only [CollatzResearch.WordTrace]
  refine ⟨84840456913882853000496605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56560304609255235333664403 84840456913882853000496605)
  ·
    refine ⟨31815171342706069875186227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84840456913882853000496605 31815171342706069875186227)
    ·
      refine ⟨47722757014059104812779341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31815171342706069875186227 47722757014059104812779341)
      ·
        refine ⟨17896033880272164304792253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47722757014059104812779341 17896033880272164304792253)
        ·
          refine ⟨6711012705102061614297095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17896033880272164304792253 6711012705102061614297095)
          ·
            refine ⟨10066519057653092421445643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6711012705102061614297095 10066519057653092421445643)
            ·
              refine ⟨15099778586479638632168465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10066519057653092421445643 15099778586479638632168465)
              ·
                refine ⟨11324833939859728974126349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15099778586479638632168465 11324833939859728974126349)
                ·
                  refine ⟨4246812727447398365297381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11324833939859728974126349 4246812727447398365297381)
                  ·
                    refine ⟨796277386396387193493259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4246812727447398365297381 796277386396387193493259)
                    ·
                      rfl

theorem cell22_2326117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_2326117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326117 prefixEnd_2326117 := by exact prefixLift 2326117
  have htrace : WordTrace (prefixWord ++ tailWord_2326117) baseStart_2326117 baseEnd_2326117 := by
    simpa [prefixWord, tailWord_2326117, baseEnd_2326117] using wordTrace_append hprefix tailTrace_2326117
  have hstable : (prefixWord ++ tailWord_2326117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326117).length < 2 ^ (prefixWord ++ tailWord_2326117).sum := by decide
  have hdescent : baseEnd_2326117 < baseStart_2326117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326134 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_2326134 : Nat := 118140960795 + 2326134 * 2 ^ 59
def prefixEnd_2326134 : Nat := 4983230072969 + 3 ^ 40 * 2326134 * 2
def baseEnd_2326134 : Nat := 796283205843804815818207

theorem tailTrace_2326134 : CollatzResearch.WordTrace tailWord_2326134 prefixEnd_2326134 796283205843804815818207 := by
  unfold tailWord_2326134
  simp only [CollatzResearch.WordTrace]
  refine ⟨5302567309676329056491591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56560717969880843269243637 5302567309676329056491591)
  ·
    refine ⟨7953850964514493584737387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5302567309676329056491591 7953850964514493584737387)
    ·
      refine ⟨11930776446771740377106081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7953850964514493584737387 11930776446771740377106081)
      ·
        refine ⟨8948082335078805282829561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11930776446771740377106081 8948082335078805282829561)
        ·
          refine ⟨6711061751309103962122171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8948082335078805282829561 6711061751309103962122171)
          ·
            refine ⟨10066592626963655943183257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6711061751309103962122171 10066592626963655943183257)
            ·
              refine ⟨7549944470222741957387443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10066592626963655943183257 7549944470222741957387443)
              ·
                refine ⟨11324916705334112936081165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7549944470222741957387443 11324916705334112936081165)
                ·
                  refine ⟨4246843764500292351030437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11324916705334112936081165 4246843764500292351030437)
                  ·
                    refine ⟨796283205843804815818207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4246843764500292351030437 796283205843804815818207)
                    ·
                      rfl

theorem cell22_2326134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_2326134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326134 prefixEnd_2326134 := by exact prefixLift 2326134
  have htrace : WordTrace (prefixWord ++ tailWord_2326134) baseStart_2326134 baseEnd_2326134 := by
    simpa [prefixWord, tailWord_2326134, baseEnd_2326134] using wordTrace_append hprefix tailTrace_2326134
  have hstable : (prefixWord ++ tailWord_2326134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326134).length < 2 ^ (prefixWord ++ tailWord_2326134).sum := by decide
  have hdescent : baseEnd_2326134 < baseStart_2326134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326147 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 4, 3]
def baseStart_2326147 : Nat := 118140960795 + 2326147 * 2 ^ 59
def prefixEnd_2326147 : Nat := 4983230072969 + 3 ^ 40 * 2326147 * 2
def baseEnd_2326147 : Nat := 796287656009477115243167

theorem tailTrace_2326147 : CollatzResearch.WordTrace tailWord_2326147 prefixEnd_2326147 796287656009477115243167 := by
  unfold tailWord_2326147
  simp only [CollatzResearch.WordTrace]
  refine ⟨84841551103774168124088695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56561034069182778749392463 84841551103774168124088695)
  ·
    refine ⟨127262326655661252186133043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84841551103774168124088695 127262326655661252186133043)
    ·
      refine ⟨190893489983491878279199565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127262326655661252186133043 190893489983491878279199565)
      ·
        refine ⟨71585058743809454354699837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190893489983491878279199565 71585058743809454354699837)
        ·
          refine ⟨26844397028928545383012439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71585058743809454354699837 26844397028928545383012439)
          ·
            refine ⟨40266595543392818074518659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26844397028928545383012439 40266595543392818074518659)
            ·
              refine ⟨60399893315089227111777989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40266595543392818074518659 60399893315089227111777989)
              ·
                refine ⟨11324979996579230083458373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60399893315089227111777989 11324979996579230083458373)
                ·
                  refine ⟨2123433749358605640648445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11324979996579230083458373 2123433749358605640648445)
                  ·
                    refine ⟨796287656009477115243167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2123433749358605640648445 796287656009477115243167)
                    ·
                      rfl

theorem cell22_2326147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 3].length) (baseStart_2326147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326147 prefixEnd_2326147 := by exact prefixLift 2326147
  have htrace : WordTrace (prefixWord ++ tailWord_2326147) baseStart_2326147 baseEnd_2326147 := by
    simpa [prefixWord, tailWord_2326147, baseEnd_2326147] using wordTrace_append hprefix tailTrace_2326147
  have hstable : (prefixWord ++ tailWord_2326147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326147).length < 2 ^ (prefixWord ++ tailWord_2326147).sum := by decide
  have hdescent : baseEnd_2326147 < baseStart_2326147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326149 : List Nat := [1, 3, 1, 1, 4, 1, 4, 3, 4]
def baseStart_2326149 : Nat := 118140960795 + 2326149 * 2 ^ 59
def prefixEnd_2326149 : Nat := 4983230072969 + 3 ^ 40 * 2326149 * 2
def baseEnd_2326149 : Nat := 265429446883449925564387

theorem tailTrace_2326149 : CollatzResearch.WordTrace tailWord_2326149 prefixEnd_2326149 265429446883449925564387 := by
  unfold tailWord_2326149
  simp only [CollatzResearch.WordTrace]
  refine ⟨84841624049766922465661501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56561082699844614977107667 84841624049766922465661501)
  ·
    refine ⟨31815609018662595924623063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84841624049766922465661501 31815609018662595924623063)
    ·
      refine ⟨47723413527993893886934595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31815609018662595924623063 47723413527993893886934595)
      ·
        refine ⟨71585120291990840830401893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47723413527993893886934595 71585120291990840830401893)
        ·
          refine ⟨13422210054748282655700355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71585120291990840830401893 13422210054748282655700355)
          ·
            refine ⟨20133315082122423983550533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13422210054748282655700355 20133315082122423983550533)
            ·
              refine ⟨3774996577897954496915725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20133315082122423983550533 3774996577897954496915725)
              ·
                refine ⟨1415623716711732936343397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3774996577897954496915725 1415623716711732936343397)
                ·
                  refine ⟨265429446883449925564387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1415623716711732936343397 265429446883449925564387)
                  ·
                    rfl

theorem cell22_2326149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 4].length) (baseStart_2326149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326149 prefixEnd_2326149 := by exact prefixLift 2326149
  have htrace : WordTrace (prefixWord ++ tailWord_2326149) baseStart_2326149 baseEnd_2326149 := by
    simpa [prefixWord, tailWord_2326149, baseEnd_2326149] using wordTrace_append hprefix tailTrace_2326149
  have hstable : (prefixWord ++ tailWord_2326149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326149).length < 2 ^ (prefixWord ++ tailWord_2326149).sum := by decide
  have hdescent : baseEnd_2326149 < baseStart_2326149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326151 : List Nat := [1, 1, 4, 2, 1, 5, 2, 1, 1, 4]
def baseStart_2326151 : Nat := 118140960795 + 2326151 * 2 ^ 59
def prefixEnd_2326151 : Nat := 4983230072969 + 3 ^ 40 * 2326151 * 2
def baseEnd_2326151 : Nat := 796289025291222438143155

theorem tailTrace_2326151 : CollatzResearch.WordTrace tailWord_2326151 prefixEnd_2326151 796289025291222438143155 := by
  unfold tailWord_2326151
  simp only [CollatzResearch.WordTrace]
  refine ⟨84841696995759676807234307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56561131330506451204822871 84841696995759676807234307)
  ·
    refine ⟨127262545493639515210851461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84841696995759676807234307 127262545493639515210851461)
    ·
      refine ⟨23861727280057409102034649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127262545493639515210851461 23861727280057409102034649)
      ·
        refine ⟨17896295460043056826525987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23861727280057409102034649 17896295460043056826525987)
        ·
          refine ⟨26844443190064585239788981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17896295460043056826525987 26844443190064585239788981)
          ·
            refine ⟨2516666549068554866230217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26844443190064585239788981 2516666549068554866230217)
            ·
              refine ⟨1887499911801416149672663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2516666549068554866230217 1887499911801416149672663)
              ·
                refine ⟨2831249867702124224508995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1887499911801416149672663 2831249867702124224508995)
                ·
                  refine ⟨4246874801553186336763493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2831249867702124224508995 4246874801553186336763493)
                  ·
                    refine ⟨796289025291222438143155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4246874801553186336763493 796289025291222438143155)
                    ·
                      rfl

theorem cell22_2326151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_2326151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326151 prefixEnd_2326151 := by exact prefixLift 2326151
  have htrace : WordTrace (prefixWord ++ tailWord_2326151) baseStart_2326151 baseEnd_2326151 := by
    simpa [prefixWord, tailWord_2326151, baseEnd_2326151] using wordTrace_append hprefix tailTrace_2326151
  have hstable : (prefixWord ++ tailWord_2326151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326151).length < 2 ^ (prefixWord ++ tailWord_2326151).sum := by decide
  have hdescent : baseEnd_2326151 < baseStart_2326151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326222 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 7]
def baseStart_2326222 : Nat := 118140960795 + 2326222 * 2 ^ 59
def prefixEnd_2326222 : Nat := 4983230072969 + 3 ^ 40 * 2326222 * 2
def baseEnd_2326222 : Nat := 265437776680733973205979

theorem tailTrace_2326222 : CollatzResearch.WordTrace tailWord_2326222 prefixEnd_2326222 265437776680733973205979 := by
  unfold tailWord_2326222
  simp only [CollatzResearch.WordTrace]
  refine ⟨10605535822312806991633615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56562857719001637288712613 10605535822312806991633615)
  ·
    refine ⟨15908303733469210487450423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10605535822312806991633615 15908303733469210487450423)
    ·
      refine ⟨23862455600203815731175635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15908303733469210487450423 23862455600203815731175635)
      ·
        refine ⟨35793683400305723596763453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23862455600203815731175635 35793683400305723596763453)
        ·
          refine ⟨13422631275114646348786295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35793683400305723596763453 13422631275114646348786295)
          ·
            refine ⟨20133946912671969523179443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13422631275114646348786295 20133946912671969523179443)
            ·
              refine ⟨30200920369007954284769165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20133946912671969523179443 30200920369007954284769165)
              ·
                refine ⟨11325345138377982856788437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30200920369007954284769165 11325345138377982856788437)
                ·
                  refine ⟨265437776680733973205979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11325345138377982856788437 265437776680733973205979)
                  ·
                    rfl

theorem cell22_2326222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_2326222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326222 prefixEnd_2326222 := by exact prefixLift 2326222
  have htrace : WordTrace (prefixWord ++ tailWord_2326222) baseStart_2326222 baseEnd_2326222 := by
    simpa [prefixWord, tailWord_2326222, baseEnd_2326222] using wordTrace_append hprefix tailTrace_2326222
  have hstable : (prefixWord ++ tailWord_2326222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326222).length < 2 ^ (prefixWord ++ tailWord_2326222).sum := by decide
  have hdescent : baseEnd_2326222 < baseStart_2326222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326226 : List Nat := [3, 2, 2, 2, 2, 1, 3, 1, 3, 3]
def baseStart_2326226 : Nat := 118140960795 + 2326226 * 2 ^ 59
def prefixEnd_2326226 : Nat := 4983230072969 + 3 ^ 40 * 2326226 * 2
def baseEnd_2326226 : Nat := 796314699323947242517925

theorem tailTrace_2326226 : CollatzResearch.WordTrace tailWord_2326226 prefixEnd_2326226 796314699323947242517925 := by
  unfold tailWord_2326226
  simp only [CollatzResearch.WordTrace]
  refine ⟨21211108117621991154053633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56562954980325309744143021 21211108117621991154053633)
  ·
    refine ⟨15908331088216493365540225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21211108117621991154053633 15908331088216493365540225)
    ·
      refine ⟨11931248316162370024155169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15908331088216493365540225 11931248316162370024155169)
      ·
        refine ⟨8948436237121777518116377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11931248316162370024155169 8948436237121777518116377)
        ·
          refine ⟨6711327177841333138587283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8948436237121777518116377 6711327177841333138587283)
          ·
            refine ⟨10066990766761999707880925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6711327177841333138587283 10066990766761999707880925)
            ·
              refine ⟨3775121537535749890455347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10066990766761999707880925 3775121537535749890455347)
              ·
                refine ⟨5662682306303624835683021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3775121537535749890455347 5662682306303624835683021)
                ·
                  refine ⟨2123505864863859313381133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5662682306303624835683021 2123505864863859313381133)
                  ·
                    refine ⟨796314699323947242517925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2123505864863859313381133 796314699323947242517925)
                    ·
                      rfl

theorem cell22_2326226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_2326226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326226 prefixEnd_2326226 := by exact prefixLift 2326226
  have htrace : WordTrace (prefixWord ++ tailWord_2326226) baseStart_2326226 baseEnd_2326226 := by
    simpa [prefixWord, tailWord_2326226, baseEnd_2326226] using wordTrace_append hprefix tailTrace_2326226
  have hstable : (prefixWord ++ tailWord_2326226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326226).length < 2 ^ (prefixWord ++ tailWord_2326226).sum := by decide
  have hdescent : baseEnd_2326226 < baseStart_2326226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326333 : List Nat := [1, 4, 1, 4, 1, 1, 3, 2, 2, 3]
def baseStart_2326333 : Nat := 118140960795 + 2326333 * 2 ^ 59
def prefixEnd_2326333 : Nat := 4983230072969 + 3 ^ 40 * 2326333 * 2
def baseEnd_2326333 : Nat := 796351327610634630092597

theorem tailTrace_2326333 : CollatzResearch.WordTrace tailWord_2326333 prefixEnd_2326333 796351327610634630092597 := by
  unfold tailWord_2326333
  simp only [CollatzResearch.WordTrace]
  refine ⟨84848335081100321890359653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56565556720733547926906435 84848335081100321890359653)
  ·
    refine ⟨15909062827706310354442435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84848335081100321890359653 15909062827706310354442435)
    ·
      refine ⟨23863594241559465531663653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15909062827706310354442435 23863594241559465531663653)
      ·
        refine ⟨4474423920292399787186935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23863594241559465531663653 4474423920292399787186935)
        ·
          refine ⟨6711635880438599680780403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4474423920292399787186935 6711635880438599680780403)
          ·
            refine ⟨10067453820657899521170605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6711635880438599680780403 10067453820657899521170605)
            ·
              refine ⟨3775295182746712320438977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10067453820657899521170605 3775295182746712320438977)
              ·
                refine ⟨2831471387060034240329233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3775295182746712320438977 2831471387060034240329233)
                ·
                  refine ⟨2123603540295025680246925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2831471387060034240329233 2123603540295025680246925)
                  ·
                    refine ⟨796351327610634630092597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2123603540295025680246925 796351327610634630092597)
                    ·
                      rfl

theorem cell22_2326333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_2326333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326333 prefixEnd_2326333 := by exact prefixLift 2326333
  have htrace : WordTrace (prefixWord ++ tailWord_2326333) baseStart_2326333 baseEnd_2326333 := by
    simpa [prefixWord, tailWord_2326333, baseEnd_2326333] using wordTrace_append hprefix tailTrace_2326333
  have hstable : (prefixWord ++ tailWord_2326333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326333).length < 2 ^ (prefixWord ++ tailWord_2326333).sum := by decide
  have hdescent : baseEnd_2326333 < baseStart_2326333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326453 : List Nat := [1, 3, 3, 2, 1, 3, 1, 4, 4]
def baseStart_2326453 : Nat := 118140960795 + 2326453 * 2 ^ 59
def prefixEnd_2326453 : Nat := 4983230072969 + 3 ^ 40 * 2326453 * 2
def baseEnd_2326453 : Nat := 265464135354331439030743

theorem tailTrace_2326453 : CollatzResearch.WordTrace tailWord_2326453 prefixEnd_2326453 265464135354331439030743 := by
  unfold tailWord_2326453
  simp only [CollatzResearch.WordTrace]
  refine ⟨84852711840665582384728013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56568474560443721589818675 84852711840665582384728013)
  ·
    refine ⟨31819766940249593394273005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84852711840665582384728013 31819766940249593394273005)
    ·
      refine ⟨11932412602593597522852377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31819766940249593394273005 11932412602593597522852377)
      ·
        refine ⟨8949309451945198142139283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11932412602593597522852377 8949309451945198142139283)
        ·
          refine ⟨13423964177917797213208925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8949309451945198142139283 13423964177917797213208925)
          ·
            refine ⟨5033986566719173954953347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13423964177917797213208925 5033986566719173954953347)
            ·
              refine ⟨7550979850078760932430021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5033986566719173954953347 7550979850078760932430021)
              ·
                refine ⟨1415808721889767674830629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7550979850078760932430021 1415808721889767674830629)
                ·
                  refine ⟨265464135354331439030743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1415808721889767674830629 265464135354331439030743)
                  ·
                    rfl

theorem cell22_2326453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 4].length) (baseStart_2326453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326453 prefixEnd_2326453 := by exact prefixLift 2326453
  have htrace : WordTrace (prefixWord ++ tailWord_2326453) baseStart_2326453 baseEnd_2326453 := by
    simpa [prefixWord, tailWord_2326453, baseEnd_2326453] using wordTrace_append hprefix tailTrace_2326453
  have hstable : (prefixWord ++ tailWord_2326453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326453).length < 2 ^ (prefixWord ++ tailWord_2326453).sum := by decide
  have hdescent : baseEnd_2326453 < baseStart_2326453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326498 : List Nat := [3, 3, 3, 1, 2, 1, 9]
def baseStart_2326498 : Nat := 118140960795 + 2326498 * 2 ^ 59
def prefixEnd_2326498 : Nat := 4983230072969 + 3 ^ 40 * 2326498 * 2
def baseEnd_2326498 : Nat := 29496585573430711100633

theorem tailTrace_2326498 : CollatzResearch.WordTrace tailWord_2326498 prefixEnd_2326498 29496585573430711100633 := by
  unfold tailWord_2326498
  simp only [CollatzResearch.WordTrace]
  refine ⟨21213588281375638767529037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56569568750335036713410765 21213588281375638767529037)
  ·
    refine ⟨7955095605515864537823389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21213588281375638767529037 7955095605515864537823389)
    ·
      refine ⟨2983160852068449201683771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7955095605515864537823389 2983160852068449201683771)
      ·
        refine ⟨4474741278102673802525657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2983160852068449201683771 4474741278102673802525657)
        ·
          refine ⟨3356055958577005351894243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4474741278102673802525657 3356055958577005351894243)
          ·
            refine ⟨5034083937865508027841365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3356055958577005351894243 5034083937865508027841365)
            ·
              refine ⟨29496585573430711100633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5034083937865508027841365 29496585573430711100633)
              ·
                rfl

theorem cell22_2326498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 9].length) (baseStart_2326498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326498 prefixEnd_2326498 := by exact prefixLift 2326498
  have htrace : WordTrace (prefixWord ++ tailWord_2326498) baseStart_2326498 baseEnd_2326498 := by
    simpa [prefixWord, tailWord_2326498, baseEnd_2326498] using wordTrace_append hprefix tailTrace_2326498
  have hstable : (prefixWord ++ tailWord_2326498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326498).length < 2 ^ (prefixWord ++ tailWord_2326498).sum := by decide
  have hdescent : baseEnd_2326498 < baseStart_2326498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326532 : List Nat := [2, 3, 2, 4, 2, 1, 2, 6]
def baseStart_2326532 : Nat := 118140960795 + 2326532 * 2 ^ 59
def prefixEnd_2326532 : Nat := 4983230072969 + 3 ^ 40 * 2326532 * 2
def baseEnd_2326532 : Nat := 88491049930829382707443

theorem tailTrace_2326532 : CollatzResearch.WordTrace tailWord_2326532 prefixEnd_2326532 88491049930829382707443 := by
  unfold tailWord_2326532
  simp only [CollatzResearch.WordTrace]
  refine ⟨42427796603689689438426925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56570395471586252584569233 42427796603689689438426925)
  ·
    refine ⟨15910423726383633539410097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42427796603689689438426925 15910423726383633539410097)
    ·
      refine ⟨11932817794787725154557573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15910423726383633539410097 11932817794787725154557573)
      ·
        refine ⟨2237403336522698466479545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11932817794787725154557573 2237403336522698466479545)
        ·
          refine ⟨1678052502392023849859659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2237403336522698466479545 1678052502392023849859659)
          ·
            refine ⟨2517078753588035774789489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1678052502392023849859659 2517078753588035774789489)
            ·
              refine ⟨1887809065191026831092117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2517078753588035774789489 1887809065191026831092117)
              ·
                refine ⟨88491049930829382707443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1887809065191026831092117 88491049930829382707443)
                ·
                  rfl

theorem cell22_2326532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 6].length) (baseStart_2326532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326532 prefixEnd_2326532 := by exact prefixLift 2326532
  have htrace : WordTrace (prefixWord ++ tailWord_2326532) baseStart_2326532 baseEnd_2326532 := by
    simpa [prefixWord, tailWord_2326532, baseEnd_2326532] using wordTrace_append hprefix tailTrace_2326532
  have hstable : (prefixWord ++ tailWord_2326532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326532).length < 2 ^ (prefixWord ++ tailWord_2326532).sum := by decide
  have hdescent : baseEnd_2326532 < baseStart_2326532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326564 : List Nat := [2, 3, 1, 4, 2, 1, 3, 2, 1, 3]
def baseStart_2326564 : Nat := 118140960795 + 2326564 * 2 ^ 59
def prefixEnd_2326564 : Nat := 4983230072969 + 3 ^ 40 * 2326564 * 2
def baseEnd_2326564 : Nat := 796430403631427027566889

theorem tailTrace_2326564 : CollatzResearch.WordTrace tailWord_2326564 prefixEnd_2326564 796430403631427027566889 := by
  unfold tailWord_2326564
  simp only [CollatzResearch.WordTrace]
  refine ⟨42428380171631724171009373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56571173562175632228012497 42428380171631724171009373)
  ·
    refine ⟨15910642564361896564128515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42428380171631724171009373 15910642564361896564128515)
    ·
      refine ⟨23865963846542844846192773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15910642564361896564128515 23865963846542844846192773)
      ·
        refine ⟨4474868221226783408661145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23865963846542844846192773 4474868221226783408661145)
        ·
          refine ⟨3356151165920087556495859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4474868221226783408661145 3356151165920087556495859)
          ·
            refine ⟨5034226748880131334743789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3356151165920087556495859 5034226748880131334743789)
            ·
              refine ⟨1887835030830049250528921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5034226748880131334743789 1887835030830049250528921)
              ·
                refine ⟨1415876273122536937896691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1887835030830049250528921 1415876273122536937896691)
                ·
                  refine ⟨2123814409683805406845037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1415876273122536937896691 2123814409683805406845037)
                  ·
                    refine ⟨796430403631427027566889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2123814409683805406845037 796430403631427027566889)
                    ·
                      rfl

theorem cell22_2326564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_2326564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326564 prefixEnd_2326564 := by exact prefixLift 2326564
  have htrace : WordTrace (prefixWord ++ tailWord_2326564) baseStart_2326564 baseEnd_2326564 := by
    simpa [prefixWord, tailWord_2326564, baseEnd_2326564] using wordTrace_append hprefix tailTrace_2326564
  have hstable : (prefixWord ++ tailWord_2326564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326564).length < 2 ^ (prefixWord ++ tailWord_2326564).sum := by decide
  have hdescent : baseEnd_2326564 < baseStart_2326564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326586 : List Nat := [3, 1, 1, 1, 3, 1, 1, 5, 1, 5]
def baseStart_2326586 : Nat := 118140960795 + 2326586 * 2 ^ 59
def prefixEnd_2326586 : Nat := 4983230072969 + 3 ^ 40 * 2326586 * 2
def baseEnd_2326586 : Nat := 796437934681026303516821

theorem tailTrace_2326586 : CollatzResearch.WordTrace tailWord_2326586 prefixEnd_2326586 796437934681026303516821 := by
  unfold tailWord_2326586
  simp only [CollatzResearch.WordTrace]
  refine ⟨21214390687295936524829903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56571708499455830732879741 21214390687295936524829903)
  ·
    refine ⟨31821586030943904787244855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21214390687295936524829903 31821586030943904787244855)
    ·
      refine ⟨47732379046415857180867283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31821586030943904787244855 47732379046415857180867283)
      ·
        refine ⟨71598568569623785771300925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47732379046415857180867283 71598568569623785771300925)
        ·
          refine ⟨26849463213608919664237847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71598568569623785771300925 26849463213608919664237847)
          ·
            refine ⟨40274194820413379496356771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26849463213608919664237847 40274194820413379496356771)
            ·
              refine ⟨60411292230620069244535157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40274194820413379496356771 60411292230620069244535157)
              ·
                refine ⟨5663558646620631491675171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60411292230620069244535157 5663558646620631491675171)
                ·
                  refine ⟨8495337969930947237512757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5663558646620631491675171 8495337969930947237512757)
                  ·
                    refine ⟨796437934681026303516821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8495337969930947237512757 796437934681026303516821)
                    ·
                      rfl

theorem cell22_2326586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_2326586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326586 prefixEnd_2326586 := by exact prefixLift 2326586
  have htrace : WordTrace (prefixWord ++ tailWord_2326586) baseStart_2326586 baseEnd_2326586 := by
    simpa [prefixWord, tailWord_2326586, baseEnd_2326586] using wordTrace_append hprefix tailTrace_2326586
  have hstable : (prefixWord ++ tailWord_2326586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326586).length < 2 ^ (prefixWord ++ tailWord_2326586).sum := by decide
  have hdescent : baseEnd_2326586 < baseStart_2326586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326590 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_2326590 : Nat := 118140960795 + 2326590 * 2 ^ 59
def prefixEnd_2326590 : Nat := 4983230072969 + 3 ^ 40 * 2326590 * 2
def baseEnd_2326590 : Nat := 796439303962771626416809

theorem tailTrace_2326590 : CollatzResearch.WordTrace tailWord_2326590 prefixEnd_2326590 796439303962771626416809 := by
  unfold tailWord_2326590
  simp only [CollatzResearch.WordTrace]
  refine ⟨10607213580146156847808153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56571805760779503188310149 10607213580146156847808153)
  ·
    refine ⟨7955410185109617635856115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10607213580146156847808153 7955410185109617635856115)
    ·
      refine ⟨11933115277664426453784173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7955410185109617635856115 11933115277664426453784173)
      ·
        refine ⟨4474918229124159920169065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11933115277664426453784173 4474918229124159920169065)
        ·
          refine ⟨3356188671843119940126799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4474918229124159920169065 3356188671843119940126799)
          ·
            refine ⟨5034283007764679910190199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3356188671843119940126799 5034283007764679910190199)
            ·
              refine ⟨7551424511647019865285299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5034283007764679910190199 7551424511647019865285299)
              ·
                refine ⟨11327136767470529797927949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7551424511647019865285299 11327136767470529797927949)
                ·
                  refine ⟨4247676287801448674222981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11327136767470529797927949 4247676287801448674222981)
                  ·
                    refine ⟨796439303962771626416809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4247676287801448674222981 796439303962771626416809)
                    ·
                      rfl

theorem cell22_2326590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_2326590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326590 prefixEnd_2326590 := by exact prefixLift 2326590
  have htrace : WordTrace (prefixWord ++ tailWord_2326590) baseStart_2326590 baseEnd_2326590 := by
    simpa [prefixWord, tailWord_2326590, baseEnd_2326590] using wordTrace_append hprefix tailTrace_2326590
  have hstable : (prefixWord ++ tailWord_2326590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326590).length < 2 ^ (prefixWord ++ tailWord_2326590).sum := by decide
  have hdescent : baseEnd_2326590 < baseStart_2326590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326605 : List Nat := [1, 6, 1, 1, 1, 1, 2, 5, 4]
def baseStart_2326605 : Nat := 118140960795 + 2326605 * 2 ^ 59
def prefixEnd_2326605 : Nat := 4983230072969 + 3 ^ 40 * 2326605 * 2
def baseEnd_2326605 : Nat := 265481479589772195763921

theorem tailTrace_2326605 : CollatzResearch.WordTrace tailWord_2326605 prefixEnd_2326605 265481479589772195763921 := by
  unfold tailWord_2326605
  simp only [CollatzResearch.WordTrace]
  refine ⟨84858255736114912344261269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56572170490743274896174179 84858255736114912344261269)
  ·
    refine ⟨3977730737630386516137247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 84858255736114912344261269 3977730737630386516137247)
    ·
      refine ⟨5966596106445579774205871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3977730737630386516137247 5966596106445579774205871)
      ·
        refine ⟨8949894159668369661308807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5966596106445579774205871 8949894159668369661308807)
        ·
          refine ⟨13424841239502554491963211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8949894159668369661308807 13424841239502554491963211)
          ·
            refine ⟨20137261859253831737944817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13424841239502554491963211 20137261859253831737944817)
            ·
              refine ⟨15102946394440373803458613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20137261859253831737944817 15102946394440373803458613)
              ·
                refine ⟨1415901224478785044074245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15102946394440373803458613 1415901224478785044074245)
                ·
                  refine ⟨265481479589772195763921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1415901224478785044074245 265481479589772195763921)
                  ·
                    rfl

theorem cell22_2326605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_2326605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326605 prefixEnd_2326605 := by exact prefixLift 2326605
  have htrace : WordTrace (prefixWord ++ tailWord_2326605) baseStart_2326605 baseEnd_2326605 := by
    simpa [prefixWord, tailWord_2326605, baseEnd_2326605] using wordTrace_append hprefix tailTrace_2326605
  have hstable : (prefixWord ++ tailWord_2326605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326605).length < 2 ^ (prefixWord ++ tailWord_2326605).sum := by decide
  have hdescent : baseEnd_2326605 < baseStart_2326605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326620 : List Nat := [2, 2, 4, 1, 1, 2, 1, 4, 2, 3]
def baseStart_2326620 : Nat := 118140960795 + 2326620 * 2 ^ 59
def prefixEnd_2326620 : Nat := 4983230072969 + 3 ^ 40 * 2326620 * 2
def baseEnd_2326620 : Nat := 796449573575861548166717

theorem tailTrace_2326620 : CollatzResearch.WordTrace tailWord_2326620 prefixEnd_2326620 796449573575861548166717 := by
  unfold tailWord_2326620
  simp only [CollatzResearch.WordTrace]
  refine ⟨42429401415530284953028657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56572535220707046604038209 42429401415530284953028657)
  ·
    refine ⟨31822051061647713714771493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42429401415530284953028657 31822051061647713714771493)
    ·
      refine ⟨5966634574058946321519655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31822051061647713714771493 5966634574058946321519655)
      ·
        refine ⟨8949951861088419482279483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5966634574058946321519655 8949951861088419482279483)
        ·
          refine ⟨13424927791632629223419225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8949951861088419482279483 13424927791632629223419225)
          ·
            refine ⟨10068695843724471917564419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13424927791632629223419225 10068695843724471917564419)
            ·
              refine ⟨15103043765586707876346629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10068695843724471917564419 15103043765586707876346629)
              ·
                refine ⟨2831820706047507726814993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15103043765586707876346629 2831820706047507726814993)
                ·
                  refine ⟨2123865529535630795111245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2831820706047507726814993 2123865529535630795111245)
                  ·
                    refine ⟨796449573575861548166717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2123865529535630795111245 796449573575861548166717)
                    ·
                      rfl

theorem cell22_2326620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_2326620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326620 prefixEnd_2326620 := by exact prefixLift 2326620
  have htrace : WordTrace (prefixWord ++ tailWord_2326620) baseStart_2326620 baseEnd_2326620 := by
    simpa [prefixWord, tailWord_2326620, baseEnd_2326620] using wordTrace_append hprefix tailTrace_2326620
  have hstable : (prefixWord ++ tailWord_2326620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326620).length < 2 ^ (prefixWord ++ tailWord_2326620).sum := by decide
  have hdescent : baseEnd_2326620 < baseStart_2326620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326682 : List Nat := [3, 1, 1, 5, 2, 1, 2, 1, 3, 3]
def baseStart_2326682 : Nat := 118140960795 + 2326682 * 2 ^ 59
def prefixEnd_2326682 : Nat := 4983230072969 + 3 ^ 40 * 2326682 * 2
def baseEnd_2326682 : Nat := 796470797442914053116527

theorem tailTrace_2326682 : CollatzResearch.WordTrace tailWord_2326682 prefixEnd_2326682 796470797442914053116527 := by
  unfold tailWord_2326682
  simp only [CollatzResearch.WordTrace]
  refine ⟨21215266039208988623703575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56574042771223969663209533 21215266039208988623703575)
  ·
    refine ⟨31822899058813482935555363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21215266039208988623703575 31822899058813482935555363)
    ·
      refine ⟨47734348588220224403333045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31822899058813482935555363 47734348588220224403333045)
      ·
        refine ⟨4475095180145646037812473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47734348588220224403333045 4475095180145646037812473)
        ·
          refine ⟨3356321385109234528359355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4475095180145646037812473 3356321385109234528359355)
          ·
            refine ⟨5034482077663851792539033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3356321385109234528359355 5034482077663851792539033)
            ·
              refine ⟨3775861558247888844404275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5034482077663851792539033 3775861558247888844404275)
              ·
                refine ⟨5663792337371833266606413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3775861558247888844404275 5663792337371833266606413)
                ·
                  refine ⟨2123922126514437474977405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5663792337371833266606413 2123922126514437474977405)
                  ·
                    refine ⟨796470797442914053116527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2123922126514437474977405 796470797442914053116527)
                    ·
                      rfl

theorem cell22_2326682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_2326682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326682 prefixEnd_2326682 := by exact prefixLift 2326682
  have htrace : WordTrace (prefixWord ++ tailWord_2326682) baseStart_2326682 baseEnd_2326682 := by
    simpa [prefixWord, tailWord_2326682, baseEnd_2326682] using wordTrace_append hprefix tailTrace_2326682
  have hstable : (prefixWord ++ tailWord_2326682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326682).length < 2 ^ (prefixWord ++ tailWord_2326682).sum := by decide
  have hdescent : baseEnd_2326682 < baseStart_2326682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326716 : List Nat := [2, 2, 2, 3, 4, 1, 1, 3, 1, 3]
def baseStart_2326716 : Nat := 118140960795 + 2326716 * 2 ^ 59
def prefixEnd_2326716 : Nat := 4983230072969 + 3 ^ 40 * 2326716 * 2
def baseEnd_2326716 : Nat := 796482436337749297766423

theorem tailTrace_2326716 : CollatzResearch.WordTrace tailWord_2326716 prefixEnd_2326716 796482436337749297766423 := by
  unfold tailWord_2326716
  simp only [CollatzResearch.WordTrace]
  refine ⟨42431152119356389150776001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56574869492475185534368001 42431152119356389150776001)
  ·
    refine ⟨31823364089517291863082001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42431152119356389150776001 31823364089517291863082001)
    ·
      refine ⟨23867523067137968897311501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31823364089517291863082001 23867523067137968897311501)
      ·
        refine ⟨8950321150176738336491813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23867523067137968897311501 8950321150176738336491813)
        ·
          refine ⟨1678185215658138438092215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8950321150176738336491813 1678185215658138438092215)
          ·
            refine ⟨2517277823487207657138323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1678185215658138438092215 2517277823487207657138323)
            ·
              refine ⟨3775916735230811485707485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2517277823487207657138323 3775916735230811485707485)
              ·
                refine ⟨1415968775711554307140307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3775916735230811485707485 1415968775711554307140307)
                ·
                  refine ⟨2123953163567331460710461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1415968775711554307140307 2123953163567331460710461)
                  ·
                    refine ⟨796482436337749297766423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2123953163567331460710461 796482436337749297766423)
                    ·
                      rfl

theorem cell22_2326716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_2326716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326716 prefixEnd_2326716 := by exact prefixLift 2326716
  have htrace : WordTrace (prefixWord ++ tailWord_2326716) baseStart_2326716 baseEnd_2326716 := by
    simpa [prefixWord, tailWord_2326716, baseEnd_2326716] using wordTrace_append hprefix tailTrace_2326716
  have hstable : (prefixWord ++ tailWord_2326716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326716).length < 2 ^ (prefixWord ++ tailWord_2326716).sum := by decide
  have hdescent : baseEnd_2326716 < baseStart_2326716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326736 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 2, 10]
def baseStart_2326736 : Nat := 118140960795 + 2326736 * 2 ^ 59
def prefixEnd_2326736 : Nat := 4983230072969 + 3 ^ 40 * 2326736 * 2
def baseEnd_2326736 : Nat := 796489282746475912266361

theorem tailTrace_2326736 : CollatzResearch.WordTrace tailWord_2326736 prefixEnd_2326736 796489282746475912266361 := by
  unfold tailWord_2326736
  simp only [CollatzResearch.WordTrace]
  refine ⟨42431516849320160858640031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56575355799093547811520041 42431516849320160858640031)
  ·
    refine ⟨63647275273980241287960047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42431516849320160858640031 63647275273980241287960047)
    ·
      refine ⟨95470912910970361931940071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63647275273980241287960047 95470912910970361931940071)
      ·
        refine ⟨143206369366455542897910107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95470912910970361931940071 143206369366455542897910107)
        ·
          refine ⟨214809554049683314346865161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143206369366455542897910107 214809554049683314346865161)
          ·
            refine ⟨161107165537262485760148871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214809554049683314346865161 161107165537262485760148871)
            ·
              refine ⟨241660748305893728640223307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161107165537262485760148871 241660748305893728640223307)
              ·
                refine ⟨362491122458840592960334961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241660748305893728640223307 362491122458840592960334961)
                ·
                  refine ⟨271868341844130444720251221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362491122458840592960334961 271868341844130444720251221)
                  ·
                    refine ⟨796489282746475912266361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 271868341844130444720251221 796489282746475912266361)
                    ·
                      rfl

theorem cell22_2326736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_2326736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326736 prefixEnd_2326736 := by exact prefixLift 2326736
  have htrace : WordTrace (prefixWord ++ tailWord_2326736) baseStart_2326736 baseEnd_2326736 := by
    simpa [prefixWord, tailWord_2326736, baseEnd_2326736] using wordTrace_append hprefix tailTrace_2326736
  have hstable : (prefixWord ++ tailWord_2326736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326736).length < 2 ^ (prefixWord ++ tailWord_2326736).sum := by decide
  have hdescent : baseEnd_2326736 < baseStart_2326736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326753 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 4, 4]
def baseStart_2326753 : Nat := 118140960795 + 2326753 * 2 ^ 59
def prefixEnd_2326753 : Nat := 4983230072969 + 3 ^ 40 * 2326753 * 2
def baseEnd_2326753 : Nat := 796495102193893534591309

theorem tailTrace_2326753 : CollatzResearch.WordTrace tailWord_2326753 prefixEnd_2326753 796495102193893534591309 := by
  unfold tailWord_2326753
  simp only [CollatzResearch.WordTrace]
  refine ⟨84863653739578733620648913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56575769159719155747099275 84863653739578733620648913)
  ·
    refine ⟨63647740304684050215486685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84863653739578733620648913 63647740304684050215486685)
    ·
      refine ⟨23867902614256518830807507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63647740304684050215486685 23867902614256518830807507)
      ·
        refine ⟨35801853921384778246211261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23867902614256518830807507 35801853921384778246211261)
        ·
          refine ⟨13425695220519291842329223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35801853921384778246211261 13425695220519291842329223)
          ·
            refine ⟨20138542830778937763493835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13425695220519291842329223 20138542830778937763493835)
            ·
              refine ⟨30207814246168406645240753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20138542830778937763493835 30207814246168406645240753)
              ·
                refine ⟨22655860684626304983930565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30207814246168406645240753 22655860684626304983930565)
                ·
                  refine ⟨4247973878367432184486981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22655860684626304983930565 4247973878367432184486981)
                  ·
                    refine ⟨796495102193893534591309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4247973878367432184486981 796495102193893534591309)
                    ·
                      rfl

theorem cell22_2326753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_2326753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326753 prefixEnd_2326753 := by exact prefixLift 2326753
  have htrace : WordTrace (prefixWord ++ tailWord_2326753) baseStart_2326753 baseEnd_2326753 := by
    simpa [prefixWord, tailWord_2326753, baseEnd_2326753] using wordTrace_append hprefix tailTrace_2326753
  have hstable : (prefixWord ++ tailWord_2326753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326753).length < 2 ^ (prefixWord ++ tailWord_2326753).sum := by decide
  have hdescent : baseEnd_2326753 < baseStart_2326753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326770 : List Nat := [3, 2, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_2326770 : Nat := 118140960795 + 2326770 * 2 ^ 59
def prefixEnd_2326770 : Nat := 4983230072969 + 3 ^ 40 * 2326770 * 2
def baseEnd_2326770 : Nat := 796500921641311156916257

theorem tailTrace_2326770 : CollatzResearch.WordTrace tailWord_2326770 prefixEnd_2326770 796500921641311156916257 := by
  unfold tailWord_2326770
  simp only [CollatzResearch.WordTrace]
  refine ⟨21216068445129286381004441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56576182520344763682678509 21216068445129286381004441)
  ·
    refine ⟨15912051333846964785753331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21216068445129286381004441 15912051333846964785753331)
    ·
      refine ⟨23868077000770447178629997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15912051333846964785753331 23868077000770447178629997)
      ·
        refine ⟨8950528875288917691986249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23868077000770447178629997 8950528875288917691986249)
        ·
          refine ⟨6712896656466688268989687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8950528875288917691986249 6712896656466688268989687)
          ·
            refine ⟨10069344984700032403484531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6712896656466688268989687 10069344984700032403484531)
            ·
              refine ⟨15104017477050048605226797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10069344984700032403484531 15104017477050048605226797)
              ·
                refine ⟨5664006553893768226960049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15104017477050048605226797 5664006553893768226960049)
                ·
                  refine ⟨4248004915420326170220037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5664006553893768226960049 4248004915420326170220037)
                  ·
                    refine ⟨796500921641311156916257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4248004915420326170220037 796500921641311156916257)
                    ·
                      rfl

theorem cell22_2326770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_2326770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326770 prefixEnd_2326770 := by exact prefixLift 2326770
  have htrace : WordTrace (prefixWord ++ tailWord_2326770) baseStart_2326770 baseEnd_2326770 := by
    simpa [prefixWord, tailWord_2326770, baseEnd_2326770] using wordTrace_append hprefix tailTrace_2326770
  have hstable : (prefixWord ++ tailWord_2326770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326770).length < 2 ^ (prefixWord ++ tailWord_2326770).sum := by decide
  have hdescent : baseEnd_2326770 < baseStart_2326770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326791 : List Nat := [1, 1, 4, 5, 1, 2, 2, 2, 4]
def baseStart_2326791 : Nat := 118140960795 + 2326791 * 2 ^ 59
def prefixEnd_2326791 : Nat := 4983230072969 + 3 ^ 40 * 2326791 * 2
def baseEnd_2326791 : Nat := 265502703456824700713731

theorem tailTrace_2326791 : CollatzResearch.WordTrace tailWord_2326791 prefixEnd_2326791 265502703456824700713731 := by
  unfold tailWord_2326791
  simp only [CollatzResearch.WordTrace]
  refine ⟨84865039713441066110532227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56576693142294044073688151 84865039713441066110532227)
  ·
    refine ⟨127297559570161599165798341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84865039713441066110532227 127297559570161599165798341)
    ·
      refine ⟨23868292419405299843587189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127297559570161599165798341 23868292419405299843587189)
      ·
        refine ⟨2237652414319246860336299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23868292419405299843587189 2237652414319246860336299)
        ·
          refine ⟨3356478621478870290504449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2237652414319246860336299 3356478621478870290504449)
          ·
            refine ⟨2517358966109152717878337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3356478621478870290504449 2517358966109152717878337)
            ·
              refine ⟨1888019224581864538408753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2517358966109152717878337 1888019224581864538408753)
              ·
                refine ⟨1416014418436398403806565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1888019224581864538408753 1416014418436398403806565)
                ·
                  refine ⟨265502703456824700713731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1416014418436398403806565 265502703456824700713731)
                  ·
                    rfl

theorem cell22_2326791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 4].length) (baseStart_2326791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326791 prefixEnd_2326791 := by exact prefixLift 2326791
  have htrace : WordTrace (prefixWord ++ tailWord_2326791) baseStart_2326791 baseEnd_2326791 := by
    simpa [prefixWord, tailWord_2326791, baseEnd_2326791] using wordTrace_append hprefix tailTrace_2326791
  have hstable : (prefixWord ++ tailWord_2326791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326791).length < 2 ^ (prefixWord ++ tailWord_2326791).sum := by decide
  have hdescent : baseEnd_2326791 < baseStart_2326791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326798 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_2326798 : Nat := 118140960795 + 2326798 * 2 ^ 59
def prefixEnd_2326798 : Nat := 4983230072969 + 3 ^ 40 * 2326798 * 2
def baseEnd_2326798 : Nat := 796510506613528417216171

theorem tailTrace_2326798 : CollatzResearch.WordTrace tailWord_2326798 prefixEnd_2326798 796510506613528417216171 := by
  unfold tailWord_2326798
  simp only [CollatzResearch.WordTrace]
  refine ⟨10608161878051963288254631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56576863349610470870691365 10608161878051963288254631)
  ·
    refine ⟨15912242817077944932381947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10608161878051963288254631 15912242817077944932381947)
    ·
      refine ⟨23868364225616917398572921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15912242817077944932381947 23868364225616917398572921)
      ·
        refine ⟨17901273169212688048929691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23868364225616917398572921 17901273169212688048929691)
        ·
          refine ⟨26851909753819032073394537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17901273169212688048929691 26851909753819032073394537)
          ·
            refine ⟨20138932315364274055045903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26851909753819032073394537 20138932315364274055045903)
            ·
              refine ⟨30208398473046411082568855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20138932315364274055045903 30208398473046411082568855)
              ·
                refine ⟨45312597709569616623853283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30208398473046411082568855 45312597709569616623853283)
                ·
                  refine ⟨67968896564354424935779925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45312597709569616623853283 67968896564354424935779925)
                  ·
                    refine ⟨796510506613528417216171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67968896564354424935779925 796510506613528417216171)
                    ·
                      rfl

theorem cell22_2326798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_2326798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326798 prefixEnd_2326798 := by exact prefixLift 2326798
  have htrace : WordTrace (prefixWord ++ tailWord_2326798) baseStart_2326798 baseEnd_2326798 := by
    simpa [prefixWord, tailWord_2326798, baseEnd_2326798] using wordTrace_append hprefix tailTrace_2326798
  have hstable : (prefixWord ++ tailWord_2326798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326798).length < 2 ^ (prefixWord ++ tailWord_2326798).sum := by decide
  have hdescent : baseEnd_2326798 < baseStart_2326798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326909 : List Nat := [1, 4, 1, 1, 2, 4, 3, 2, 4]
def baseStart_2326909 : Nat := 118140960795 + 2326909 * 2 ^ 59
def prefixEnd_2326909 : Nat := 4983230072969 + 3 ^ 40 * 2326909 * 2
def baseEnd_2326909 : Nat := 265516168060653709230277

theorem tailTrace_2326909 : CollatzResearch.WordTrace tailWord_2326909 prefixEnd_2326909 265516168060653709230277 := by
  unfold tailWord_2326909
  simp only [CollatzResearch.WordTrace]
  refine ⟨84869343527013572263327781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56579562351342381508885187 84869343527013572263327781)
  ·
    refine ⟨15913001911315044799373959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84869343527013572263327781 15913001911315044799373959)
    ·
      refine ⟨23869502866972567199060939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15913001911315044799373959 23869502866972567199060939)
      ·
        refine ⟨35804254300458850798591409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23869502866972567199060939 35804254300458850798591409)
        ·
          refine ⟨26853190725344138098943557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35804254300458850798591409 26853190725344138098943557)
          ·
            refine ⟨5034973261002025893551917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26853190725344138098943557 5034973261002025893551917)
            ·
              refine ⟨1888114972875759710081969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5034973261002025893551917 1888114972875759710081969)
              ·
                refine ⟨1416086229656819782561477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1888114972875759710081969 1416086229656819782561477)
                ·
                  refine ⟨265516168060653709230277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1416086229656819782561477 265516168060653709230277)
                  ·
                    rfl

theorem cell22_2326909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_2326909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326909 prefixEnd_2326909 := by exact prefixLift 2326909
  have htrace : WordTrace (prefixWord ++ tailWord_2326909) baseStart_2326909 baseEnd_2326909 := by
    simpa [prefixWord, tailWord_2326909, baseEnd_2326909] using wordTrace_append hprefix tailTrace_2326909
  have hstable : (prefixWord ++ tailWord_2326909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326909).length < 2 ^ (prefixWord ++ tailWord_2326909).sum := by decide
  have hdescent : baseEnd_2326909 < baseStart_2326909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326920 : List Nat := [2, 1, 3, 3, 1, 1, 4, 7]
def baseStart_2326920 : Nat := 118140960795 + 2326920 * 2 ^ 59
def prefixEnd_2326920 : Nat := 4983230072969 + 3 ^ 40 * 2326920 * 2
def baseEnd_2326920 : Nat := 88505807745195640629533

theorem tailTrace_2326920 : CollatzResearch.WordTrace tailWord_2326920 prefixEnd_2326920 88505807745195640629533 := by
  unfold tailWord_2326920
  simp only [CollatzResearch.WordTrace]
  refine ⟨42434872364986860570989107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56579829819982480761318809 42434872364986860570989107)
  ·
    refine ⟨63652308547480290856483661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42434872364986860570989107 63652308547480290856483661)
    ·
      refine ⟨23869615705305109071181373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63652308547480290856483661 23869615705305109071181373)
      ·
        refine ⟨8951105889489415901693015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23869615705305109071181373 8951105889489415901693015)
        ·
          refine ⟨13426658834234123852539523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8951105889489415901693015 13426658834234123852539523)
          ·
            refine ⟨20139988251351185778809285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13426658834234123852539523 20139988251351185778809285)
            ·
              refine ⟨3776247797128347333526741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20139988251351185778809285 3776247797128347333526741)
              ·
                refine ⟨88505807745195640629533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3776247797128347333526741 88505807745195640629533)
                ·
                  rfl

theorem cell22_2326920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 7].length) (baseStart_2326920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326920 prefixEnd_2326920 := by exact prefixLift 2326920
  have htrace : WordTrace (prefixWord ++ tailWord_2326920) baseStart_2326920 baseEnd_2326920 := by
    simpa [prefixWord, tailWord_2326920, baseEnd_2326920] using wordTrace_append hprefix tailTrace_2326920
  have hstable : (prefixWord ++ tailWord_2326920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326920).length < 2 ^ (prefixWord ++ tailWord_2326920).sum := by decide
  have hdescent : baseEnd_2326920 < baseStart_2326920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326924 : List Nat := [2, 2, 1, 2, 1, 4, 4, 1, 2, 3]
def baseStart_2326924 : Nat := 118140960795 + 2326924 * 2 ^ 59
def prefixEnd_2326924 : Nat := 4983230072969 + 3 ^ 40 * 2326924 * 2
def baseEnd_2326924 : Nat := 796553638988506088565785

theorem tailTrace_2326924 : CollatzResearch.WordTrace tailWord_2326924 prefixEnd_2326924 796553638988506088565785 := by
  unfold tailWord_2326924
  simp only [CollatzResearch.WordTrace]
  refine ⟨42434945310979614912561913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56579927081306153216749217 42434945310979614912561913)
  ·
    refine ⟨31826208983234711184421435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42434945310979614912561913 31826208983234711184421435)
    ·
      refine ⟨47739313474852066776632153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31826208983234711184421435 47739313474852066776632153)
      ·
        refine ⟨35804485106139050082474115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47739313474852066776632153 35804485106139050082474115)
        ·
          refine ⟨53706727659208575123711173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35804485106139050082474115 53706727659208575123711173)
          ·
            refine ⟨10070011436101607835695845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53706727659208575123711173 10070011436101607835695845)
            ·
              refine ⟨1888127144269051469192971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10070011436101607835695845 1888127144269051469192971)
              ·
                refine ⟨2832190716403577203789457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1888127144269051469192971 2832190716403577203789457)
                ·
                  refine ⟨2124143037302682902842093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2832190716403577203789457 2124143037302682902842093)
                  ·
                    refine ⟨796553638988506088565785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2124143037302682902842093 796553638988506088565785)
                    ·
                      rfl

theorem cell22_2326924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 2, 3].length) (baseStart_2326924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326924 prefixEnd_2326924 := by exact prefixLift 2326924
  have htrace : WordTrace (prefixWord ++ tailWord_2326924) baseStart_2326924 baseEnd_2326924 := by
    simpa [prefixWord, tailWord_2326924, baseEnd_2326924] using wordTrace_append hprefix tailTrace_2326924
  have hstable : (prefixWord ++ tailWord_2326924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326924).length < 2 ^ (prefixWord ++ tailWord_2326924).sum := by decide
  have hdescent : baseEnd_2326924 < baseStart_2326924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326954 : List Nat := [3, 1, 6, 1, 1, 10]
def baseStart_2326954 : Nat := 118140960795 + 2326954 * 2 ^ 59
def prefixEnd_2326954 : Nat := 4983230072969 + 3 ^ 40 * 2326954 * 2
def baseEnd_2326954 : Nat := 9834122328414765559453

theorem tailTrace_2326954 : CollatzResearch.WordTrace tailWord_2326954 prefixEnd_2326954 9834122328414765559453 := by
  unfold tailWord_2326954
  simp only [CollatzResearch.WordTrace]
  refine ⟨21217746202962636237178979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56580656541233696632477277 21217746202962636237178979)
  ·
    refine ⟨31826619304443954355768469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21217746202962636237178979 31826619304443954355768469)
    ·
      refine ⟨1491872779895810360426647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31826619304443954355768469 1491872779895810360426647)
      ·
        refine ⟨2237809169843715540639971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1491872779895810360426647 2237809169843715540639971)
        ·
          refine ⟨3356713754765573310959957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2237809169843715540639971 3356713754765573310959957)
          ·
            refine ⟨9834122328414765559453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3356713754765573310959957 9834122328414765559453)
            ·
              rfl

theorem cell22_2326954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 10].length) (baseStart_2326954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2326954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2326954 prefixEnd_2326954 := by exact prefixLift 2326954
  have htrace : WordTrace (prefixWord ++ tailWord_2326954) baseStart_2326954 baseEnd_2326954 := by
    simpa [prefixWord, tailWord_2326954, baseEnd_2326954] using wordTrace_append hprefix tailTrace_2326954
  have hstable : (prefixWord ++ tailWord_2326954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326954).length < 2 ^ (prefixWord ++ tailWord_2326954).sum := by decide
  have hdescent : baseEnd_2326954 < baseStart_2326954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327027 : List Nat := [1, 1, 1, 2, 2, 2, 3, 6, 4]
def baseStart_2327027 : Nat := 118140960795 + 2327027 * 2 ^ 59
def prefixEnd_2327027 : Nat := 4983230072969 + 3 ^ 40 * 2327027 * 2
def baseEnd_2327027 : Nat := 265529632664482717746823

theorem tailTrace_2327027 : CollatzResearch.WordTrace tailWord_2327027 prefixEnd_2327027 265529632664482717746823 := by
  unfold tailWord_2327027
  simp only [CollatzResearch.WordTrace]
  refine ⟨84873647340586078416123335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56582431560390718944082223 84873647340586078416123335)
  ·
    refine ⟨127310471010879117624185003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84873647340586078416123335 127310471010879117624185003)
    ·
      refine ⟨190965706516318676436277505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127310471010879117624185003 190965706516318676436277505)
      ·
        refine ⟨143224279887239007327208129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190965706516318676436277505 143224279887239007327208129)
        ·
          refine ⟨107418209915429255495406097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143224279887239007327208129 107418209915429255495406097)
          ·
            refine ⟨80563657436571941621554573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107418209915429255495406097 80563657436571941621554573)
            ·
              refine ⟨30211371538714478108082965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80563657436571941621554573 30211371538714478108082965)
              ·
                refine ⟨1416158040877241161316389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30211371538714478108082965 1416158040877241161316389)
                ·
                  refine ⟨265529632664482717746823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1416158040877241161316389 265529632664482717746823)
                  ·
                    rfl

theorem cell22_2327027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 4].length) (baseStart_2327027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2327027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2327027 prefixEnd_2327027 := by exact prefixLift 2327027
  have htrace : WordTrace (prefixWord ++ tailWord_2327027) baseStart_2327027 baseEnd_2327027 := by
    simpa [prefixWord, tailWord_2327027, baseEnd_2327027] using wordTrace_append hprefix tailTrace_2327027
  have hstable : (prefixWord ++ tailWord_2327027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327027).length < 2 ^ (prefixWord ++ tailWord_2327027).sum := by decide
  have hdescent : baseEnd_2327027 < baseStart_2327027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327149 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_2327149 : Nat := 118140960795 + 2327149 * 2 ^ 59
def prefixEnd_2327149 : Nat := 4983230072969 + 3 ^ 40 * 2327149 * 2
def baseEnd_2327149 : Nat := 796630661086680501690095

theorem tailTrace_2327149 : CollatzResearch.WordTrace tailWord_2327149 prefixEnd_2327149 796630661086680501690095 := by
  unfold tailWord_2327149
  simp only [CollatzResearch.WordTrace]
  refine ⟨84878097046144093252064501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56585398030762728834709667 84878097046144093252064501)
  ·
    refine ⟨7957321598076008742381047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84878097046144093252064501 7957321598076008742381047)
    ·
      refine ⟨11935982397114013113571571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7957321598076008742381047 11935982397114013113571571)
      ·
        refine ⟨17903973595671019670357357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11935982397114013113571571 17903973595671019670357357)
        ·
          refine ⟨6713990098376632376384009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17903973595671019670357357 6713990098376632376384009)
          ·
            refine ⟨5035492573782474282288007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6713990098376632376384009 5035492573782474282288007)
            ·
              refine ⟨7553238860673711423432011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5035492573782474282288007 7553238860673711423432011)
              ·
                refine ⟨11329858291010567135148017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7553238860673711423432011 11329858291010567135148017)
                ·
                  refine ⟨8497393718257925351361013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11329858291010567135148017 8497393718257925351361013)
                  ·
                    refine ⟨796630661086680501690095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8497393718257925351361013 796630661086680501690095)
                    ·
                      rfl

theorem cell22_2327149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_2327149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2327149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2327149 prefixEnd_2327149 := by exact prefixLift 2327149
  have htrace : WordTrace (prefixWord ++ tailWord_2327149) baseStart_2327149 baseEnd_2327149 := by
    simpa [prefixWord, tailWord_2327149, baseEnd_2327149] using wordTrace_append hprefix tailTrace_2327149
  have hstable : (prefixWord ++ tailWord_2327149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327149).length < 2 ^ (prefixWord ++ tailWord_2327149).sum := by decide
  have hdescent : baseEnd_2327149 < baseStart_2327149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327196 : List Nat := [2, 2, 3, 2, 2, 1, 2, 4, 4]
def baseStart_2327196 : Nat := 118140960795 + 2327196 * 2 ^ 59
def prefixEnd_2327196 : Nat := 4983230072969 + 3 ^ 40 * 2327196 * 2
def baseEnd_2327196 : Nat := 265548916715729348588317

theorem tailTrace_2327196 : CollatzResearch.WordTrace tailWord_2327196 prefixEnd_2327196 265548916715729348588317 := by
  unfold tailWord_2327196
  simp only [CollatzResearch.WordTrace]
  refine ⟨42439905638486910139512721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56586540851315880186016961 42439905638486910139512721)
  ·
    refine ⟨31829929228865182604634541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42439905638486910139512721 31829929228865182604634541)
    ·
      refine ⟨11936223460824443476737953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31829929228865182604634541 11936223460824443476737953)
      ·
        refine ⟨8952167595618332607553465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11936223460824443476737953 8952167595618332607553465)
        ·
          refine ⟨6714125696713749455665099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8952167595618332607553465 6714125696713749455665099)
          ·
            refine ⟨10071188545070624183497649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6714125696713749455665099 10071188545070624183497649)
            ·
              refine ⟨7553391408802968137623237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10071188545070624183497649 7553391408802968137623237)
              ·
                refine ⟨1416260889150556525804357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7553391408802968137623237 1416260889150556525804357)
                ·
                  refine ⟨265548916715729348588317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1416260889150556525804357 265548916715729348588317)
                  ·
                    rfl

theorem cell22_2327196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 4].length) (baseStart_2327196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2327196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2327196 prefixEnd_2327196 := by exact prefixLift 2327196
  have htrace : WordTrace (prefixWord ++ tailWord_2327196) baseStart_2327196 baseEnd_2327196 := by
    simpa [prefixWord, tailWord_2327196, baseEnd_2327196] using wordTrace_append hprefix tailTrace_2327196
  have hstable : (prefixWord ++ tailWord_2327196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327196).length < 2 ^ (prefixWord ++ tailWord_2327196).sum := by decide
  have hdescent : baseEnd_2327196 < baseStart_2327196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327256 : List Nat := [2, 1, 2, 2, 3, 2, 3, 1, 3, 3]
def baseStart_2327256 : Nat := 118140960795 + 2327256 * 2 ^ 59
def prefixEnd_2327256 : Nat := 4983230072969 + 3 ^ 40 * 2327256 * 2
def baseEnd_2327256 : Nat := 796667289373367889264767

theorem tailTrace_2327256 : CollatzResearch.WordTrace tailWord_2327256 prefixEnd_2327256 796667289373367889264767 := by
  unfold tailWord_2327256
  simp only [CollatzResearch.WordTrace]
  refine ⟨42440999828378225263104811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56587999771170967017473081 42440999828378225263104811)
  ·
    refine ⟨63661499742567337894657217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42440999828378225263104811 63661499742567337894657217)
    ·
      refine ⟨47746124806925503420992913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63661499742567337894657217 47746124806925503420992913)
      ·
        refine ⟨35809593605194127565744685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47746124806925503420992913 35809593605194127565744685)
        ·
          refine ⟨13428597601947797837154257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35809593605194127565744685 13428597601947797837154257)
          ·
            refine ⟨10071448201460848377865693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13428597601947797837154257 10071448201460848377865693)
            ·
              refine ⟨3776793075547818141699635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10071448201460848377865693 3776793075547818141699635)
              ·
                refine ⟨5665189613321727212549453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3776793075547818141699635 5665189613321727212549453)
                ·
                  refine ⟨2124446104995647704706045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5665189613321727212549453 2124446104995647704706045)
                  ·
                    refine ⟨796667289373367889264767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2124446104995647704706045 796667289373367889264767)
                    ·
                      rfl

theorem cell22_2327256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_2327256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2327256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2327256 prefixEnd_2327256 := by exact prefixLift 2327256
  have htrace : WordTrace (prefixWord ++ tailWord_2327256) baseStart_2327256 baseEnd_2327256 := by
    simpa [prefixWord, tailWord_2327256, baseEnd_2327256] using wordTrace_append hprefix tailTrace_2327256
  have hstable : (prefixWord ++ tailWord_2327256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327256).length < 2 ^ (prefixWord ++ tailWord_2327256).sum := by decide
  have hdescent : baseEnd_2327256 < baseStart_2327256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327346 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 4, 3]
def baseStart_2327346 : Nat := 118140960795 + 2327346 * 2 ^ 59
def prefixEnd_2327346 : Nat := 4983230072969 + 3 ^ 40 * 2327346 * 2
def baseEnd_2327346 : Nat := 796698098212637654514491

theorem tailTrace_2327346 : CollatzResearch.WordTrace tailWord_2327346 prefixEnd_2327346 796698098212637654514491 := by
  unfold tailWord_2327346
  simp only [CollatzResearch.WordTrace]
  refine ⟨21221320556607598974246473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56590188150953597264657261 21221320556607598974246473)
  ·
    refine ⟨15915990417455699230684855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21221320556607598974246473 15915990417455699230684855)
    ·
      refine ⟨23873985626183548846027283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15915990417455699230684855 23873985626183548846027283)
      ·
        refine ⟨35810978439275323269040925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23873985626183548846027283 35810978439275323269040925)
        ·
          refine ⟨13429116914728246225890347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35810978439275323269040925 13429116914728246225890347)
          ·
            refine ⟨20143675372092369338835521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13429116914728246225890347 20143675372092369338835521)
            ·
              refine ⟨15107756529069277004126641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20143675372092369338835521 15107756529069277004126641)
              ·
                refine ⟨11330817396801957753094981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15107756529069277004126641 11330817396801957753094981)
                ·
                  refine ⟨2124528261900367078705309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11330817396801957753094981 2124528261900367078705309)
                  ·
                    refine ⟨796698098212637654514491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2124528261900367078705309 796698098212637654514491)
                    ·
                      rfl

theorem cell22_2327346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_2327346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2327346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2327346 prefixEnd_2327346 := by exact prefixLift 2327346
  have htrace : WordTrace (prefixWord ++ tailWord_2327346) baseStart_2327346 baseEnd_2327346 := by
    simpa [prefixWord, tailWord_2327346, baseEnd_2327346] using wordTrace_append hprefix tailTrace_2327346
  have hstable : (prefixWord ++ tailWord_2327346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327346).length < 2 ^ (prefixWord ++ tailWord_2327346).sum := by decide
  have hdescent : baseEnd_2327346 < baseStart_2327346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327350 : List Nat := [5, 1, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_2327350 : Nat := 118140960795 + 2327350 * 2 ^ 59
def prefixEnd_2327350 : Nat := 4983230072969 + 3 ^ 40 * 2327350 * 2
def baseEnd_2327350 : Nat := 796699467494382977414479

theorem tailTrace_2327350 : CollatzResearch.WordTrace tailWord_2327350 prefixEnd_2327350 796699467494382977414479 := by
  unfold tailWord_2327350
  simp only [CollatzResearch.WordTrace]
  refine ⟨5305339257400994036258219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56590285412277269720087669 5305339257400994036258219)
  ·
    refine ⟨7958008886101491054387329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5305339257400994036258219 7958008886101491054387329)
    ·
      refine ⟨5968506664576118290790497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7958008886101491054387329 5968506664576118290790497)
      ·
        refine ⟨4476379998432088718092873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5968506664576118290790497 4476379998432088718092873)
        ·
          refine ⟨3357284998824066538569655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4476379998432088718092873 3357284998824066538569655)
          ·
            refine ⟨5035927498236099807854483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3357284998824066538569655 5035927498236099807854483)
            ·
              refine ⟨7553891247354149711781725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5035927498236099807854483 7553891247354149711781725)
              ·
                refine ⟨2832709217757806141918147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7553891247354149711781725 2832709217757806141918147)
                ·
                  refine ⟨4249063826636709212877221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2832709217757806141918147 4249063826636709212877221)
                  ·
                    refine ⟨796699467494382977414479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4249063826636709212877221 796699467494382977414479)
                    ·
                      rfl

theorem cell22_2327350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_2327350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2327350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2327350 prefixEnd_2327350 := by exact prefixLift 2327350
  have htrace : WordTrace (prefixWord ++ tailWord_2327350) baseStart_2327350 baseEnd_2327350 := by
    simpa [prefixWord, tailWord_2327350, baseEnd_2327350] using wordTrace_append hprefix tailTrace_2327350
  have hstable : (prefixWord ++ tailWord_2327350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327350).length < 2 ^ (prefixWord ++ tailWord_2327350).sum := by decide
  have hdescent : baseEnd_2327350 < baseStart_2327350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327359 : List Nat := [1, 1, 2, 2, 5, 2, 9]
def baseStart_2327359 : Nat := 118140960795 + 2327359 * 2 ^ 59
def prefixEnd_2327359 : Nat := 4983230072969 + 3 ^ 40 * 2327359 * 2
def baseEnd_2327359 : Nat := 29507501791789257553313

theorem tailTrace_2327359 : CollatzResearch.WordTrace tailWord_2327359 prefixEnd_2327359 29507501791789257553313 := by
  unfold tailWord_2327359
  simp only [CollatzResearch.WordTrace]
  refine ⟨84885756375383299117209131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56590504250255532744806087 84885756375383299117209131)
  ·
    refine ⟨127328634563074948675813697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84885756375383299117209131 127328634563074948675813697)
    ·
      refine ⟨95496475922306211506860273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127328634563074948675813697 95496475922306211506860273)
      ·
        refine ⟨71622356941729658630145205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95496475922306211506860273 71622356941729658630145205)
        ·
          refine ⟨6714595963287155496576113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71622356941729658630145205 6714595963287155496576113)
          ·
            refine ⟨5035946972465366622432085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6714595963287155496576113 5035946972465366622432085)
            ·
              refine ⟨29507501791789257553313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5035946972465366622432085 29507501791789257553313)
              ·
                rfl

theorem cell22_2327359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 9].length) (baseStart_2327359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2327359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2327359 prefixEnd_2327359 := by exact prefixLift 2327359
  have htrace : WordTrace (prefixWord ++ tailWord_2327359) baseStart_2327359 baseEnd_2327359 := by
    simpa [prefixWord, tailWord_2327359, baseEnd_2327359] using wordTrace_append hprefix tailTrace_2327359
  have hstable : (prefixWord ++ tailWord_2327359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327359).length < 2 ^ (prefixWord ++ tailWord_2327359).sum := by decide
  have hdescent : baseEnd_2327359 < baseStart_2327359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327380 : List Nat := [2, 4, 1, 1, 5, 1, 1, 1, 1, 5]
def baseStart_2327380 : Nat := 118140960795 + 2327380 * 2 ^ 59
def prefixEnd_2327380 : Nat := 4983230072969 + 3 ^ 40 * 2327380 * 2
def baseEnd_2327380 : Nat := 796709737107472899164387

theorem tailTrace_2327380 : CollatzResearch.WordTrace tailWord_2327380 prefixEnd_2327380 796709737107472899164387 := by
  unfold tailWord_2327380
  simp only [CollatzResearch.WordTrace]
  refine ⟨42443261154153609851861797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56591014872204813135815729 42443261154153609851861797)
  ·
    refine ⟨7958111466403801847224087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42443261154153609851861797 7958111466403801847224087)
    ·
      refine ⟨11937167199605702770836131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7958111466403801847224087 11937167199605702770836131)
      ·
        refine ⟨17905750799408554156254197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11937167199605702770836131 17905750799408554156254197)
        ·
          refine ⟨1678664137444551952148831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17905750799408554156254197 1678664137444551952148831)
          ·
            refine ⟨2517996206166827928223247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1678664137444551952148831 2517996206166827928223247)
            ·
              refine ⟨3776994309250241892334871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2517996206166827928223247 3776994309250241892334871)
              ·
                refine ⟨5665491463875362838502307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3776994309250241892334871 5665491463875362838502307)
                ·
                  refine ⟨8498237195813044257753461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5665491463875362838502307 8498237195813044257753461)
                  ·
                    refine ⟨796709737107472899164387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8498237195813044257753461 796709737107472899164387)
                    ·
                      rfl

theorem cell22_2327380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_2327380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2327380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2327380 prefixEnd_2327380 := by exact prefixLift 2327380
  have htrace : WordTrace (prefixWord ++ tailWord_2327380) baseStart_2327380 baseEnd_2327380 := by
    simpa [prefixWord, tailWord_2327380, baseEnd_2327380] using wordTrace_append hprefix tailTrace_2327380
  have hstable : (prefixWord ++ tailWord_2327380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327380).length < 2 ^ (prefixWord ++ tailWord_2327380).sum := by decide
  have hdescent : baseEnd_2327380 < baseStart_2327380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327391 : List Nat := [1, 1, 2, 3, 1, 3, 1, 4, 3, 3]
def baseStart_2327391 : Nat := 118140960795 + 2327391 * 2 ^ 59
def prefixEnd_2327391 : Nat := 4983230072969 + 3 ^ 40 * 2327391 * 2
def baseEnd_2327391 : Nat := 796713502632272537139353

theorem tailTrace_2327391 : CollatzResearch.WordTrace tailWord_2327391 prefixEnd_2327391 796713502632272537139353 := by
  unfold tailWord_2327391
  simp only [CollatzResearch.WordTrace]
  refine ⟨84886923511267368582374027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56591282340844912388249351 84886923511267368582374027)
  ·
    refine ⟨127330385266901052873561041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84886923511267368582374027 127330385266901052873561041)
    ·
      refine ⟨95497788950175789655170781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127330385266901052873561041 95497788950175789655170781)
      ·
        refine ⟨35811670856315921120689043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95497788950175789655170781 35811670856315921120689043)
        ·
          refine ⟨53717506284473881681033565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35811670856315921120689043 53717506284473881681033565)
          ·
            refine ⟨20144064856677705630387587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53717506284473881681033565 20144064856677705630387587)
            ·
              refine ⟨30216097285016558445581381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20144064856677705630387587 30216097285016558445581381)
              ·
                refine ⟨5665518240940604708546509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30216097285016558445581381 5665518240940604708546509)
                ·
                  refine ⟨2124569340352726765704941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5665518240940604708546509 2124569340352726765704941)
                  ·
                    refine ⟨796713502632272537139353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2124569340352726765704941 796713502632272537139353)
                    ·
                      rfl

theorem cell22_2327391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 3].length) (baseStart_2327391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2327391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2327391 prefixEnd_2327391 := by exact prefixLift 2327391
  have htrace : WordTrace (prefixWord ++ tailWord_2327391) baseStart_2327391 baseEnd_2327391 := by
    simpa [prefixWord, tailWord_2327391, baseEnd_2327391] using wordTrace_append hprefix tailTrace_2327391
  have hstable : (prefixWord ++ tailWord_2327391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327391).length < 2 ^ (prefixWord ++ tailWord_2327391).sum := by decide
  have hdescent : baseEnd_2327391 < baseStart_2327391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327404 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 9]
def baseStart_2327404 : Nat := 118140960795 + 2327404 * 2 ^ 59
def prefixEnd_2327404 : Nat := 4983230072969 + 3 ^ 40 * 2327404 * 2
def baseEnd_2327404 : Nat := 265572650932648278854771

theorem tailTrace_2327404 : CollatzResearch.WordTrace tailWord_2327404 prefixEnd_2327404 265572650932648278854771 := by
  unfold tailWord_2327404
  simp only [CollatzResearch.WordTrace]
  refine ⟨42443698830110135901298633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56591598440146847868398177 42443698830110135901298633)
  ·
    refine ⟨31832774122582601925973975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42443698830110135901298633 31832774122582601925973975)
    ·
      refine ⟨47749161183873902888960963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31832774122582601925973975 47749161183873902888960963)
      ·
        refine ⟨71623741775810854333441445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47749161183873902888960963 71623741775810854333441445)
        ·
          refine ⟨13429451582964535187520271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71623741775810854333441445 13429451582964535187520271)
          ·
            refine ⟨20144177374446802781280407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13429451582964535187520271 20144177374446802781280407)
            ·
              refine ⟨30216266061670204171920611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20144177374446802781280407 30216266061670204171920611)
              ·
                refine ⟨45324399092505306257880917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30216266061670204171920611 45324399092505306257880917)
                ·
                  refine ⟨265572650932648278854771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45324399092505306257880917 265572650932648278854771)
                  ·
                    rfl

theorem cell22_2327404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_2327404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2327404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2327404 prefixEnd_2327404 := by exact prefixLift 2327404
  have htrace : WordTrace (prefixWord ++ tailWord_2327404) baseStart_2327404 baseEnd_2327404 := by
    simpa [prefixWord, tailWord_2327404, baseEnd_2327404] using wordTrace_append hprefix tailTrace_2327404
  have hstable : (prefixWord ++ tailWord_2327404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327404).length < 2 ^ (prefixWord ++ tailWord_2327404).sum := by decide
  have hdescent : baseEnd_2327404 < baseStart_2327404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327419 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 4, 5]
def baseStart_2327419 : Nat := 118140960795 + 2327419 * 2 ^ 59
def prefixEnd_2327419 : Nat := 4983230072969 + 3 ^ 40 * 2327419 * 2
def baseEnd_2327419 : Nat := 796723087604489797439267

theorem tailTrace_2327419 : CollatzResearch.WordTrace tailWord_2327419 prefixEnd_2327419 796723087604489797439267 := by
  unfold tailWord_2327419
  simp only [CollatzResearch.WordTrace]
  refine ⟨84887944755165929364393311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56591963170110619576262207 84887944755165929364393311)
  ·
    refine ⟨127331917132748894046589967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84887944755165929364393311 127331917132748894046589967)
    ·
      refine ⟨190997875699123341069884951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127331917132748894046589967 190997875699123341069884951)
      ·
        refine ⟨286496813548685011604827427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190997875699123341069884951 286496813548685011604827427)
        ·
          refine ⟨429745220323027517407241141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286496813548685011604827427 429745220323027517407241141)
          ·
            refine ⟨40288614405283829756928857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 429745220323027517407241141 40288614405283829756928857)
            ·
              refine ⟨30216460803962872317696643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40288614405283829756928857 30216460803962872317696643)
              ·
                refine ⟨45324691205944308476544965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30216460803962872317696643 45324691205944308476544965)
                ·
                  refine ⟨8498379601114557839352181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45324691205944308476544965 8498379601114557839352181)
                  ·
                    refine ⟨796723087604489797439267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8498379601114557839352181 796723087604489797439267)
                    ·
                      rfl

theorem cell22_2327419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 5].length) (baseStart_2327419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2327419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2327419 prefixEnd_2327419 := by exact prefixLift 2327419
  have htrace : WordTrace (prefixWord ++ tailWord_2327419) baseStart_2327419 baseEnd_2327419 := by
    simpa [prefixWord, tailWord_2327419, baseEnd_2327419] using wordTrace_append hprefix tailTrace_2327419
  have hstable : (prefixWord ++ tailWord_2327419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327419).length < 2 ^ (prefixWord ++ tailWord_2327419).sum := by decide
  have hdescent : baseEnd_2327419 < baseStart_2327419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327449 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 8]
def baseStart_2327449 : Nat := 118140960795 + 2327449 * 2 ^ 59
def prefixEnd_2327449 : Nat := 4983230072969 + 3 ^ 40 * 2327449 * 2
def baseEnd_2327449 : Nat := 265577785739193239729725

theorem tailTrace_2327449 : CollatzResearch.WordTrace tailWord_2327449 prefixEnd_2327449 265577785739193239729725 := by
  unfold tailWord_2327449
  simp only [CollatzResearch.WordTrace]
  refine ⟨84889038945057244487985401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56592692630038162991990267 84889038945057244487985401)
  ·
    refine ⟨63666779208792933365989051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84889038945057244487985401 63666779208792933365989051)
    ·
      refine ⟨95500168813189400048983577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63666779208792933365989051 95500168813189400048983577)
      ·
        refine ⟨71625126609892050036737683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95500168813189400048983577 71625126609892050036737683)
        ·
          refine ⟨107437689914838075055106525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71625126609892050036737683 107437689914838075055106525)
          ·
            refine ⟨40289133718064278145664947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107437689914838075055106525 40289133718064278145664947)
            ·
              refine ⟨60433700577096417218497421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40289133718064278145664947 60433700577096417218497421)
              ·
                refine ⟨22662637716411156456936533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60433700577096417218497421 22662637716411156456936533)
                ·
                  refine ⟨265577785739193239729725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22662637716411156456936533 265577785739193239729725)
                  ·
                    rfl

theorem cell22_2327449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 8].length) (baseStart_2327449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2327449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2327449 prefixEnd_2327449 := by exact prefixLift 2327449
  have htrace : WordTrace (prefixWord ++ tailWord_2327449) baseStart_2327449 baseEnd_2327449 := by
    simpa [prefixWord, tailWord_2327449, baseEnd_2327449] using wordTrace_append hprefix tailTrace_2327449
  have hstable : (prefixWord ++ tailWord_2327449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327449).length < 2 ^ (prefixWord ++ tailWord_2327449).sum := by decide
  have hdescent : baseEnd_2327449 < baseStart_2327449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327476 : List Nat := [2, 5, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_2327476 : Nat := 118140960795 + 2327476 * 2 ^ 59
def prefixEnd_2327476 : Nat := 4983230072969 + 3 ^ 40 * 2327476 * 2
def baseEnd_2327476 : Nat := 796742599869360648764093

theorem tailTrace_2327476 : CollatzResearch.WordTrace tailWord_2327476 prefixEnd_2327476 796742599869360648764093 := by
  unfold tailWord_2327476
  simp only [CollatzResearch.WordTrace]
  refine ⟨42445011857979714049609141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56593349143972952066145521 42445011857979714049609141)
  ·
    refine ⟨3979219861685598192150857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42445011857979714049609141 3979219861685598192150857)
    ·
      refine ⟨2984414896264198644113143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3979219861685598192150857 2984414896264198644113143)
      ·
        refine ⟨4476622344396297966169715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2984414896264198644113143 4476622344396297966169715)
        ·
          refine ⟨6714933516594446949254573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4476622344396297966169715 6714933516594446949254573)
          ·
            refine ⟨2518100068722917605970465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6714933516594446949254573 2518100068722917605970465)
            ·
              refine ⟨1888575051542188204477849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2518100068722917605970465 1888575051542188204477849)
              ·
                refine ⟨1416431288656641153358387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1888575051542188204477849 1416431288656641153358387)
                ·
                  refine ⟨2124646932984961730037581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1416431288656641153358387 2124646932984961730037581)
                  ·
                    refine ⟨796742599869360648764093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2124646932984961730037581 796742599869360648764093)
                    ·
                      rfl

theorem cell22_2327476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_2327476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2327476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2327476 prefixEnd_2327476 := by exact prefixLift 2327476
  have htrace : WordTrace (prefixWord ++ tailWord_2327476) baseStart_2327476 baseEnd_2327476 := by
    simpa [prefixWord, tailWord_2327476, baseEnd_2327476] using wordTrace_append hprefix tailTrace_2327476
  have hstable : (prefixWord ++ tailWord_2327476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327476).length < 2 ^ (prefixWord ++ tailWord_2327476).sum := by decide
  have hdescent : baseEnd_2327476 < baseStart_2327476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327513 : List Nat := [1, 2, 1, 2, 5, 1, 3, 1, 2, 4]
def baseStart_2327513 : Nat := 118140960795 + 2327513 * 2 ^ 59
def prefixEnd_2327513 : Nat := 4983230072969 + 3 ^ 40 * 2327513 * 2
def baseEnd_2327513 : Nat := 796755265725504885588979

theorem tailTrace_2327513 : CollatzResearch.WordTrace tailWord_2327513 prefixEnd_2327513 796755265725504885588979 := by
  unfold tailWord_2327513
  simp only [CollatzResearch.WordTrace]
  refine ⟨84891373216825383418315193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56594248811216922278876795 84891373216825383418315193)
  ·
    refine ⟨63668529912619037563736395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84891373216825383418315193 63668529912619037563736395)
    ·
      refine ⟨95502794868928556345604593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63668529912619037563736395 95502794868928556345604593)
      ·
        refine ⟨71627096151696417259203445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95502794868928556345604593 71627096151696417259203445)
        ·
          refine ⟨6715040264221539118050323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71627096151696417259203445 6715040264221539118050323)
          ·
            refine ⟨10072560396332308677075485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6715040264221539118050323 10072560396332308677075485)
            ·
              refine ⟨3777210148624615753903307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10072560396332308677075485 3777210148624615753903307)
              ·
                refine ⟨5665815222936923630854961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3777210148624615753903307 5665815222936923630854961)
                ·
                  refine ⟨4249361417202692723141221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5665815222936923630854961 4249361417202692723141221)
                  ·
                    refine ⟨796755265725504885588979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4249361417202692723141221 796755265725504885588979)
                    ·
                      rfl

theorem cell22_2327513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 4].length) (baseStart_2327513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2327513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2327513 prefixEnd_2327513 := by exact prefixLift 2327513
  have htrace : WordTrace (prefixWord ++ tailWord_2327513) baseStart_2327513 baseEnd_2327513 := by
    simpa [prefixWord, tailWord_2327513, baseEnd_2327513] using wordTrace_append hprefix tailTrace_2327513
  have hstable : (prefixWord ++ tailWord_2327513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327513).length < 2 ^ (prefixWord ++ tailWord_2327513).sum := by decide
  have hdescent : baseEnd_2327513 < baseStart_2327513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327594 : List Nat := [3, 1, 4, 1, 4, 1, 1, 1, 3, 3]
def baseStart_2327594 : Nat := 118140960795 + 2327594 * 2 ^ 59
def prefixEnd_2327594 : Nat := 4983230072969 + 3 ^ 40 * 2327594 * 2
def baseEnd_2327594 : Nat := 796782993680847674313731

theorem tailTrace_2327594 : CollatzResearch.WordTrace tailWord_2327594 prefixEnd_2327594 796782993680847674313731 := by
  unfold tailWord_2327594
  simp only [CollatzResearch.WordTrace]
  refine ⟨21223581882382983563003459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56596218353021289501342557 21223581882382983563003459)
  ·
    refine ⟨31835372823574475344505189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21223581882382983563003459 31835372823574475344505189)
    ·
      refine ⟨5969132404420214127094723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31835372823574475344505189 5969132404420214127094723)
      ·
        refine ⟨8953698606630321190642085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5969132404420214127094723 8953698606630321190642085)
        ·
          refine ⟨1678818488743185223245391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8953698606630321190642085 1678818488743185223245391)
          ·
            refine ⟨2518227733114777834868087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1678818488743185223245391 2518227733114777834868087)
            ·
              refine ⟨3777341599672166752302131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2518227733114777834868087 3777341599672166752302131)
              ·
                refine ⟨5666012399508250128453197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3777341599672166752302131 5666012399508250128453197)
                ·
                  refine ⟨2124754649815593798169949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5666012399508250128453197 2124754649815593798169949)
                  ·
                    refine ⟨796782993680847674313731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2124754649815593798169949 796782993680847674313731)
                    ·
                      rfl

theorem cell22_2327594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_2327594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2327594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2327594 prefixEnd_2327594 := by exact prefixLift 2327594
  have htrace : WordTrace (prefixWord ++ tailWord_2327594) baseStart_2327594 baseEnd_2327594 := by
    simpa [prefixWord, tailWord_2327594, baseEnd_2327594] using wordTrace_append hprefix tailTrace_2327594
  have hstable : (prefixWord ++ tailWord_2327594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327594).length < 2 ^ (prefixWord ++ tailWord_2327594).sum := by decide
  have hdescent : baseEnd_2327594 < baseStart_2327594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327633 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 6, 3]
def baseStart_2327633 : Nat := 118140960795 + 2327633 * 2 ^ 59
def prefixEnd_2327633 : Nat := 4983230072969 + 3 ^ 40 * 2327633 * 2
def baseEnd_2327633 : Nat := 796796344177864572588611

theorem tailTrace_2327633 : CollatzResearch.WordTrace tailWord_2327633 prefixEnd_2327633 796796344177864572588611 := by
  unfold tailWord_2327633
  simp only [CollatzResearch.WordTrace]
  refine ⟨84895749976390643912683553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56597166650927095941789035 84895749976390643912683553)
  ·
    refine ⟨63671812482292982934512665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84895749976390643912683553 63671812482292982934512665)
    ·
      refine ⟨47753859361719737200884499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63671812482292982934512665 47753859361719737200884499)
      ·
        refine ⟨71630789042579605801326749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47753859361719737200884499 71630789042579605801326749)
        ·
          refine ⟨26861545890967352175497531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71630789042579605801326749 26861545890967352175497531)
          ·
            refine ⟨40292318836451028263246297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26861545890967352175497531 40292318836451028263246297)
            ·
              refine ⟨30219239127338271197434723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40292318836451028263246297 30219239127338271197434723)
              ·
                refine ⟨45328858691007406796152085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30219239127338271197434723 45328858691007406796152085)
                ·
                  refine ⟨2124790251140972193569629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45328858691007406796152085 2124790251140972193569629)
                  ·
                    refine ⟨796796344177864572588611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2124790251140972193569629 796796344177864572588611)
                    ·
                      rfl

theorem cell22_2327633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_2327633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2327633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2327633 prefixEnd_2327633 := by exact prefixLift 2327633
  have htrace : WordTrace (prefixWord ++ tailWord_2327633) baseStart_2327633 baseEnd_2327633 := by
    simpa [prefixWord, tailWord_2327633, baseEnd_2327633] using wordTrace_append hprefix tailTrace_2327633
  have hstable : (prefixWord ++ tailWord_2327633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327633).length < 2 ^ (prefixWord ++ tailWord_2327633).sum := by decide
  have hdescent : baseEnd_2327633 < baseStart_2327633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327648 : List Nat := [2, 1, 1, 3, 2, 2, 1, 4, 2, 4]
def baseStart_2327648 : Nat := 118140960795 + 2327648 * 2 ^ 59
def prefixEnd_2327648 : Nat := 4983230072969 + 3 ^ 40 * 2327648 * 2
def baseEnd_2327648 : Nat := 796801478984409533463565

theorem tailTrace_2327648 : CollatzResearch.WordTrace tailWord_2327648 prefixEnd_2327648 796801478984409533463565 := by
  unfold tailWord_2327648
  simp only [CollatzResearch.WordTrace]
  refine ⟨42448148535668150737239799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56597531380890867649653065 42448148535668150737239799)
  ·
    refine ⟨63672222803502226105859699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42448148535668150737239799 63672222803502226105859699)
    ·
      refine ⟨95508334205253339158789549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63672222803502226105859699 95508334205253339158789549)
      ·
        refine ⟨35815625326970002184546081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95508334205253339158789549 35815625326970002184546081)
        ·
          refine ⟨26861718995227501638409561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35815625326970002184546081 26861718995227501638409561)
          ·
            refine ⟨20146289246420626228807171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26861718995227501638409561 20146289246420626228807171)
            ·
              refine ⟨30219433869630939343210757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20146289246420626228807171 30219433869630939343210757)
              ·
                refine ⟨5666143850555801126852017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30219433869630939343210757 5666143850555801126852017)
                ·
                  refine ⟨4249607887916850845139013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5666143850555801126852017 4249607887916850845139013)
                  ·
                    refine ⟨796801478984409533463565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4249607887916850845139013 796801478984409533463565)
                    ·
                      rfl

theorem cell22_2327648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 2, 4].length) (baseStart_2327648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2327648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2327648 prefixEnd_2327648 := by exact prefixLift 2327648
  have htrace : WordTrace (prefixWord ++ tailWord_2327648) baseStart_2327648 baseEnd_2327648 := by
    simpa [prefixWord, tailWord_2327648, baseEnd_2327648] using wordTrace_append hprefix tailTrace_2327648
  have hstable : (prefixWord ++ tailWord_2327648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327648).length < 2 ^ (prefixWord ++ tailWord_2327648).sum := by decide
  have hdescent : baseEnd_2327648 < baseStart_2327648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327712 : List Nat := [2, 1, 1, 4, 2, 1, 1, 6, 1, 3]
def baseStart_2327712 : Nat := 118140960795 + 2327712 * 2 ^ 59
def prefixEnd_2327712 : Nat := 4983230072969 + 3 ^ 40 * 2327712 * 2
def baseEnd_2327712 : Nat := 796823387492334699863369

theorem tailTrace_2327712 : CollatzResearch.WordTrace tailWord_2327712 prefixEnd_2327712 796823387492334699863369 := by
  unfold tailWord_2327712
  simp only [CollatzResearch.WordTrace]
  refine ⟨42449315671552220202404695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56599087562069626936539593 42449315671552220202404695)
  ·
    refine ⟨63673973507328330303607043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42449315671552220202404695 63673973507328330303607043)
    ·
      refine ⟨95510960260992495455410565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63673973507328330303607043 95510960260992495455410565)
      ·
        refine ⟨17908305048936092897889481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95510960260992495455410565 17908305048936092897889481)
        ·
          refine ⟨13431228786702069673417111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17908305048936092897889481 13431228786702069673417111)
          ·
            refine ⟨20146843180053104510125667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13431228786702069673417111 20146843180053104510125667)
            ·
              refine ⟨30220264770079656765188501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20146843180053104510125667 30220264770079656765188501)
              ·
                refine ⟨1416574911097483910868211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30220264770079656765188501 1416574911097483910868211)
                ·
                  refine ⟨2124862366646225866302317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1416574911097483910868211 2124862366646225866302317)
                  ·
                    refine ⟨796823387492334699863369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2124862366646225866302317 796823387492334699863369)
                    ·
                      rfl

theorem cell22_2327712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 1, 3].length) (baseStart_2327712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2327712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2327712 prefixEnd_2327712 := by exact prefixLift 2327712
  have htrace : WordTrace (prefixWord ++ tailWord_2327712) baseStart_2327712 baseEnd_2327712 := by
    simpa [prefixWord, tailWord_2327712, baseEnd_2327712] using wordTrace_append hprefix tailTrace_2327712
  have hstable : (prefixWord ++ tailWord_2327712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327712).length < 2 ^ (prefixWord ++ tailWord_2327712).sum := by decide
  have hdescent : baseEnd_2327712 < baseStart_2327712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327789 : List Nat := [1, 5, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_2327789 : Nat := 118140960795 + 2327789 * 2 ^ 59
def prefixEnd_2327789 : Nat := 4983230072969 + 3 ^ 40 * 2327789 * 2
def baseEnd_2327789 : Nat := 796849746165932165688133

theorem tailTrace_2327789 : CollatzResearch.WordTrace tailWord_2327789 prefixEnd_2327789 796849746165932165688133 := by
  unfold tailWord_2327789
  simp only [CollatzResearch.WordTrace]
  refine ⟨84901439763825482555362421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56600959842550321703574947 84901439763825482555362421)
  ·
    refine ⟨7959509977858638989565227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84901439763825482555362421 7959509977858638989565227)
    ·
      refine ⟨11939264966787958484347841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7959509977858638989565227 11939264966787958484347841)
      ·
        refine ⟨8954448725090968863260881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11939264966787958484347841 8954448725090968863260881)
        ·
          refine ⟨6715836543818226647445661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8954448725090968863260881 6715836543818226647445661)
          ·
            refine ⟨2518438703931834992792123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6715836543818226647445661 2518438703931834992792123)
            ·
              refine ⟨3777658055897752489188185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2518438703931834992792123 3777658055897752489188185)
              ·
                refine ⟨2833243541923314366891139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3777658055897752489188185 2833243541923314366891139)
                ·
                  refine ⟨4249865312884971550336709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2833243541923314366891139 4249865312884971550336709)
                  ·
                    refine ⟨796849746165932165688133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4249865312884971550336709 796849746165932165688133)
                    ·
                      rfl

theorem cell22_2327789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_2327789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2327789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2327789 prefixEnd_2327789 := by exact prefixLift 2327789
  have htrace : WordTrace (prefixWord ++ tailWord_2327789) baseStart_2327789 baseEnd_2327789 := by
    simpa [prefixWord, tailWord_2327789, baseEnd_2327789] using wordTrace_append hprefix tailTrace_2327789
  have hstable : (prefixWord ++ tailWord_2327789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327789).length < 2 ^ (prefixWord ++ tailWord_2327789).sum := by decide
  have hdescent : baseEnd_2327789 < baseStart_2327789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327907 : List Nat := [1, 1, 1, 5, 2, 2, 1, 4, 1, 4]
def baseStart_2327907 : Nat := 118140960795 + 2327907 * 2 ^ 59
def prefixEnd_2327907 : Nat := 4983230072969 + 3 ^ 40 * 2327907 * 2
def baseEnd_2327907 : Nat := 796890139977419191237771

theorem tailTrace_2327907 : CollatzResearch.WordTrace tailWord_2327907 prefixEnd_2327907 796890139977419191237771 := by
  unfold tailWord_2327907
  simp only [CollatzResearch.WordTrace]
  refine ⟨84905743577397988708157975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56603829051598659138771983 84905743577397988708157975)
  ·
    refine ⟨127358615366096983062236963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84905743577397988708157975 127358615366096983062236963)
    ·
      refine ⟨191037923049145474593355445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127358615366096983062236963 191037923049145474593355445)
      ·
        refine ⟨17909805285857388243127073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 191037923049145474593355445 17909805285857388243127073)
        ·
          refine ⟨13432353964393041182345305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17909805285857388243127073 13432353964393041182345305)
          ·
            refine ⟨10074265473294780886758979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13432353964393041182345305 10074265473294780886758979)
            ·
              refine ⟨15111398209942171330138469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10074265473294780886758979 15111398209942171330138469)
              ·
                refine ⟨2833387164364157124400963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15111398209942171330138469 2833387164364157124400963)
                ·
                  refine ⟨4250080746546235686601445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2833387164364157124400963 4250080746546235686601445)
                  ·
                    refine ⟨796890139977419191237771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4250080746546235686601445 796890139977419191237771)
                    ·
                      rfl

theorem cell22_2327907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 4].length) (baseStart_2327907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2327907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2327907 prefixEnd_2327907 := by exact prefixLift 2327907
  have htrace : WordTrace (prefixWord ++ tailWord_2327907) baseStart_2327907 baseEnd_2327907 := by
    simpa [prefixWord, tailWord_2327907, baseEnd_2327907] using wordTrace_append hprefix tailTrace_2327907
  have hstable : (prefixWord ++ tailWord_2327907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327907).length < 2 ^ (prefixWord ++ tailWord_2327907).sum := by decide
  have hdescent : baseEnd_2327907 < baseStart_2327907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327920 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 3, 5]
def baseStart_2327920 : Nat := 118140960795 + 2327920 * 2 ^ 59
def prefixEnd_2327920 : Nat := 4983230072969 + 3 ^ 40 * 2327920 * 2
def baseEnd_2327920 : Nat := 796894590143091490662731

theorem tailTrace_2327920 : CollatzResearch.WordTrace tailWord_2327920 prefixEnd_2327920 796894590143091490662731 := by
  unfold tailWord_2327920
  simp only [CollatzResearch.WordTrace]
  refine ⟨42453108863175445964190607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56604145150900594618920809 42453108863175445964190607)
  ·
    refine ⟨63679663294763168946285911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42453108863175445964190607 63679663294763168946285911)
    ·
      refine ⟨95519494942144753419428867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63679663294763168946285911 95519494942144753419428867)
      ·
        refine ⟨143279242413217130129143301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95519494942144753419428867 143279242413217130129143301)
        ·
          refine ⟨26864857952478211899214369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143279242413217130129143301 26864857952478211899214369)
          ·
            refine ⟨20148643464358658924410777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26864857952478211899214369 20148643464358658924410777)
            ·
              refine ⟨15111482598268994193308083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20148643464358658924410777 15111482598268994193308083)
              ·
                refine ⟨22667223897403491289962125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15111482598268994193308083 22667223897403491289962125)
                ·
                  refine ⟨8500208961526309233735797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22667223897403491289962125 8500208961526309233735797)
                  ·
                    refine ⟨796894590143091490662731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8500208961526309233735797 796894590143091490662731)
                    ·
                      rfl

theorem cell22_2327920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_2327920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2327920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2327920 prefixEnd_2327920 := by exact prefixLift 2327920
  have htrace : WordTrace (prefixWord ++ tailWord_2327920) baseStart_2327920 baseEnd_2327920 := by
    simpa [prefixWord, tailWord_2327920, baseEnd_2327920] using wordTrace_append hprefix tailTrace_2327920
  have hstable : (prefixWord ++ tailWord_2327920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327920).length < 2 ^ (prefixWord ++ tailWord_2327920).sum := by decide
  have hdescent : baseEnd_2327920 < baseStart_2327920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328076 : List Nat := [2, 2, 1, 2, 5, 1, 2, 2, 1, 4]
def baseStart_2328076 : Nat := 118140960795 + 2328076 * 2 ^ 59
def prefixEnd_2328076 : Nat := 4983230072969 + 3 ^ 40 * 2328076 * 2
def baseEnd_2328076 : Nat := 796947992131159083762253

theorem tailTrace_2328076 : CollatzResearch.WordTrace tailWord_2328076 prefixEnd_2328076 796947992131159083762253 := by
  unfold tailWord_2328076
  simp only [CollatzResearch.WordTrace]
  refine ⟨42455953756892865285530041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56607938342523820380706721 42455953756892865285530041)
  ·
    refine ⟨31841965317669648964147531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42455953756892865285530041 31841965317669648964147531)
    ·
      refine ⟨47762947976504473446221297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31841965317669648964147531 47762947976504473446221297)
      ·
        refine ⟨35822210982378355084665973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47762947976504473446221297 35822210982378355084665973)
        ·
          refine ⟨3358332279597970789187435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35822210982378355084665973 3358332279597970789187435)
          ·
            refine ⟨5037498419396956183781153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3358332279597970789187435 5037498419396956183781153)
            ·
              refine ⟨3778123814547717137835865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5037498419396956183781153 3778123814547717137835865)
              ·
                refine ⟨2833592860910787853376899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3778123814547717137835865 2833592860910787853376899)
                ·
                  refine ⟨4250389291366181780065349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2833592860910787853376899 4250389291366181780065349)
                  ·
                    refine ⟨796947992131159083762253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4250389291366181780065349 796947992131159083762253)
                    ·
                      rfl

theorem cell22_2328076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_2328076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328076 prefixEnd_2328076 := by exact prefixLift 2328076
  have htrace : WordTrace (prefixWord ++ tailWord_2328076) baseStart_2328076 baseEnd_2328076 := by
    simpa [prefixWord, tailWord_2328076, baseEnd_2328076] using wordTrace_append hprefix tailTrace_2328076
  have hstable : (prefixWord ++ tailWord_2328076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328076).length < 2 ^ (prefixWord ++ tailWord_2328076).sum := by decide
  have hdescent : baseEnd_2328076 < baseStart_2328076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328106 : List Nat := [3, 1, 4, 1, 1, 1, 2, 4, 2, 3]
def baseStart_2328106 : Nat := 118140960795 + 2328106 * 2 ^ 59
def prefixEnd_2328106 : Nat := 4983230072969 + 3 ^ 40 * 2328106 * 2
def baseEnd_2328106 : Nat := 796958261744249005512161

theorem tailTrace_2328106 : CollatzResearch.WordTrace tailWord_2328106 prefixEnd_2328106 796958261744249005512161 := by
  unfold tailWord_2328106
  simp only [CollatzResearch.WordTrace]
  refine ⟨21228250425919261423663043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56608667802451363796434781 21228250425919261423663043)
  ·
    refine ⟨31842375638878892135494565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21228250425919261423663043 31842375638878892135494565)
    ·
      refine ⟨5970445432289792275405231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31842375638878892135494565 5970445432289792275405231)
      ·
        refine ⟨8955668148434688413107847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5970445432289792275405231 8955668148434688413107847)
        ·
          refine ⟨13433502222652032619661771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8955668148434688413107847 13433502222652032619661771)
          ·
            refine ⟨20150253333978048929492657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13433502222652032619661771 20150253333978048929492657)
            ·
              refine ⟨15112690000483536697119493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20150253333978048929492657 15112690000483536697119493)
              ·
                refine ⟨2833629375090663130709905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15112690000483536697119493 2833629375090663130709905)
                ·
                  refine ⟨2125222031317997348032429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2833629375090663130709905 2125222031317997348032429)
                  ·
                    refine ⟨796958261744249005512161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2125222031317997348032429 796958261744249005512161)
                    ·
                      rfl

theorem cell22_2328106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_2328106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328106 prefixEnd_2328106 := by exact prefixLift 2328106
  have htrace : WordTrace (prefixWord ++ tailWord_2328106) baseStart_2328106 baseEnd_2328106 := by
    simpa [prefixWord, tailWord_2328106, baseEnd_2328106] using wordTrace_append hprefix tailTrace_2328106
  have hstable : (prefixWord ++ tailWord_2328106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328106).length < 2 ^ (prefixWord ++ tailWord_2328106).sum := by decide
  have hdescent : baseEnd_2328106 < baseStart_2328106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328164 : List Nat := [2, 3, 1, 1, 2, 3, 1, 4, 5]
def baseStart_2328164 : Nat := 118140960795 + 2328164 * 2 ^ 59
def prefixEnd_2328164 : Nat := 4983230072969 + 3 ^ 40 * 2328164 * 2
def baseEnd_2328164 : Nat := 265659372109852062520661

theorem tailTrace_2328164 : CollatzResearch.WordTrace tailWord_2328164 prefixEnd_2328164 265659372109852062520661 := by
  unfold tailWord_2328164
  simp only [CollatzResearch.WordTrace]
  refine ⟨42457558568733460800131773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56610078091644614400175697 42457558568733460800131773)
  ·
    refine ⟨15921584463275047800049415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42457558568733460800131773 15921584463275047800049415)
    ·
      refine ⟨23882376694912571700074123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15921584463275047800049415 23882376694912571700074123)
      ·
        refine ⟨35823565042368857550111185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23882376694912571700074123 35823565042368857550111185)
        ·
          refine ⟨26867673781776643162583389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35823565042368857550111185 26867673781776643162583389)
          ·
            refine ⟨10075377668166241185968771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26867673781776643162583389 10075377668166241185968771)
            ·
              refine ⟨15113066502249361778953157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10075377668166241185968771 15113066502249361778953157)
              ·
                refine ⟨2833699969171755333553717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15113066502249361778953157 2833699969171755333553717)
                ·
                  refine ⟨265659372109852062520661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2833699969171755333553717 265659372109852062520661)
                  ·
                    rfl

theorem cell22_2328164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_2328164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328164 prefixEnd_2328164 := by exact prefixLift 2328164
  have htrace : WordTrace (prefixWord ++ tailWord_2328164) baseStart_2328164 baseEnd_2328164 := by
    simpa [prefixWord, tailWord_2328164, baseEnd_2328164] using wordTrace_append hprefix tailTrace_2328164
  have hstable : (prefixWord ++ tailWord_2328164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328164).length < 2 ^ (prefixWord ++ tailWord_2328164).sum := by decide
  have hdescent : baseEnd_2328164 < baseStart_2328164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328181 : List Nat := [1, 3, 4, 2, 1, 1, 2, 3, 5]
def baseStart_2328181 : Nat := 118140960795 + 2328181 * 2 ^ 59
def prefixEnd_2328181 : Nat := 4983230072969 + 3 ^ 40 * 2328181 * 2
def baseEnd_2328181 : Nat := 265661311925657936628977

theorem tailTrace_2328181 : CollatzResearch.WordTrace tailWord_2328181 prefixEnd_2328181 265661311925657936628977 := by
  unfold tailWord_2328181
  simp only [CollatzResearch.WordTrace]
  refine ⟨84915737178405333503632397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56610491452270222335754931 84915737178405333503632397)
  ·
    refine ⟨31843401441902000063862149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84915737178405333503632397 31843401441902000063862149)
    ·
      refine ⟨5970637770356625011974153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31843401441902000063862149 5970637770356625011974153)
      ·
        refine ⟨4477978327767468758980615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5970637770356625011974153 4477978327767468758980615)
        ·
          refine ⟨6716967491651203138470923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4477978327767468758980615 6716967491651203138470923)
          ·
            refine ⟨10075451237476804707706385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6716967491651203138470923 10075451237476804707706385)
            ·
              refine ⟨7556588428107603530779789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10075451237476804707706385 7556588428107603530779789)
              ·
                refine ⟨2833720660540351324042421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7556588428107603530779789 2833720660540351324042421)
                ·
                  refine ⟨265661311925657936628977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2833720660540351324042421 265661311925657936628977)
                  ·
                    rfl

theorem cell22_2328181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_2328181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328181 prefixEnd_2328181 := by exact prefixLift 2328181
  have htrace : WordTrace (prefixWord ++ tailWord_2328181) baseStart_2328181 baseEnd_2328181 := by
    simpa [prefixWord, tailWord_2328181, baseEnd_2328181] using wordTrace_append hprefix tailTrace_2328181
  have hstable : (prefixWord ++ tailWord_2328181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328181).length < 2 ^ (prefixWord ++ tailWord_2328181).sum := by decide
  have hdescent : baseEnd_2328181 < baseStart_2328181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328232 : List Nat := [2, 1, 7, 1, 1, 1, 3, 1, 5]
def baseStart_2328232 : Nat := 118140960795 + 2328232 * 2 ^ 59
def prefixEnd_2328232 : Nat := 4983230072969 + 3 ^ 40 * 2328232 * 2
def baseEnd_2328232 : Nat := 265667131373075558953925

theorem tailTrace_2328232 : CollatzResearch.WordTrace tailWord_2328232 prefixEnd_2328232 265667131373075558953925 := by
  unfold tailWord_2328232
  simp only [CollatzResearch.WordTrace]
  refine ⟨42458798650610284606869475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56611731534147046142492633 42458798650610284606869475)
  ·
    refine ⟨63688197975915426910304213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42458798650610284606869475 63688197975915426910304213)
    ·
      refine ⟨1492692140060517818210255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 63688197975915426910304213 1492692140060517818210255)
      ·
        refine ⟨2239038210090776727315383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1492692140060517818210255 2239038210090776727315383)
        ·
          refine ⟨3358557315136165090973075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2239038210090776727315383 3358557315136165090973075)
          ·
            refine ⟨5037835972704247636459613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3358557315136165090973075 5037835972704247636459613)
            ·
              refine ⟨1889188489764092863672355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5037835972704247636459613 1889188489764092863672355)
              ·
                refine ⟨2833782734646139295508533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1889188489764092863672355 2833782734646139295508533)
                ·
                  refine ⟨265667131373075558953925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2833782734646139295508533 265667131373075558953925)
                  ·
                    rfl

theorem cell22_2328232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 5].length) (baseStart_2328232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328232 prefixEnd_2328232 := by exact prefixLift 2328232
  have htrace : WordTrace (prefixWord ++ tailWord_2328232) baseStart_2328232 baseEnd_2328232 := by
    simpa [prefixWord, tailWord_2328232, baseEnd_2328232] using wordTrace_append hprefix tailTrace_2328232
  have hstable : (prefixWord ++ tailWord_2328232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328232).length < 2 ^ (prefixWord ++ tailWord_2328232).sum := by decide
  have hdescent : baseEnd_2328232 < baseStart_2328232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328314 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 4, 5]
def baseStart_2328314 : Nat := 118140960795 + 2328314 * 2 ^ 59
def prefixEnd_2328314 : Nat := 4983230072969 + 3 ^ 40 * 2328314 * 2
def baseEnd_2328314 : Nat := 797029464395005796311523

theorem tailTrace_2328314 : CollatzResearch.WordTrace tailWord_2328314 prefixEnd_2328314 797029464395005796311523 := by
  unfold tailWord_2328314
  simp only [CollatzResearch.WordTrace]
  refine ⟨21230147021730874304555999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56613725391282331478815997 21230147021730874304555999)
  ·
    refine ⟨31845220532596311456833999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21230147021730874304555999 31845220532596311456833999)
    ·
      refine ⟨47767830798894467185250999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31845220532596311456833999 47767830798894467185250999)
      ·
        refine ⟨71651746198341700777876499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47767830798894467185250999 71651746198341700777876499)
        ·
          refine ⟨107477619297512551166814749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71651746198341700777876499 107477619297512551166814749)
          ·
            refine ⟨40304107236567206687555531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107477619297512551166814749 40304107236567206687555531)
            ·
              refine ⟨60456160854850810031333297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40304107236567206687555531 60456160854850810031333297)
              ·
                refine ⟨45342120641138107523499973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60456160854850810031333297 45342120641138107523499973)
                ·
                  refine ⟨8501647620213395160656245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45342120641138107523499973 8501647620213395160656245)
                  ·
                    refine ⟨797029464395005796311523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8501647620213395160656245 797029464395005796311523)
                    ·
                      rfl

theorem cell22_2328314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_2328314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328314 prefixEnd_2328314 := by exact prefixLift 2328314
  have htrace : WordTrace (prefixWord ++ tailWord_2328314) baseStart_2328314 baseEnd_2328314 := by
    simpa [prefixWord, tailWord_2328314, baseEnd_2328314] using wordTrace_append hprefix tailTrace_2328314
  have hstable : (prefixWord ++ tailWord_2328314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328314).length < 2 ^ (prefixWord ++ tailWord_2328314).sum := by decide
  have hdescent : baseEnd_2328314 < baseStart_2328314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328346 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 3, 4]
def baseStart_2328346 : Nat := 118140960795 + 2328346 * 2 ^ 59
def prefixEnd_2328346 : Nat := 4983230072969 + 3 ^ 40 * 2328346 * 2
def baseEnd_2328346 : Nat := 797040418648968379511425

theorem tailTrace_2328346 : CollatzResearch.WordTrace tailWord_2328346 prefixEnd_2328346 797040418648968379511425 := by
  unfold tailWord_2328346
  simp only [CollatzResearch.WordTrace]
  refine ⟨21230438805701891670847223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56614503481871711122259261 21230438805701891670847223)
  ·
    refine ⟨31845658208552837506270835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21230438805701891670847223 31845658208552837506270835)
    ·
      refine ⟨47768487312829256259406253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31845658208552837506270835 47768487312829256259406253)
      ·
        refine ⟨17913182742310971097277345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47768487312829256259406253 17913182742310971097277345)
        ·
          refine ⟨13434887056733228322958009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17913182742310971097277345 13434887056733228322958009)
          ·
            refine ⟨10076165292549921242218507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13434887056733228322958009 10076165292549921242218507)
            ·
              refine ⟨15114247938824881863327761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10076165292549921242218507 15114247938824881863327761)
              ·
                refine ⟨11335685954118661397495821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15114247938824881863327761 11335685954118661397495821)
                ·
                  refine ⟨4250882232794498024060933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11335685954118661397495821 4250882232794498024060933)
                  ·
                    refine ⟨797040418648968379511425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4250882232794498024060933 797040418648968379511425)
                    ·
                      rfl

theorem cell22_2328346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_2328346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328346 prefixEnd_2328346 := by exact prefixLift 2328346
  have htrace : WordTrace (prefixWord ++ tailWord_2328346) baseStart_2328346 baseEnd_2328346 := by
    simpa [prefixWord, tailWord_2328346, baseEnd_2328346] using wordTrace_append hprefix tailTrace_2328346
  have hstable : (prefixWord ++ tailWord_2328346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328346).length < 2 ^ (prefixWord ++ tailWord_2328346).sum := by decide
  have hdescent : baseEnd_2328346 < baseStart_2328346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328376 : List Nat := [2, 1, 2, 1, 3, 3, 2, 2, 1, 5]
def baseStart_2328376 : Nat := 118140960795 + 2328376 * 2 ^ 59
def prefixEnd_2328376 : Nat := 4983230072969 + 3 ^ 40 * 2328376 * 2
def baseEnd_2328376 : Nat := 797050688262058301261333

theorem tailTrace_2328376 : CollatzResearch.WordTrace tailWord_2328376 prefixEnd_2328376 797050688262058301261333 := by
  unfold tailWord_2328376
  simp only [CollatzResearch.WordTrace]
  refine ⟨42461424706349440903490491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56615232941799254537987321 42461424706349440903490491)
  ·
    refine ⟨63692137059524161355235737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42461424706349440903490491 63692137059524161355235737)
    ·
      refine ⟨47769102794643121016426803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63692137059524161355235737 47769102794643121016426803)
      ·
        refine ⟨71653654191964681524640205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47769102794643121016426803 71653654191964681524640205)
        ·
          refine ⟨26870120321986755571740077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71653654191964681524640205 26870120321986755571740077)
          ·
            refine ⟨10076295120745033339402529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26870120321986755571740077 10076295120745033339402529)
            ·
              refine ⟨7557221340558775004551897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10076295120745033339402529 7557221340558775004551897)
              ·
                refine ⟨5667916005419081253413923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7557221340558775004551897 5667916005419081253413923)
                ·
                  refine ⟨8501874008128621880120885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5667916005419081253413923 8501874008128621880120885)
                  ·
                    refine ⟨797050688262058301261333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8501874008128621880120885 797050688262058301261333)
                    ·
                      rfl

theorem cell22_2328376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_2328376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328376 prefixEnd_2328376 := by exact prefixLift 2328376
  have htrace : WordTrace (prefixWord ++ tailWord_2328376) baseStart_2328376 baseEnd_2328376 := by
    simpa [prefixWord, tailWord_2328376, baseEnd_2328376] using wordTrace_append hprefix tailTrace_2328376
  have hstable : (prefixWord ++ tailWord_2328376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328376).length < 2 ^ (prefixWord ++ tailWord_2328376).sum := by decide
  have hdescent : baseEnd_2328376 < baseStart_2328376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328378 : List Nat := [3, 1, 1, 1, 5, 1, 1, 5, 4]
def baseStart_2328378 : Nat := 118140960795 + 2328378 * 2 ^ 59
def prefixEnd_2328378 : Nat := 4983230072969 + 3 ^ 40 * 2328378 * 2
def baseEnd_2328378 : Nat := 265683790967643654237109

theorem tailTrace_2328378 : CollatzResearch.WordTrace tailWord_2328378 prefixEnd_2328378 265683790967643654237109 := by
  unfold tailWord_2328378
  simp only [CollatzResearch.WordTrace]
  refine ⟨21230730589672909037138447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56615281572461090765702525 21230730589672909037138447)
  ·
    refine ⟨31846095884509363555707671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21230730589672909037138447 31846095884509363555707671)
    ·
      refine ⟨47769143826764045333561507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31846095884509363555707671 47769143826764045333561507)
      ·
        refine ⟨71653715740146068000342261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47769143826764045333561507 71653715740146068000342261)
        ·
          refine ⟨6717535850638693875032087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71653715740146068000342261 6717535850638693875032087)
          ·
            refine ⟨10076303775958040812548131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6717535850638693875032087 10076303775958040812548131)
            ·
              refine ⟨15114455663937061218822197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10076303775958040812548131 15114455663937061218822197)
              ·
                refine ⟨1416980218494099489264581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15114455663937061218822197 1416980218494099489264581)
                ·
                  refine ⟨265683790967643654237109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1416980218494099489264581 265683790967643654237109)
                  ·
                    rfl

theorem cell22_2328378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 4].length) (baseStart_2328378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328378 prefixEnd_2328378 := by exact prefixLift 2328378
  have htrace : WordTrace (prefixWord ++ tailWord_2328378) baseStart_2328378 baseEnd_2328378 := by
    simpa [prefixWord, tailWord_2328378, baseEnd_2328378] using wordTrace_append hprefix tailTrace_2328378
  have hstable : (prefixWord ++ tailWord_2328378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328378).length < 2 ^ (prefixWord ++ tailWord_2328378).sum := by decide
  have hdescent : baseEnd_2328378 < baseStart_2328378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328389 : List Nat := [1, 3, 1, 1, 1, 2, 13]
def baseStart_2328389 : Nat := 118140960795 + 2328389 * 2 ^ 59
def prefixEnd_2328389 : Nat := 4983230072969 + 3 ^ 40 * 2328389 * 2
def baseEnd_2328389 : Nat := 29520560682508540766159

theorem tailTrace_2328389 : CollatzResearch.WordTrace tailWord_2328389 prefixEnd_2328389 29520560682508540766159 := by
  unfold tailWord_2328389
  simp only [CollatzResearch.WordTrace]
  refine ⟨84923323561651785027204221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56615549041101190018136147 84923323561651785027204221)
  ·
    refine ⟨31846246335619419385201583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84923323561651785027204221 31846246335619419385201583)
    ·
      refine ⟨47769369503429129077802375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31846246335619419385201583 47769369503429129077802375)
      ·
        refine ⟨71654054255143693616703563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47769369503429129077802375 71654054255143693616703563)
        ·
          refine ⟨107481081382715540425055345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71654054255143693616703563 107481081382715540425055345)
          ·
            refine ⟨80610811037036655318791509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107481081382715540425055345 80610811037036655318791509)
            ·
              refine ⟨29520560682508540766159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 80610811037036655318791509 29520560682508540766159)
              ·
                rfl

theorem cell22_2328389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 13].length) (baseStart_2328389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328389 prefixEnd_2328389 := by exact prefixLift 2328389
  have htrace : WordTrace (prefixWord ++ tailWord_2328389) baseStart_2328389 baseEnd_2328389 := by
    simpa [prefixWord, tailWord_2328389, baseEnd_2328389] using wordTrace_append hprefix tailTrace_2328389
  have hstable : (prefixWord ++ tailWord_2328389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328389).length < 2 ^ (prefixWord ++ tailWord_2328389).sum := by decide
  have hdescent : baseEnd_2328389 < baseStart_2328389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
